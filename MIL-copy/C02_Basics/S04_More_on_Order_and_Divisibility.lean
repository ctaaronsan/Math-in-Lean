import MIL.Common
import Mathlib.Data.Real.Basic

namespace C02S04

section
variable (a b c d : ℝ)

#check (min_le_left a b : min a b ≤ a)
#check (min_le_right a b : min a b ≤ b)
#check (le_min : c ≤ a → c ≤ b → c ≤ min a b)

#check (le_max_left : ∀ (a b : ℝ), a ≤ max a b)
#check (le_max_left a b: a ≤ max a b)
#check (le_max_right a b: b ≤ max a b)
#check (max_le : a ≤ c → b ≤ c → max a b ≤ c)

#check max (1:ℝ)
#check (max · 1)

example : min a b = min b a := by
  apply le_antisymm
  · show min a b ≤ min b a
    apply le_min
    · apply min_le_right
    apply min_le_left
  · show min b a ≤ min a b
    apply le_min
    · apply min_le_right
    apply min_le_left

example : min a b = min b a := by
  have h : ∀ x y : ℝ, min x y ≤ min y x := by
    intro x y
    apply le_min
    apply min_le_right
    apply min_le_left
  apply le_antisymm
  apply h
  apply h

theorem min_symm : min a b = min b a := by
  apply le_antisymm
  repeat
    apply le_min
    apply min_le_right
    apply min_le_left

example : max a b = max b a := by
  have h : ∀ x y : ℝ, max x y ≤ max y x := by
    intro x y
    apply max_le
    apply le_max_right
    apply le_max_left
  apply le_antisymm
  apply h
  apply h

example : min (min a b) c = min a (min b c) := by
  have h₁ (a b c : ℝ): min (min a b) c ≤ min b c := by
    apply le_min
    · show min (min a b) c ≤ b
      calc
        _ ≤ min a b := by apply min_le_left
        _ ≤ b := by apply min_le_right
    · show min (min a b) c ≤ c
      apply min_le_right
  have h₂ (a b c : ℝ): min (min a b) c ≤ a := by
    calc
      _ ≤ min a b := by apply min_le_left
      _ ≤ a := by apply min_le_left
  have h_le (a b c : ℝ): min (min a b) c ≤ min a (min b c) := by
    apply le_min (h₂ a b c) (h₁ a b c)

  have h_ge : min (min a b) c ≥ min a (min b c)
  calc
    _ = min c (min b a) := by rw [min_symm, min_symm a b]
    _ ≥ min (min c b) a := by apply h_le
    _ = min a (min b c) := by rw [min_symm, min_symm b c]

  exact le_antisymm (h_le a b c) h_ge

-- simplified version
example : min (min a b) c = min a (min b c) := by
  have h_le (a b c : ℝ) : min (min a b) c ≤ min a (min b c) := by
    apply le_min
    · show min (min a b) c ≤ a
      exact le_trans (min_le_left _ c) (min_le_left a b)
    · show  min (min a b) c ≤ min b c
      apply le_min
      · exact le_trans (min_le_left _ _) (min_le_right _ _)
      · exact min_le_right _ _
  have h_ge : min (min a b) c ≥ min a (min b c) := by
    rw [min_symm, min_symm a b, min_symm a, min_symm b c]
    apply h_le
  -- have h_ge : min (min a b) c ≥ min a (min b c)
  -- calc
    -- _ = min c (min b a) := by rw [min_symm, min_symm a b]
    -- _ ≥ min (min c b) a := by apply h_le
    -- _ = min a (min b c) := by rw [min_symm, min_symm b c]
  exact le_antisymm (h_le _ _ _) h_ge

#check (add_neg_cancel_right)
#check (min_le_left)

theorem aux : min a b + c ≤ min (a + c) (b + c) := by
  apply le_min
  · linarith [min_le_left a b]
  · linarith [min_le_right a b]

#check aux (a+c) (b+c) (-c)
#check add_le_add_left

example : min a b + c = min (a + c) (b + c) := by
  apply le_antisymm
  · exact aux _ _ _
  · show min (a + c) (b + c) ≤ min a b + c
    rw [← add_neg_cancel_right (min _ _) (-c), neg_neg]
    apply add_le_add_left
    nth_rw 2 [← add_neg_cancel_right a c, ← add_neg_cancel_right b c]
    exact aux (a+c) (b+c) (-c)

-- better
example : min a b + c = min (a + c) (b + c) := by
  apply le_antisymm
  · exact aux a b c
  · show min (a + c) (b + c) ≤ min a b + c
    have h : min (a + c) (b + c) - c ≤ min a b
    calc
      _ ≤ min (a + c + -c) (b + c + -c) := aux (a+c) (b+c) (-c)
      _ = min a b := by rw [add_neg_cancel_right, add_neg_cancel_right]
    linarith

#check (abs_add_le : ∀ a b : ℝ, |a + b| ≤ |a| + |b|)
#check add_sub_cancel_right
#check sub_add_cancel

example : |a| - |b| ≤ |a - b| := by
  -- have h : |a-b+b| ≤ |a-b| + |b| := abs_add_le (a-b) b
  have h := abs_add_le (a-b) b
  rw [sub_add_cancel] at h
  linarith

end

section
variable (w x y z : ℕ)

example (h₀ : x ∣ y) (h₁ : y ∣ z) : x ∣ z :=
  dvd_trans h₀ h₁

example : x ∣ y * x * z := by
  apply dvd_mul_of_dvd_left
  apply dvd_mul_left

example : x ∣ x ^ 2 := by
  apply dvd_mul_left

#check dvd_add

example (h : x ∣ w) : x ∣ y * (x * z) + x ^ 2 + w ^ 2 := by
  apply dvd_add
  · show x ∣ y * (x * z) + x ^ 2
    apply dvd_add
    · apply dvd_mul_of_dvd_right
      apply dvd_mul_right
    apply dvd_mul_left
  · show x ∣ w ^ 2
    -- rw [pow_two]
    apply dvd_mul_of_dvd_right
    exact h
end

section
variable (m n : ℕ)

#check (Nat.gcd_zero_right n : Nat.gcd n 0 = n)
#check (Nat.gcd_zero_left n : Nat.gcd 0 n = n)
#check (Nat.lcm_zero_right n : Nat.lcm n 0 = 0)
#check (Nat.lcm_zero_left n : Nat.lcm 0 n = 0)

#check dvd_antisymm
#check Nat.dvd_antisymm

example : Nat.gcd m n = Nat.gcd n m := by
  have h (m n : ℕ): Nat.gcd m n ∣ Nat.gcd n m := by
    apply dvd_gcd
    apply gcd_dvd_right
    apply gcd_dvd_left
  apply dvd_antisymm (h _ _) (h _ _)
end
