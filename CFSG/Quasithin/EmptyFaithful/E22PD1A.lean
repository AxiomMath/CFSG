module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.DihedralCore
import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.Quasithin.E22L2

open DihedralGroup

theorem e22pd1_four_mul_q (k : ℕ) : (4 : ZMod (2 ^ (k + 2))) * 2 ^ k = 0 := by
  have h : ((2 ^ (k + 2) : ℕ) : ZMod (2 ^ (k + 2))) = 0 := ZMod.natCast_self _
  have h' : (2 : ZMod (2 ^ (k + 2))) ^ (k + 2) = 0 := by exact_mod_cast h
  calc (4 : ZMod (2 ^ (k + 2))) * 2 ^ k = 2 ^ (k + 2) := by ring
    _ = 0 := h'

theorem e22pd1_h_add_h (k : ℕ) :
    (2 : ZMod (2 ^ (k + 2))) ^ (k + 1) + 2 ^ (k + 1) = 0 := by
  have := e22pd1_four_mul_q k
  linear_combination this

theorem e22pd1_neg_h (k : ℕ) : -(2 : ZMod (2 ^ (k + 2))) ^ (k + 1) = 2 ^ (k + 1) := by
  have := e22pd1_h_add_h k
  linear_combination -this

theorem e22pd1_two_pow_ne_zero {m j : ℕ} (hj : j < m) : (2 ^ j : ZMod (2 ^ m)) ≠ 0 := by
  intro h
  have h' : ((2 ^ j : ℕ) : ZMod (2 ^ m)) = 0 := by simpa using h
  have hdvd := (ZMod.natCast_eq_zero_iff (2 ^ j) (2 ^ m)).mp h'
  have h1 := Nat.le_of_dvd (by positivity) hdvd
  have h2 := Nat.pow_lt_pow_right (by norm_num : 1 < 2) hj
  omega

theorem e22pd1_two_mul_eq_zero_iff (k : ℕ) (x : ZMod (2 ^ (k + 2))) :
    2 * x = 0 ↔ x = 0 ∨ x = 2 ^ (k + 1) :=
  CFSG.GorensteinWalter.zmod_two_mul_eq_zero_iff (m := k + 2) (by omega) x

theorem e22pd1_four_mul_eq_zero {k : ℕ} {x : ZMod (2 ^ (k + 2))} (hx : 4 * x = 0) :
    x = 0 ∨ x = 2 ^ k ∨ x = 2 * 2 ^ k ∨ x = 3 * 2 ^ k := by
  have h1 : 2 * (2 * x) = 0 := by linear_combination hx
  rcases (e22pd1_two_mul_eq_zero_iff k _).mp h1 with h | h
  · rcases (e22pd1_two_mul_eq_zero_iff k x).mp h with h' | h'
    · exact Or.inl h'
    · exact Or.inr (Or.inr (Or.inl (by rw [h']; ring)))
  · have h2 : 2 * (x - 2 ^ k) = 0 := by linear_combination h
    rcases (e22pd1_two_mul_eq_zero_iff k _).mp h2 with h' | h'
    · exact Or.inr (Or.inl (by linear_combination h'))
    · exact Or.inr (Or.inr (Or.inr (by linear_combination h')))

theorem e22pd1_int_mul_h (k : ℕ) (a : ℤ) :
    (a : ZMod (2 ^ (k + 2))) * 2 ^ (k + 1) = 0 ∨
      (a : ZMod (2 ^ (k + 2))) * 2 ^ (k + 1) = 2 ^ (k + 1) := by
  have hh := e22pd1_h_add_h k
  rcases Int.even_or_odd' a with ⟨c, rfl | rfl⟩
  · left
    push_cast
    linear_combination (c : ZMod (2 ^ (k + 2))) * hh
  · right
    push_cast
    linear_combination (c : ZMod (2 ^ (k + 2))) * hh

theorem e22pd1_sr_ne_one {n : ℕ} (a : ZMod n) : sr a ≠ 1 := by
  rw [one_def]
  intro h
  cases h

theorem e22pd1_sr_ne_r {n : ℕ} (a b : ZMod n) : sr a ≠ r b := by
  intro h
  cases h

@[expose] def e22pd1_kf (k : ℕ) (j : ZMod (2 ^ (k + 2))) :
    Subgroup (DihedralGroup (2 ^ (k + 2))) where
  carrier := {x | (∃ a : ℤ, x = r ((a : ZMod (2 ^ (k + 2))) * 2 ^ (k + 1))) ∨
    (∃ a : ℤ, x = sr (j + (a : ZMod (2 ^ (k + 2))) * 2 ^ (k + 1)))}
  one_mem' := Or.inl ⟨0, by simp⟩
  mul_mem' := by
    rintro x y (⟨a, rfl⟩ | ⟨a, rfl⟩) (⟨b, rfl⟩ | ⟨b, rfl⟩)
    · exact Or.inl ⟨a + b, by simp only [r_mul_r]; congr 1; push_cast; ring⟩
    · exact Or.inr ⟨b - a, by simp only [r_mul_sr]; congr 1; push_cast; ring⟩
    · exact Or.inr ⟨a + b, by simp only [sr_mul_r]; congr 1; push_cast; ring⟩
    · exact Or.inl ⟨b - a, by simp only [sr_mul_sr]; congr 1; push_cast; ring⟩
  inv_mem' := by
    rintro x (⟨a, rfl⟩ | ⟨a, rfl⟩)
    · exact Or.inl ⟨-a, by simp only [inv_r]; congr 1; push_cast; ring⟩
    · exact Or.inr ⟨a, by simp only [inv_sr]⟩

theorem e22pd1_mem_kf {k : ℕ} {j : ZMod (2 ^ (k + 2))} {x : DihedralGroup (2 ^ (k + 2))} :
    x ∈ e22pd1_kf k j ↔
      x = 1 ∨ x = r (2 ^ (k + 1)) ∨ x = sr j ∨ x = sr (j + 2 ^ (k + 1)) := by
  constructor
  · rintro (⟨a, rfl⟩ | ⟨a, rfl⟩)
    · rcases e22pd1_int_mul_h k a with h | h
      · left; rw [h]; simp
      · right; left; rw [h]
    · rcases e22pd1_int_mul_h k a with h | h
      · right; right; left; rw [h, add_zero]
      · right; right; right; rw [h]
  · rintro (rfl | rfl | rfl | rfl)
    · exact Or.inl ⟨0, by simp⟩
    · exact Or.inl ⟨1, by simp⟩
    · exact Or.inr ⟨0, by simp⟩
    · exact Or.inr ⟨1, by simp⟩

theorem e22pd1_sq_eq_one_of_mem_kf {k : ℕ} {j : ZMod (2 ^ (k + 2))}
    {x : DihedralGroup (2 ^ (k + 2))} (hx : x ∈ e22pd1_kf k j) : x * x = 1 := by
  have hh := e22pd1_h_add_h k
  rcases e22pd1_mem_kf.mp hx with rfl | rfl | rfl | rfl
  · simp
  · rw [r_mul_r, hh, r_zero]
  · rw [sr_mul_sr, sub_self, r_zero]
  · rw [sr_mul_sr, sub_self, r_zero]

theorem e22pd1_kf_card (k : ℕ) (j : ZMod (2 ^ (k + 2))) : Nat.card ↥(e22pd1_kf k j) = 4 := by
  have hh : (2 : ZMod (2 ^ (k + 2))) ^ (k + 1) ≠ 0 := e22pd1_two_pow_ne_zero (by omega)
  have hset : ((e22pd1_kf k j : Subgroup (DihedralGroup (2 ^ (k + 2)))) :
      Set (DihedralGroup (2 ^ (k + 2)))) =
      {1, r (2 ^ (k + 1)), sr j, sr (j + 2 ^ (k + 1))} := by
    ext x
    simp only [SetLike.mem_coe, e22pd1_mem_kf, Set.mem_insert_iff, Set.mem_singleton_iff]
  have hcard : Nat.card ↥(e22pd1_kf k j) =
      ((e22pd1_kf k j : Subgroup (DihedralGroup (2 ^ (k + 2)))) :
        Set (DihedralGroup (2 ^ (k + 2)))).ncard :=
    Nat.card_coe_set_eq _
  rw [hcard, hset]
  have h1 : (1 : DihedralGroup (2 ^ (k + 2))) ∉
      ({r (2 ^ (k + 1)), sr j, sr (j + 2 ^ (k + 1))} : Set (DihedralGroup (2 ^ (k + 2)))) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    refine ⟨fun h => hh ?_, fun h => e22pd1_sr_ne_one _ h.symm,
      fun h => e22pd1_sr_ne_one _ h.symm⟩
    rw [← r_zero] at h
    simpa using (DihedralGroup.r.inj h).symm
  have h2 : r (2 ^ (k + 1) : ZMod (2 ^ (k + 2))) ∉
      ({sr j, sr (j + 2 ^ (k + 1))} : Set (DihedralGroup (2 ^ (k + 2)))) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨fun h => e22pd1_sr_ne_r _ _ h.symm, fun h => e22pd1_sr_ne_r _ _ h.symm⟩
  have h3 : sr j ≠ sr (j + 2 ^ (k + 1) : ZMod (2 ^ (k + 2))) := by
    intro h
    apply hh
    have := DihedralGroup.sr.inj h
    simpa using this
  rw [Set.ncard_insert_of_notMem h1, Set.ncard_insert_of_notMem h2, Set.ncard_pair h3]

theorem e22pd1_isKleinFour_kf (k : ℕ) (j : ZMod (2 ^ (k + 2))) :
    IsKleinFour ↥(e22pd1_kf k j) := by
  refine ⟨e22pd1_kf_card k j, ?_⟩
  have hh : (2 : ZMod (2 ^ (k + 2))) ^ (k + 1) ≠ 0 := e22pd1_two_pow_ne_zero (by omega)
  have : Nontrivial ↥(e22pd1_kf k j) :=
    ⟨⟨⟨r (2 ^ (k + 1)), e22pd1_mem_kf.mpr (Or.inr (Or.inl rfl))⟩, 1, fun h => hh (by
      have := congrArg Subtype.val h
      simpa [one_def] using (DihedralGroup.r.inj this))⟩⟩
  rw [Monoid.exponent_eq_prime_iff Nat.prime_two]
  intro g hg
  refine orderOf_eq_prime ?_ hg
  rw [pow_two]
  exact Subtype.ext (e22pd1_sq_eq_one_of_mem_kf g.2)

theorem e22pd1_rot_sq {k : ℕ} {i : ZMod (2 ^ (k + 2))} (h : r i * r i = 1) :
    i = 0 ∨ i = 2 ^ (k + 1) := by
  rw [r_mul_r, ← r_zero] at h
  have h1 : i + i = 0 := DihedralGroup.r.inj h
  have h2 : 2 * i = 0 := by linear_combination h1
  exact (e22pd1_two_mul_eq_zero_iff k i).mp h2

theorem e22pd1_ref_comm {k : ℕ} {a b : ZMod (2 ^ (k + 2))} (h : sr a * sr b = sr b * sr a) :
    b = a ∨ b = a + 2 ^ (k + 1) := by
  rw [sr_mul_sr, sr_mul_sr] at h
  have h1 : b - a = a - b := DihedralGroup.r.inj h
  have h2 : 2 * (b - a) = 0 := by linear_combination h1
  rcases (e22pd1_two_mul_eq_zero_iff k (b - a)).mp h2 with h3 | h3
  · exact Or.inl (by linear_combination h3)
  · exact Or.inr (by linear_combination h3)

theorem e22pd1_le_kf_of_mem {k : ℕ} {A : Subgroup (DihedralGroup (2 ^ (k + 2)))}
    (hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (hsq : ∀ x ∈ A, x * x = 1)
    {a : ZMod (2 ^ (k + 2))} (ha : sr a ∈ A) : A ≤ e22pd1_kf k a := by
  intro x hx
  rw [e22pd1_mem_kf]
  rcases x with i | b
  · rcases e22pd1_rot_sq (hsq _ hx) with rfl | rfl
    · left; simp
    · right; left; rfl
  · rcases e22pd1_ref_comm (hcomm _ ha _ hx) with rfl | rfl
    · right; right; left; rfl
    · right; right; right; rfl

theorem e22pd1_exists_ref {k : ℕ} {A : Subgroup (DihedralGroup (2 ^ (k + 2)))}
    (hsq : ∀ x ∈ A, x * x = 1) (hcard : 2 < Nat.card A) : ∃ a, sr a ∈ A := by
  by_contra hne
  push Not at hne
  have hsub : (A : Set (DihedralGroup (2 ^ (k + 2)))) ⊆ {1, r (2 ^ (k + 1))} := by
    intro x hx
    rcases x with i | b
    · rcases e22pd1_rot_sq (hsq _ hx) with rfl | rfl
      · left; simp
      · right; rfl
    · exact absurd hx (hne b)
  have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
  have h2 : ({1, r (2 ^ (k + 1))} : Set (DihedralGroup (2 ^ (k + 2)))).ncard ≤ 2 :=
    calc ({1, r (2 ^ (k + 1))} : Set (DihedralGroup (2 ^ (k + 2)))).ncard
        ≤ ({r (2 ^ (k + 1))} : Set (DihedralGroup (2 ^ (k + 2)))).ncard + 1 :=
          Set.ncard_insert_le _ _
      _ = 2 := by rw [Set.ncard_singleton]
  have h3 : Nat.card A = (A : Set (DihedralGroup (2 ^ (k + 2)))).ncard :=
    Nat.card_coe_set_eq _
  omega

theorem e22pd1_exists_kf_eq {k : ℕ} {A : Subgroup (DihedralGroup (2 ^ (k + 2)))}
    (hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (hsq : ∀ x ∈ A, x * x = 1)
    (hcard : 4 ≤ Nat.card A) : ∃ a, A = e22pd1_kf k a := by
  obtain ⟨a, ha⟩ := e22pd1_exists_ref hsq (by omega)
  exact ⟨a, Subgroup.eq_of_le_of_card_ge (e22pd1_le_kf_of_mem hcomm hsq ha)
    (by rw [e22pd1_kf_card]; exact hcard)⟩

theorem e22pd1_exists_kf_eq_of_isKleinFour {k : ℕ}
    {A : Subgroup (DihedralGroup (2 ^ (k + 2)))} (hA : IsKleinFour ↥A) :
    ∃ a, A = e22pd1_kf k a := by
  refine e22pd1_exists_kf_eq (fun x hx y hy => ?_) (fun x hx => ?_) (by rw [hA.card_four])
  · exact congrArg Subtype.val
      (mul_comm_of_exponent_two hA.exponent_two (⟨x, hx⟩ : A) ⟨y, hy⟩)
  · exact congrArg Subtype.val (@IsKleinFour.mul_self _ _ hA (⟨x, hx⟩ : A))

theorem e22pd1_r_mem_of_isKleinFour {k : ℕ} {A : Subgroup (DihedralGroup (2 ^ (k + 2)))}
    (hA : IsKleinFour ↥A) : r (2 ^ (k + 1)) ∈ A := by
  obtain ⟨a, rfl⟩ := e22pd1_exists_kf_eq_of_isKleinFour hA
  exact e22pd1_mem_kf.mpr (Or.inr (Or.inl rfl))

theorem e22pd1_r_h_comm {k : ℕ} (x : DihedralGroup (2 ^ (k + 2))) :
    r (2 ^ (k + 1)) * x = x * r (2 ^ (k + 1)) := by
  have hneg := e22pd1_neg_h k
  rcases x with i | i
  · rw [r_mul_r, r_mul_r]
    congr 1
    ring
  · rw [r_mul_sr, sr_mul_r]
    congr 1
    linear_combination hneg

end CFSG.Quasithin.E22L2
