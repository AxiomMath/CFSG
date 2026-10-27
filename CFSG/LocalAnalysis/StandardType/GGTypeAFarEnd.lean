module

public import CFSG.LinearAlgebra.LinearGroups.Perfect
public import CFSG.LocalAnalysis.StandardType.GGTypeAEndNode

public section

namespace CFSG.StandardType

open Matrix
open scoped commutatorElement

variable {F : Type} [Field F]

theorem slPerfect_of_four_le_card [Finite F] {m : ℕ} (hm : 2 ≤ m) (hF : 4 ≤ Nat.card F) :
    Group.IsPerfect (SpecialLinearGroup (Fin m) F) := by
  apply CFSG.LinearGroups.special_linear_isPerfect hm
  right
  haveI : Fintype F := Fintype.ofFinite F
  have hcard : 4 ≤ (Finset.univ : Finset F).card := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
    exact hF
  obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (n := 4) hcard
  exact ⟨s, hs⟩

theorem range_le_commutator_of_isPerfect {H X : Type*} [Group H] [Group X]
    (hH : Group.IsPerfect H) (f : H →* X) : f.range ≤ ⁅f.range, f.range⁆ := by
  haveI := hH
  have h : ⁅f.range, f.range⁆ = f.range := Subgroup.isPerfect_iff.mp (Group.IsPerfect.range f)
  rw [h]

theorem diag2nUnit_mul {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R] {i j : ι}
    (hij : i ≠ j) (t s : Rˣ) :
    Matrix.SpecialLinearGroup.diag2nUnit hij t * Matrix.SpecialLinearGroup.diag2nUnit hij s =
      Matrix.SpecialLinearGroup.diag2nUnit hij (t * s) := by
  apply Matrix.SpecialLinearGroup.coeMonoidHom_injective
  simp only [map_mul, Matrix.SpecialLinearGroup.coeMonoidHom_apply,
    Matrix.SpecialLinearGroup.diag2nUnit_coe, Matrix.diagonal_mul_diagonal]
  congr 1
  funext r
  by_cases hri : r = i
  · subst hri
    simp [hij, Units.val_mul]
  · by_cases hrj : r = j
    · subst hrj
      simp [hri, Units.val_mul, Units.val_inv_eq_inv_val, _root_.mul_inv_rev, mul_comm]
    · simp [hri, hrj]

theorem diag2nUnit_pow {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R] {i j : ι}
    (hij : i ≠ j) (t : Rˣ) (n : ℕ) :
    Matrix.SpecialLinearGroup.diag2nUnit hij t ^ n =
      Matrix.SpecialLinearGroup.diag2nUnit hij (t ^ n) := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, ih, pow_succ, diag2nUnit_mul]

theorem exists_orderP_mem_lowerLower [Finite F] {X : Type*} [Group X] {p : ℕ} [Fact p.Prime]
    (hp : p ∣ Nat.card Fˣ) {m : ℕ} (hm : 2 ≤ m)
    {φ : SpecialLinearGroup (Fin (m + 1 + 1)) F →* X}
    (hker : φ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (m + 1 + 1)) F)) :
    ∃ g ∈ ((φ.comp (slLowerBlockHom (m + 1) F)).comp (slLowerBlockHom m F)).range,
      g ≠ 1 ∧ g ^ p = 1 := by
  haveI : NeZero m := ⟨by omega⟩
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' p hp
  have hprime : p.Prime := Fact.out
  have ht_ne : t ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ht
    exact hprime.ne_one ht.symm
  have h01 : (0 : Fin m) ≠ ⟨1, by omega⟩ := by
    intro h
    have hv := congrArg Fin.val h
    simp at hv
  have hφι : Function.Injective (φ.comp (slLowerBlockHom (m + 1) F)) :=
    injective_comp_slLowerBlockHom hker
  have hψ_inj : Function.Injective
      ((φ.comp (slLowerBlockHom (m + 1) F)).comp (slLowerBlockHom m F)) :=
    hφι.comp (slLowerBlockHom_injective (n := m) (F := F))
  have hdiag_ne : Matrix.SpecialLinearGroup.diag2nUnit h01 t ≠ 1 := by
    intro h
    have h00 : (Matrix.SpecialLinearGroup.diag2nUnit h01 t :
        Matrix (Fin m) (Fin m) F) 0 0 = 1 := by
      rw [h]; simp
    rw [Matrix.SpecialLinearGroup.diag2nUnit_coe, Matrix.diagonal_apply_eq] at h00
    simp [h01] at h00
    exact ht_ne h00
  refine ⟨_, MonoidHom.mem_range.mpr
      ⟨Matrix.SpecialLinearGroup.diag2nUnit h01 t, rfl⟩, ?_, ?_⟩
  · intro hg
    exact hdiag_ne (hψ_inj (by rw [map_one]; exact hg))
  · rw [← map_pow, diag2nUnit_pow]
    have ht_pow : t ^ p = 1 := by
      rw [← ht]; exact pow_orderOf_eq_one t
    rw [ht_pow, Matrix.SpecialLinearGroup.diag2nUnit_one, map_one]

theorem pow_natCard_units_eq_one_of_centralizes_range [Finite F] {X : Type*} [Group X] {m : ℕ}
    (hperf : Group.IsPerfect (SpecialLinearGroup (Fin m) F))
    {φ : SpecialLinearGroup (Fin m) F →* X}
    (hker : φ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin m) F)) {u : X}
    (hu : u ∈ φ.range) (hcent : ∀ s, u * φ s = φ s * u) : u ^ Nat.card Fˣ = 1 := by
  obtain ⟨s₀, rfl⟩ := MonoidHom.mem_range.mp hu
  by_cases hm0 : m = 0
  · subst hm0
    rw [show s₀ = 1 from Subsingleton.elim s₀ 1, map_one, one_pow]
  · have hcomm (s : SpecialLinearGroup (Fin m) F) :
        ⁅s, s₀⁆ ∈ Subgroup.center (SpecialLinearGroup (Fin m) F) := by
      apply hker
      rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact (hcent s).symm
    have hs₀Z : s₀ ∈ Subgroup.center (SpecialLinearGroup (Fin m) F) := by
      have hx : QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (Fin m) F)) s₀ ∈
          Subgroup.center (SpecialLinearGroup (Fin m) F ⧸
            Subgroup.center (SpecialLinearGroup (Fin m) F)) := by
        rw [Subgroup.mem_center_iff]
        intro y
        obtain ⟨g, rfl⟩ :=
          QuotientGroup.mk'_surjective (Subgroup.center (SpecialLinearGroup (Fin m) F)) y
        have h1 : ⁅QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (Fin m) F)) g,
            QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (Fin m) F)) s₀⁆ = 1 := by
          rw [← map_commutatorElement]
          exact (QuotientGroup.eq_one_iff
            (N := Subgroup.center (SpecialLinearGroup (Fin m) F)) ⁅g, s₀⁆).mpr (hcomm g)
        exact commutatorElement_eq_one_iff_mul_comm.mp h1
      have hbot : Subgroup.center (SpecialLinearGroup (Fin m) F ⧸
          Subgroup.center (SpecialLinearGroup (Fin m) F)) = ⊥ := by
        haveI := hperf
        exact Group.IsPerfect.center_quotient_center_eq_bot _
      rw [hbot, Subgroup.mem_bot] at hx
      exact (QuotientGroup.eq_one_iff
        (N := Subgroup.center (SpecialLinearGroup (Fin m) F)) s₀).mp hx
    rw [Matrix.SpecialLinearGroup.mem_center_iff] at hs₀Z
    obtain ⟨r, hrpow, hr_eq⟩ := hs₀Z
    rw [Fintype.card_fin] at hrpow
    have hr_ne : r ≠ 0 := by
      intro h
      rw [h, zero_pow hm0] at hrpow
      exact zero_ne_one hrpow
    have hrN : r ^ Nat.card Fˣ = 1 := by
      have hc : (Units.mk0 r hr_ne : Fˣ) ^ Nat.card Fˣ = 1 := pow_card_eq_one'
      have hv : ((Units.mk0 r hr_ne : Fˣ) : F) ^ Nat.card Fˣ = 1 := by
        rw [← Units.val_pow_eq_pow_val, hc, Units.val_one]
      simpa using hv
    have hs0pow_mat : ((s₀ ^ Nat.card Fˣ : SpecialLinearGroup (Fin m) F) :
        Matrix (Fin m) (Fin m) F) = Matrix.scalar (Fin m) (r ^ Nat.card Fˣ) := by
      rw [Matrix.SpecialLinearGroup.coe_pow, ← hr_eq]
      exact (map_pow (Matrix.scalar (Fin m)) r (Nat.card Fˣ)).symm
    have hs0pow : s₀ ^ Nat.card Fˣ = 1 := by
      apply Subtype.ext
      rw [hs0pow_mat, hrN]
      simp
    rw [← map_pow, hs0pow, map_one]

theorem eq_one_of_mem_range_of_centralizes [Finite F] {X : Type*} [Group X] {m : ℕ}
    (hperf : Group.IsPerfect (SpecialLinearGroup (Fin m) F)) (hF : Odd (Nat.card Fˣ))
    {φ : SpecialLinearGroup (Fin m) F →* X}
    (hker : φ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin m) F)) {u : X}
    (hu : u ∈ φ.range) (hcent : ∀ s, u * φ s = φ s * u) (huu : u * u = 1) : u = 1 := by
  have hpow := pow_natCard_units_eq_one_of_centralizes_range hperf hker hu hcent
  obtain ⟨k, hk⟩ := hF
  rw [hk] at hpow
  have hu2 : u ^ 2 = 1 := by rw [pow_two]; exact huu
  have h1 : u ^ (2 * k + 1) = u := by
    rw [pow_succ, pow_mul, hu2, one_pow, one_mul]
  rwa [h1] at hpow

end CFSG.StandardType
