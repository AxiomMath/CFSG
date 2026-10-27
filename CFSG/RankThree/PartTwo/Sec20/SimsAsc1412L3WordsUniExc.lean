module

public import CFSG.RankThree.PartTwo.Sec20.SimsAsc1412L3Excl
public import CFSG.RankThree.Classical.SteinbergBJUnitaryThreeInvolutions
import CFSG.RankThree.PartTwo.Sec20.SimsAsc1411U37Group
import CFSG.RankThree.PartTwo.KFacts.AutPSUFaithful
import CFSG.RankThree.PartTwo.KFacts.AutPSUInner

public section

namespace CFSG.RankThree.PartTwo.Sec20

open Matrix Module CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.RankThree.PartTwo.KFacts
open CFSG.RankThree.Classical

variable {K : Type} [Field K] {p : ℕ}

theorem unitaryScalars_eq_bot_exc (h : UnitaryFieldData p 1 K) (hp3 : p % 3 = 1) :
    unitaryScalars h 3 = ⊥ := by
  rw [← Subgroup.card_eq_one, card_unitaryScalars h (by norm_num), pow_one]
  exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr (by omega)

theorem unitaryProj_injective_exc (h : UnitaryFieldData p 1 K) (hp3 : p % 3 = 1) :
    Function.Injective (unitaryProj h 3) := by
  rw [← MonoidHom.ker_eq_bot_iff, ker_unitaryProj, unitaryScalars_eq_bot_exc h hp3]

theorem center_unitaryPSU_exc (h : UnitaryFieldData p 1 K) (hp3 : p % 3 = 1) :
    Subgroup.center (unitaryPSU h 3) = ⊥ := by
  have hq : 2 < p ^ 1 := by
    have := h.prime.two_le
    rw [pow_one]
    omega
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨g, rfl⟩ := unitaryProj_surjective h 3 x
  have hg : g ∈ Subgroup.center (unitarySU p 1 K 3) := by
    rw [Subgroup.mem_center_iff]
    intro y
    have := Subgroup.mem_center_iff.mp hx (unitaryProj h 3 y)
    rw [← map_mul, ← map_mul] at this
    exact unitaryProj_injective_exc h hp3 this
  rw [center_unitarySU_three (h := h) hq, unitaryScalars_eq_bot_exc h hp3, Subgroup.mem_bot] at hg
  rw [hg, map_one]
  exact Subgroup.one_mem _

theorem exists_sq_eq_neg_one_of_unitary_exc (h : UnitaryFieldData p 1 K) (hp4 : p % 4 = 3) :
    (p : K) = 0 ∧ ∃ z : K, z ^ 2 = -1 ∧ h.bar z = -z := by
  have := h.finite
  have := Fintype.ofFinite K
  have : CharP K p := h.charP
  have hp0 : (p : K) = 0 := CharP.cast_eq_zero K p
  obtain ⟨y, hy⟩ : IsSquare (-1 : K) := FiniteField.isSquare_neg_one_iff.mpr (by
    rw [← Nat.card_eq_fintype_card, h.card, Nat.pow_mod, hp4]
    norm_num)
  have hy2 : y ^ 2 = -1 := by rw [sq, ← hy]
  refine ⟨hp0, y, hy2, ?_⟩
  rw [h.bar_apply, pow_one]
  obtain ⟨m, hm⟩ : ∃ m, p = 4 * m + 3 := ⟨p / 4, by omega⟩
  rw [hm]
  calc y ^ (4 * m + 3) = (y ^ 2) ^ (2 * m + 1) * y := by ring
    _ = -y := by rw [hy2, pow_succ, pow_mul, neg_one_sq, one_pow]; ring

theorem excl1412_unitaryPSU3_of_exc (h : UnitaryFieldData p 1 K) (hp3 : p % 3 = 1)
    (hinner : Excl1412 (MulAut.conj (unitaryProj h 3 (unitaryInvT h))))
    {y : GL (Fin 3) K} (hy : y ∈ unitarySU p 1 K 3) (hsym : (y : Matrix (Fin 3) (Fin 3) K)ᵀ = y)
    {q k : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hk : 1 ≤ k)
    (h8 : ∀ e : ℕ, 1 ≤ e → e ≤ 8 → ¬ q ^ k ∣ 2 ^ e - 1) (hyq : q ^ k ∣ orderOf y)
    (α : MulAut (unitaryPSU h 3)) (hα : orderOf α = 2) : Excl1412 α := by
  have hp2 : p ≠ 2 := by omega
  have hq' : 2 < p ^ 1 := by
    have := h.prime.two_le
    rw [pow_one]
    omega
  have hα2 : α ^ 2 = 1 := by rw [← hα]; exact pow_orderOf_eq_one α
  obtain ⟨A, σ, rfl⟩ := exists_psuConj_mul_psuField hq' α
  have key :
      psuConj h (A * ⟨glAut σ A, glAut_mem_unitaryIsom3 σ A.2⟩) * psuField h (σ * σ) = 1 := by
    rw [map_mul, map_mul, ← psuField_mul_psuConj_mul_inv σ A, ← hα2, sq]
    simp only [mul_assoc, inv_mul_cancel_left]
  obtain ⟨hσσ, c, hcN, hcA⟩ := eq_one_of_psuConj_mul_psuField_eq_one _ _ key
  rcases ringEquiv_eq_refl_or_bar h hσσ with rfl | hσbar
  ·
    have hα' : psuConj h A * psuField h (RingEquiv.refl K) = psuConj h A := by
      rw [show RingEquiv.refl K = 1 from rfl, map_one, mul_one]
    rw [hα'] at hα hα2 ⊢
    obtain ⟨s, hs⟩ := mem_range_conj_of_mem_psuConj_range_of_coprime ⟨A, rfl⟩
      (m := 2) (by norm_num) hα2
    have hZ := center_unitaryPSU_exc h hp3
    have hs2 : orderOf s = 2 := by
      refine orderOf_eq_prime ?_ fun h1 => ?_
      · have hc : MulAut.conj (s ^ 2) = 1 := by rw [map_pow, hs, hα2]
        have : s ^ 2 ∈ Subgroup.center (unitaryPSU h 3) := by
          rw [Subgroup.mem_center_iff]
          intro z
          have e := congrArg (fun φ : MulAut (unitaryPSU h 3) => φ z) hc
          simp only [MulAut.conj_apply, MulAut.one_apply] at e
          calc z * s ^ 2 = s ^ 2 * z * (s ^ 2)⁻¹ * s ^ 2 := by rw [e]
            _ = s ^ 2 * z := by group
        rw [hZ, Subgroup.mem_bot] at this
        exact this
      · rw [h1, map_one] at hs
        rw [← hs, orderOf_one] at hα
        exact absurd hα (by norm_num)
    obtain ⟨g, hg⟩ := isConj_iff.mp (isConj_unitaryProj_unitaryInvT h hp2 hs2)
    have hβ : MulAut.conj s = MulAut.conj g⁻¹ * MulAut.conj (unitaryProj h 3 (unitaryInvT h)) *
        (MulAut.conj g⁻¹)⁻¹ := by
      rw [← hg]
      simp only [map_mul, map_inv]
      group
    rw [← hs, hβ]
    exact hinner.conj _
  ·
    have hσmat : ∀ M : Matrix (Fin 3) (Fin 3) K, M.map σ = M.map h.bar := fun M => by
      ext i j
      exact hσbar _
    have hAA : (A : GL (Fin 3) K) * glAut σ A = 1 := by
      have hc1 : c = 1 := by
        have hmat := congrArg (fun M : GL (Fin 3) K => (M : Matrix (Fin 3) (Fin 3) K).det) hcA
        simp only [Subgroup.coe_mul, Units.val_mul, coe_glAut, det_mul,
          GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.det_diagonal,
          Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hmat
        have hσdet : (((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).map σ).det =
            h.bar ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det := by
          rw [hσmat, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
        have hN := norm_det_of_mem_unitaryIsom3 A.2
        rw [UnitaryFieldData.norm] at hN
        have hc3 : (c : K) ^ 3 = 1 := by rw [← hmat, hσdet, hN]
        have hcp : (c : K) ^ (p + 1) = 1 := by
          rw [UnitaryFieldData.norm, h.bar_apply, pow_one] at hcN
          rw [← hcN]
          ring
        obtain ⟨m, hm⟩ : ∃ m, p + 1 = 3 * m + 2 := ⟨p / 3, by omega⟩
        have hc2 : (c : K) ^ 2 = 1 := by
          rw [hm, pow_add, pow_mul, hc3, one_pow, one_mul] at hcp
          exact hcp
        apply Units.ext
        rw [Units.val_one]
        calc (c : K) = (c : K) ^ 2 * c := by rw [hc2, one_mul]
          _ = (c : K) ^ 3 := by ring
          _ = 1 := hc3
      have e := hcA
      rw [hc1, map_one] at e
      exact e
    have hAAm : ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).map h.bar = 1 := by
      have := congrArg (fun M : GL (Fin 3) K => (M : Matrix (Fin 3) (Fin 3) K)) hAA
      simpa [coe_glAut, hσmat] using this
    obtain ⟨C, d, hAC, hCC⟩ := exists_antiunitary_normalForm_unitary3 h hp2 A.2 hAAm
    have hyU := (mem_unitarySU_iff h).mp hy
    have hyS : y ∈ gramSU h (d • (1 : Matrix (Fin 3) (Fin 3) K)) := by
      refine mem_gramSU.mpr ⟨?_, hyU.1⟩
      rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hyU.2]
    have hxS : C * y * C⁻¹ ∈ unitarySU p 1 K 3 := by
      rw [unitarySU_eq_gramSU h 3]
      exact conj_mem_gramSU_of_gram h hCC hyS
    set x : unitarySU p 1 K 3 := ⟨C * y * C⁻¹, hxS⟩
    have hyσ : glAut σ y = y⁻¹ := by
      apply Units.ext
      rw [coe_glAut, hσmat, Matrix.coe_units_inv]
      have h1 : ((y : Matrix (Fin 3) (Fin 3) K).map h.bar)ᵀ = (y : Matrix (Fin 3) (Fin 3) K)⁻¹ :=
        (Matrix.inv_eq_left_inv hyU.2).symm
      rw [← Matrix.transpose_transpose ((y : Matrix (Fin 3) (Fin 3) K).map h.bar), h1,
        Matrix.transpose_nonsing_inv, hsym]
    have hCσ : glAut σ C = (A : GL (Fin 3) K)⁻¹ * C := by
      rw [eq_inv_mul_iff_mul_eq]
      apply Units.ext
      rw [Units.val_mul, coe_glAut, hσmat]
      exact hAC
    have hαx : (psuConj h A * psuField h σ) (unitaryProj h 3 x) = (unitaryProj h 3 x)⁻¹ := by
      rw [MulAut.mul_apply, ← map_inv]
      change psuConj h A (psuField h σ (x : unitaryPSU h 3)) = ((x⁻¹ : unitarySU p 1 K 3) :
        unitaryPSU h 3)
      rw [psuField_mk, psuConj_mk]
      congr 1
      apply Subtype.ext
      rw [coe_suConj, coe_suField, Subgroup.coe_inv]
      change (A : GL (Fin 3) K) * glAut σ (C * y * C⁻¹) * (A : GL (Fin 3) K)⁻¹ = (C * y * C⁻¹)⁻¹
      rw [map_mul, map_mul, map_inv, hyσ, hCσ]
      group
    have hxo : orderOf (unitaryProj h 3 x) = orderOf y := by
      rw [orderOf_injective _ (unitaryProj_injective_exc h hp3) x, ← Subgroup.orderOf_coe]
      change orderOf (C * y * C⁻¹) = orderOf y
      rw [← MulAut.conj_apply]
      exact MulEquiv.orderOf_eq (MulAut.conj C) y
    refine Or.inl ⟨unitaryProj h 3 x, q, k, hq, hq2, hk, h8, ?_⟩
    have hw : (psuConj h A * psuField h σ) (unitaryProj h 3 x) * (unitaryProj h 3 x)⁻¹ =
        ((unitaryProj h 3 x) ^ 2)⁻¹ := by
      rw [hαx, sq, _root_.mul_inv_rev]
    have h2o : orderOf (unitaryProj h 3 x) ∣ 2 * orderOf ((unitaryProj h 3 x) ^ 2) := by
      apply orderOf_dvd_of_pow_eq_one
      rw [pow_mul, pow_orderOf_eq_one]
    have hcop : (q ^ k).Coprime 2 :=
      Nat.Coprime.pow_left k ((Nat.coprime_primes hq Nat.prime_two).mpr hq2)
    rw [hw, orderOf_inv]
    have hxq : q ^ k ∣ orderOf (unitaryProj h 3 x) := by rw [hxo]; exact hyq
    exact hcop.dvd_of_dvd_mul_left (hxq.trans h2o)

end CFSG.RankThree.PartTwo.Sec20
