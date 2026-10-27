module

public import CFSG.LocalAnalysis.StandardType.GGSixAutStructurePSUFixed

public section

namespace CFSG.StandardType

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag Matrix
open CFSG.LieType.Universal.Unitary (SU antidiag)
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_involutive)
open CFSG.SeitzReduction.F4Pilot (gramSUToSL coe_gramSUToSL gramSUToSL_injective)

namespace AutPSU

section Fixed

variable {f : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2] (h : UnitaryFieldData 2 f K)
  {n : ℕ}

theorem compl_fixes_projU {c : MulAut (PJ h n)} (hc : c ∈ compl h)
    (x : SU (unitaryInvolution K 2 f) n)
    (hx : ∀ φ : K ≃+* K,
      ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map φ = (x : GL (Fin n) K)) :
    c (projU h x) = projU h x := by
  rw [projU_apply]
  exact compl_fixes_of_map h hc _ hx

theorem compl_fixes_lroot {c : MulAut (PJ h n)} (hc : c ∈ compl h) {i : Fin n}
    (hi : i ≠ Fin.rev i) :
    c (projU h (lroot (unitaryInvolution K 2 f) hi)) =
      projU h (lroot (unitaryInvolution K 2 f) hi) :=
  compl_fixes_projU h hc _ fun φ => map_lroot _ φ hi

theorem compl_fixes_sroot {c : MulAut (PJ h n)} (hc : c ∈ compl h) {i j : Fin n} (hij : i ≠ j)
    (hi : i ≠ Fin.rev i) (hj : j ≠ Fin.rev j) :
    c (projU h (sroot (unitaryInvolution K 2 f) (sigma_involutive h) hij hi hj)) =
      projU h (sroot (unitaryInvolution K 2 f) (sigma_involutive h) hij hi hj) :=
  compl_fixes_projU h hc _ fun φ => map_sroot _ _ φ hij hi hj

end Fixed

section Elements

variable {f m : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2] (h : UnitaryFieldData 2 f K)

noncomputable abbrev rootU (m : ℕ) : SU (unitaryInvolution K 2 f) (m + 1) :=
  ggInvSU (unitaryInvolution K 2 f) (m + 1) 1

theorem coe_rootU (hm : 1 ≤ m) :
    (((rootU m : SU (unitaryInvolution K 2 f) (m + 1)) : GL (Fin (m + 1)) K) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) K) = 1 + single (Fin.last m) 0 1 := by
  rw [coe_ggInvSU _ (by omega), ggInvUMatrix_one (by omega)]
  congr 2

theorem gramSUToSL_rootU (hm : 1 ≤ m) :
    gramSUToSL h _ (suEquiv h (rootU m)) = AutPSL.rootInv (K := K) hm := by
  apply Subtype.ext
  change (((rootU m : SU (unitaryInvolution K 2 f) (m + 1)) : GL (Fin (m + 1)) K) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) K) = ((AutPSL.rootInv (K := K) hm :
      SpecialLinearGroup (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K)
  rw [coe_rootU hm]
  rfl

theorem compl_fixes_rootU (hm : 1 ≤ m) {c : MulAut (PJ h (m + 1))} (hc : c ∈ compl h) :
    c (projU h (rootU m)) = projU h (rootU m) :=
  compl_fixes_projU h hc _ fun φ => by rw [coe_ggInvSU _ (by omega), map_ggInvUMatrix]

theorem rev_idxOne_ne (hm : 3 ≤ m) :
    Fin.rev (AutPSL.idxOne (m := m) (by omega)) ≠
      Fin.rev (Fin.rev (AutPSL.idxOne (m := m) (by omega))) := by
  rw [Fin.rev_rev]
  exact (AutPSL.idxOne_ne_rev hm).symm

@[expose] noncomputable def ordThreeU (hm : 3 ≤ m) : SU (unitaryInvolution K 2 f) (m + 1) :=
  lroot (unitaryInvolution K 2 f) (AutPSL.idxOne_ne_rev hm) *
    lroot (unitaryInvolution K 2 f) (rev_idxOne_ne hm)

theorem gramSUToSL_ordThreeU (hm : 3 ≤ m) :
    gramSUToSL h _ (suEquiv h (ordThreeU hm)) = AutPSL.ordThreeElt (K := K) hm := by
  rw [ordThreeU, map_mul, map_mul, gramSUToSL_lroot, gramSUToSL_lroot, AutPSL.ordThreeElt,
    AutPSL.ordThree,
    AutPSL.transvection_congr (rev_idxOne_ne hm) (AutPSL.idxOne_ne_rev hm).symm rfl
      (Fin.rev_rev _)]

theorem compl_fixes_ordThreeU (hm : 3 ≤ m) {c : MulAut (PJ h (m + 1))} (hc : c ∈ compl h) :
    c (projU h (ordThreeU hm)) = projU h (ordThreeU hm) := by
  rw [ordThreeU, map_mul, map_mul, compl_fixes_lroot h hc, compl_fixes_lroot h hc]

theorem ordThreeU_comm_rootU (hm : 3 ≤ m) :
    projU h (ordThreeU hm) * projU h (rootU m) = projU h (rootU m) * projU h (ordThreeU hm) := by
  rw [← map_mul, ← map_mul]
  congr 1
  apply (suEquiv h).injective
  apply gramSUToSL_injective h _
  rw [map_mul, map_mul, map_mul, map_mul, gramSUToSL_ordThreeU, gramSUToSL_rootU h (by omega),
    AutPSL.ordThree_comm_rootInv hm]

theorem orderOf_projU_ordThreeU (hm : 3 ≤ m) : orderOf (projU h (ordThreeU hm)) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine orderOf_eq_prime ?_ ?_
  · have e : (ordThreeU hm : SU (unitaryInvolution K 2 f) (m + 1)) ^ 3 = 1 := by
      apply (suEquiv h).injective
      apply gramSUToSL_injective h _
      rw [map_pow, map_pow, gramSUToSL_ordThreeU, AutPSL.ordThree_pow_three, map_one, map_one]
    rw [← map_pow, e, map_one]
  · intro h1
    rw [projU_apply, QuotientGroup.eq_one_iff] at h1
    obtain ⟨c, -, hcn, hc⟩ := h1
    apply AutPSL.ordThree_not_mem_scalars (K := K) (AutPSL.idxOne_ne_rev hm)
    refine ⟨c, hcn, ?_⟩
    change ((AutPSL.ordThreeElt (K := K) hm : SpecialLinearGroup (Fin (m + 1)) K) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) K) = _
    rw [← gramSUToSL_ordThreeU h hm]
    change (((suEquiv h (ordThreeU hm) : XJ h (m + 1)) : GL (Fin (m + 1)) K) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) K) = _
    rw [hc, GeneralLinearGroup.coe_scalar]

end Elements

section Class

variable {f m : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2] (h : UnitaryFieldData 2 f K)

theorem exists_conj_of_mem_inndiag (hm : 3 ≤ m) {e : MulAut (PJ h (m + 1))}
    (he : e ∈ inndiag h) :
    ∃ k : PJ h (m + 1), e (projU h (rootU m)) =
      k * projU h (rootU m) * (k⁻¹ : PJ h (m + 1)) := by
  obtain ⟨A, rfl⟩ := he
  set σ := unitaryInvolution K 2 f with hσdef
  have hσ : ∀ c, σ (σ c) = c := sigma_involutive h
  set ν : K := ((A : GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K).det with hνdef
  have hνn : ν * σ ν = 1 := by
    have e := norm_det_eq_one h (gramJ (m + 1)) A.2
    rwa [UnitaryFieldData.norm, RootDetectSU.bar_eq h] at e
  have hν0 : ν ≠ 0 := left_ne_zero_of_mul_eq_one hνn
  obtain ⟨ρ, hρ0, hρ⟩ := RootDetectSU.exists_div_eq h hνn
  set b : Fin (m + 1) := AutPSL.idxOne (by omega) with hbdef
  have hb : b ≠ Fin.rev b := AutPSL.idxOne_ne_rev hm
  have hdu := RootDetectSU.pairDiag_unitary hσ hb hρ0
  set d : GL (Fin (m + 1)) K := RootDetectSU.diagGL (RootDetectSU.pairDiag σ b ρ)
    (CFSG.LieType.Universal.Unitary.ne_zero_of_unitary hdu) with hddef
  have hdU : d ∈ primeFormUnitary h
      ((gramJ (m + 1) : GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K) :=
    RootDetectSU.diagGL_mem_primeFormUnitary h hdu
  have hddet : ((d : GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K).det = ν := by
    rw [hddef, RootDetectSU.coe_diagGL, det_diagonal, RootDetectSU.prod_pairDiag hb,
      ← div_eq_mul_inv, hρ]
  set s : GL (Fin (m + 1)) K := (A : GL (Fin (m + 1)) K) * d⁻¹ with hsdef
  have hs : s ∈ XJ h (m + 1) := by
    refine (mem_gramSU_iff_unitary h).mpr ⟨mul_mem A.2 (inv_mem hdU), ?_⟩
    have e : ((s * d : GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K).det = ν := by
      rw [hsdef, inv_mul_cancel_right]
    rw [Units.val_mul, det_mul, hddet] at e
    exact mul_right_cancel₀ hν0 (e.trans (one_mul ν).symm)
  have h0 : RootDetectSU.pairDiag σ b ρ 0 = 1 :=
    RootDetectSU.pairDiag_of_ne (by simp [hbdef, AutPSL.idxOne, Fin.ext_iff])
      (by simp only [hbdef, AutPSL.idxOne, ne_eq, Fin.ext_iff, Fin.val_rev, Fin.val_zero]; omega) ρ
  have hl : RootDetectSU.pairDiag σ b ρ (Fin.last m) = 1 :=
    RootDetectSU.pairDiag_of_ne
      (by simp only [hbdef, AutPSL.idxOne, ne_eq, Fin.ext_iff, Fin.val_last]; omega)
      (by simp only [hbdef, AutPSL.idxOne, ne_eq, Fin.ext_iff, Fin.val_rev, Fin.val_last]; omega) ρ
  have hmat : (1 + single (Fin.last m) 0 (1 : K)) * diagonal (RootDetectSU.pairDiag σ b ρ) =
      diagonal (RootDetectSU.pairDiag σ b ρ) * (1 + single (Fin.last m) 0 (1 : K)) := by
    rw [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one]
    congr 1
    ext a c
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.single_apply]
    split_ifs with hac
    · obtain ⟨rfl, rfl⟩ := hac
      rw [h0, hl]
    · simp
  have hcomm : ((rootU m : SU σ (m + 1)) : GL (Fin (m + 1)) K) * d =
      d * ((rootU m : SU σ (m + 1)) : GL (Fin (m + 1)) K) := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, coe_rootU (by omega), hddef, RootDetectSU.coe_diagGL]
    exact hmat
  refine ⟨((⟨s, hs⟩ : XJ h (m + 1)) : PJ h (m + 1)), ?_⟩
  rw [projU_apply]
  change primeFormConjHom h _ A ((suEquiv h (rootU m) : XJ h (m + 1)) : PJ h (m + 1)) = _
  rw [primeFormConjHom_mk, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  congr 1
  apply Subtype.ext
  change (A : GL (Fin (m + 1)) K) * ((rootU m : SU σ (m + 1)) : GL (Fin (m + 1)) K) *
      (A : GL (Fin (m + 1)) K)⁻¹ = s * ((rootU m : SU σ (m + 1)) : GL (Fin (m + 1)) K) * s⁻¹
  rw [hsdef]
  calc (A : GL (Fin (m + 1)) K) * ((rootU m : SU σ (m + 1)) : GL (Fin (m + 1)) K) *
        (A : GL (Fin (m + 1)) K)⁻¹ = (A : GL (Fin (m + 1)) K) * d⁻¹ *
          (d * ((rootU m : SU σ (m + 1)) : GL (Fin (m + 1)) K)) * (A : GL (Fin (m + 1)) K)⁻¹ := by
        group
    _ = (A : GL (Fin (m + 1)) K) * d⁻¹ * (((rootU m : SU σ (m + 1)) : GL (Fin (m + 1)) K) * d) *
          (A : GL (Fin (m + 1)) K)⁻¹ := by rw [hcomm]
    _ = _ := by group

theorem goodAut_of_core (hm : 3 ≤ m) {c : MulAut (PJ h (m + 1))} (hc : c ∈ compl h)
    (hO : ∀ Q : Subgroup (PJ h (m + 1)), (∀ q ∈ Q, c q = q) → IsPGroup 2 Q →
      (∀ y : PJ h (m + 1), c y = y → ∀ q ∈ Q, y * q * y⁻¹ ∈ Q) → Q = ⊥)
    {e : MulAut (PJ h (m + 1))} (he : e ∈ inndiag h) :
    GGGoodAut (projU h (rootU m)) (e * c * e⁻¹) := by
  refine GGGoodAut.conj ?_ e (exists_conj_of_mem_inndiag h hm he)
  refine ⟨hO, 1, ?_, projU h (ordThreeU hm), compl_fixes_ordThreeU h hm hc, ?_, ?_, ?_⟩
  · simp only [one_mul, inv_one, mul_one]
    exact compl_fixes_rootU h (by omega) hc
  · simp only [one_mul, inv_one, mul_one]
    exact ordThreeU_comm_rootU h hm
  · intro h1
    have := orderOf_projU_ordThreeU h hm
    rw [h1, orderOf_one] at this
    omega
  · rw [orderOf_projU_ordThreeU h hm]
    decide

end Class

end AutPSU

end CFSG.StandardType
