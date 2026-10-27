module

public import CFSG.LinearAlgebra.SLThreeSymmetricTorus
public import CFSG.GH74.KGroups.L3EpsBlockAut
public import CFSG.GH74.KGroups.L3EpsAutDiag
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4StabL
public import CFSG.GH74.GLS.IVK.Proofs2.Std44LinConj
public import CFSG.CGT.Timmesfeld75.MultPrime
public import CFSG.Permutation.FiveTransitive.SylowThreeFixedOrbits
public import CFSG.GroupTheory.OddInvariantSubgroupFamily
public import CFSG.GroupTheory.MulAutCongr
public import Mathlib.GroupTheory.GroupAction.Defs
public import CFSG.Certificates.Kernel.ThDemp.OrbCent
public import CFSG.CGT.Timmesfeld75.OddCenter
public import CFSG.CGT.Timmesfeld75.Sec5FiveEng
public import CFSG.CGT.Timmesfeld75.Sec5Nine
public import CFSG.CGT.Timmesfeld75.Sec5Ten
public import CFSG.CGT.Timmesfeld75.Step57Reduction
public import CFSG.ClassicalInvolution.WeakCT.StandardPair
public import CFSG.GH74.BNPair.Defs
public import CFSG.GH74.GLS.IVK.L2.F1
public import CFSG.GH74.KGroups.L3EpsNoNormalThree
public import CFSG.GH74.KGroups.L3EpsOutExp
public import CFSG.LieType.CurtisTits.SpecialLinear
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDescentEndpoint
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixStructure
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherScalarSquareSplit
public import CFSG.Sporadic.M23.M23Group
public import CFSG.Sporadic.Th.Max3.Packet
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.DicksonSplitTorus
public import Certificates.Certificate1
public import Certificates.Certificate2

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG CFSG.Open CFSG.Quasithin CFSG.LinearAlgebra
open CFSG.GH74.KGroups.L3Eps
open CFSG.ComponentClassification.CatalogueBHigherLinearAction
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ClassicalInvolution.WeakCT
open CFSG.RankThree.CentralCover
open Subgroup Matrix
open scoped MatrixGroups

variable {K : Type} [Field K] [Finite K]

private noncomputable def stdX : projectiveSL 3 K :=
  proj 3 K (oddDiag₃SL (K := K))

private noncomputable def stdY : projectiveSL 3 K :=
  proj 3 K (oddDiag₂SL (K := K))

private theorem stdX_eq_proj_dNeg : stdX (K := K) = proj 3 K ((dNeg : SL(3, K))) := by
  rw [stdX]
  congr 1

private theorem stdX_mul_self : stdX (K := K) * stdX (K := K) = 1 := by
  rw [stdX, ← map_mul, show oddDiag₃SL (K := K) * oddDiag₃SL (K := K) = 1 by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one, coe_oddDiag₃SL]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three],
    map_one]

private theorem stdY_mul_self : stdY (K := K) * stdY (K := K) = 1 := by
  rw [stdY, ← map_mul, show oddDiag₂SL (K := K) * oddDiag₂SL (K := K) = 1 by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one, coe_oddDiag₂SL]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three],
    map_one]

private theorem fieldAut_stdX (σ : K ≃+* K) : fieldAut 3 K σ (stdX (K := K)) = stdX (K := K) := by
  rw [stdX, fieldAut_proj]
  congr 1
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, coe_oddDiag₃SL]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

private theorem fieldAut_stdY (σ : K ≃+* K) : fieldAut 3 K σ (stdY (K := K)) = stdY (K := K) := by
  rw [stdY, fieldAut_proj]
  congr 1
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, coe_oddDiag₂SL]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

private theorem dualAut_stdX : dualAut 3 K (stdX (K := K)) = stdX (K := K) := by
  rw [stdX_eq_proj_dNeg, dualAut_proj]
  congr 1
  exact dNeg_inv_transpose (F := K)

private theorem dualAut_stdY : dualAut 3 K (stdY (K := K)) = stdY (K := K) := by
  rw [stdY, dualAut_proj]
  congr 1
  have hsq : oddDiag₂SL (K := K) * oddDiag₂SL (K := K) = 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one, coe_oddDiag₂SL]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  rw [inv_eq_of_mul_eq_one_right hsq]
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_transpose, coe_oddDiag₂SL]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

private theorem dualAut_pow_stdX {ε : ℕ} (hε : ε ≤ 1) :
    (dualAut 3 K ^ ε) (stdX (K := K)) = stdX (K := K) := by
  interval_cases ε
  · rw [pow_zero, MulAut.one_apply]
  · rw [pow_one, dualAut_stdX]

private theorem dualAut_pow_stdY {ε : ℕ} (hε : ε ≤ 1) :
    (dualAut 3 K ^ ε) (stdY (K := K)) = stdY (K := K) := by
  interval_cases ε
  · rw [pow_zero, MulAut.one_apply]
  · rw [pow_one, dualAut_stdY]

private theorem exists_diagonal_form_of_fixes (h2 : (2 : K) ≠ 0)
    (α : MulAut (projectiveSL 3 K)) (hαx : α (stdX (K := K)) = stdX (K := K))
    (hαy : α (stdY (K := K)) = stdY (K := K)) :
    ∃ (A : GL (Fin 3) K) (σ : K ≃+* K) (ε : ℕ) (a0 a1 a2 : K),
      ε ≤ 1 ∧ α = conjAut 3 K A * fieldAut 3 K σ * dualAut 3 K ^ ε ∧
      (A : Matrix (Fin 3) (Fin 3) K) = diagonal ![a0, a1, a2] ∧
      a0 ≠ 0 ∧ a2 ≠ 0 := by
  obtain ⟨A, σ, ε, hε, hα⟩ :=
    (automorphism_generation (K := K) (n := 3) (by norm_num)).2 α
  have hfx : fieldAut 3 K σ (stdX (K := K)) = stdX (K := K) := fieldAut_stdX σ
  have hfy : fieldAut 3 K σ (stdY (K := K)) = stdY (K := K) := fieldAut_stdY σ
  have hdx : (dualAut 3 K ^ ε) (stdX (K := K)) = stdX (K := K) := dualAut_pow_stdX hε
  have hdy : (dualAut 3 K ^ ε) (stdY (K := K)) = stdY (K := K) := dualAut_pow_stdY hε
  have hcx : conjAut 3 K A (stdX (K := K)) = stdX (K := K) := by
    rw [hα] at hαx
    rw [MulAut.mul_apply, MulAut.mul_apply, hdx, hfx] at hαx
    exact hαx
  have hcy : conjAut 3 K A (stdY (K := K)) = stdY (K := K) := by
    rw [hα] at hαy
    rw [MulAut.mul_apply, MulAut.mul_apply, hdy, hfy] at hαy
    exact hαy
  have hcx' : proj 3 K (slConjugation 3 K A ((dNeg : SL(3, K)))) =
      proj 3 K ((dNeg : SL(3, K))) := by
    have h := hcx
    rw [stdX_eq_proj_dNeg] at h
    rwa [conjAut_proj] at h
  have hA3 : (A : Matrix (Fin 3) (Fin 3) K) * ((dNeg : SL(3, K)) : SL(3, K)).1 =
      ((dNeg : SL(3, K)) : SL(3, K)).1 * A :=
    commute_dNeg_of_proj h2 A hcx'
  obtain ⟨h02, h12, h20, h21⟩ := entries_of_commute_dNeg h2 hA3
  have hcy' : proj 3 K (slConjugation 3 K A (oddDiag₂SL (K := K))) =
      proj 3 K (oddDiag₂SL (K := K)) := by
    have h := hcy
    rw [stdY] at h
    simpa only [conjAut_proj] using h
  obtain ⟨c, hc3, hrel⟩ := conj_scalar_relation A hcy'
  have hAAinv : (A : Matrix (Fin 3) (Fin 3) K) *
      ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hA22 : (A : Matrix (Fin 3) (Fin 3) K) 2 2 ≠ 0 := by
    have h22 := congrFun (congrFun hAAinv 2) 2
    simp only [Matrix.mul_apply, Fin.sum_univ_three, h20, h21, zero_mul, zero_add,
      Matrix.one_apply_eq] at h22
    intro h0
    rw [h0, zero_mul] at h22
    exact zero_ne_one h22
  have hc1 : c = 1 := by
    have h22 := congrFun (congrFun hrel 2) 2
    simp [Matrix.mul_apply, Fin.sum_univ_three, h20, h21, Matrix.scalar_apply,
      coe_oddDiag₂SL, Matrix.diagonal] at h22
    have h1 : (A : Matrix (Fin 3) (Fin 3) K) 2 2 * 1 =
        (A : Matrix (Fin 3) (Fin 3) K) 2 2 * c := by simpa using h22
    exact (mul_left_cancel₀ hA22 h1).symm
  have hA2 : (oddDiag₂SL (K := K) : Matrix (Fin 3) (Fin 3) K) * A =
      (A : Matrix (Fin 3) (Fin 3) K) * oddDiag₂SL (K := K) := by
    rw [hc1] at hrel
    simpa using hrel
  have h01 : (A : Matrix (Fin 3) (Fin 3) K) 0 1 = 0 := by
    have h := congrFun (congrFun hA2 0) 1
    simp only [Matrix.mul_apply, Fin.sum_univ_three, h02, h12, h20, h21, zero_mul,
      zero_add, coe_oddDiag₂SL, Matrix.of_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.tail_cons] at h
    have h' : (2 : K) * (A : Matrix (Fin 3) (Fin 3) K) 0 1 = 0 := by
      linear_combination -h
    exact (mul_eq_zero.mp h').resolve_left h2
  have h10 : (A : Matrix (Fin 3) (Fin 3) K) 1 0 = 0 := by
    have h := congrFun (congrFun hA2 1) 0
    simp only [Matrix.mul_apply, Fin.sum_univ_three, h02, h12, h20, h21, zero_mul,
      zero_add, coe_oddDiag₂SL, Matrix.of_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.tail_cons] at h
    have h' : (2 : K) * (A : Matrix (Fin 3) (Fin 3) K) 1 0 = 0 := by
      linear_combination h
    exact (mul_eq_zero.mp h').resolve_left h2
  have hdiag : (A : Matrix (Fin 3) (Fin 3) K) =
      diagonal ![(A : Matrix (Fin 3) (Fin 3) K) 0 0,
        (A : Matrix (Fin 3) (Fin 3) K) 1 1, (A : Matrix (Fin 3) (Fin 3) K) 2 2] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [h01, h10, h02, h12, h20, h21, Matrix.diagonal]
  have hA00 : (A : Matrix (Fin 3) (Fin 3) K) 0 0 ≠ 0 := by
    have h00 := congrFun (congrFun hAAinv 0) 0
    simp only [Matrix.mul_apply, Fin.sum_univ_three, h01, h02, zero_mul, zero_add,
      Matrix.one_apply_eq] at h00
    intro h0
    rw [h0, zero_mul] at h00
    norm_num at h00
  exact ⟨A, σ, ε, _, _, _, hε, hα, hdiag, hA00, hA22⟩

private noncomputable def d0Proj : Kˣ →* projectiveSL 3 K :=
  (proj 3 K).comp (d0Hom (K := K))

private noncomputable def d0Aut : Kˣ →* MulAut (projectiveSL 3 K) :=
  MulAut.conj.comp (d0Proj (K := K))

private noncomputable def d0Orbit (P : Subgroup (projectiveSL 3 K)) :
    Set (Subgroup (projectiveSL 3 K)) :=
  {Q | ∃ δ : Kˣ, Q = P.map (d0Aut (K := K) δ).toMonoidHom}

private theorem d0Proj_neg_one : d0Proj (K := K) (-1) = stdX (K := K) := by
  rw [d0Proj, MonoidHom.comp_apply, stdX]
  congr 1
  apply Subtype.ext
  rw [coe_d0Hom, coe_oddDiag₃SL]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

private theorem stdX_conj_symTorusHom (h2 : (2 : K) ≠ 0) (lam : Kˣ) :
    stdX (K := K) * symTorusHom (K := K) h2 lam * stdX (K := K) =
      (symTorusHom (K := K) h2 lam)⁻¹ := by
  have h := congrArg (proj 3 K) (oddDiag₃SL_conj_symTorusMat (K := K) h2 lam)
  rw [map_mul, map_mul, map_inv] at h
  simpa [stdX, symTorusHom_apply] using h

private theorem stdY_conj_symTorusHom (h2 : (2 : K) ≠ 0) (lam : Kˣ) :
    stdY (K := K) * symTorusHom (K := K) h2 lam * stdY (K := K) =
      symTorusHom (K := K) h2 lam := by
  have h := congrArg (proj 3 K) (oddDiag₂SL_conj_symTorusMat (K := K) h2 lam)
  rw [map_mul, map_mul] at h
  simpa [stdY, symTorusHom_apply] using h

private theorem stdX_inv_symTorusHom (h2 : (2 : K) ≠ 0) (lam : Kˣ) :
    stdX (K := K) * symTorusHom (K := K) h2 lam * (stdX (K := K))⁻¹ =
      (symTorusHom (K := K) h2 lam)⁻¹ := by
  rw [inv_eq_of_mul_eq_one_right (stdX_mul_self (K := K))]
  exact stdX_conj_symTorusHom h2 lam

private theorem stdY_comm_symTorusHom (h2 : (2 : K) ≠ 0) (lam : Kˣ) :
    stdY (K := K) * symTorusHom (K := K) h2 lam * (stdY (K := K))⁻¹ =
      symTorusHom (K := K) h2 lam := by
  rw [inv_eq_of_mul_eq_one_right (stdY_mul_self (K := K))]
  exact stdY_conj_symTorusHom h2 lam

private theorem exists_odd_torus_data (hq4 : Nat.card K % 4 = 3) (hq7 : 7 ≤ Nat.card K) :
    ∃ (r : ℕ) (Hr : Subgroup Kˣ),
      r.Prime ∧ Odd r ∧ Nat.card Hr = r ∧
      ∀ (φ : Kˣ →* Kˣ), Function.Injective φ → Hr.map φ = Hr := by
  classical
  have hq_eq : Nat.card K = 4 * (Nat.card K / 4) + 3 := by
    have h := Nat.div_add_mod (Nat.card K) 4
    omega
  have h2dvd : 2 ∣ Nat.card K - 1 := by omega
  let m : ℕ := (Nat.card K - 1) / 2
  have hm_gt : 1 < m := by omega
  have hm_odd : Odd m := by
    rw [show m = 2 * (Nat.card K / 4) + 1 by omega]
    exact ⟨Nat.card K / 4, by ring⟩
  obtain ⟨r, hrprime, hrm⟩ := Nat.exists_prime_and_dvd (show m ≠ 1 by omega)
  have hrodd : Odd r := hm_odd.of_dvd_nat hrm
  have hrdvd : r ∣ Nat.card K - 1 := hrm.trans (Nat.div_dvd_of_dvd h2dvd)
  haveI : IsCyclic Kˣ := inferInstance
  obtain ⟨g, hg_ord⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Kˣ)
  have hordg : orderOf g = Nat.card K - 1 := by
    rw [hg_ord, Nat.card_units]
  let Hr : Subgroup Kˣ := Subgroup.zpowers (g ^ ((Nat.card K - 1) / r))
  have hHr : Nat.card Hr = r := by
    change Nat.card (Subgroup.zpowers (g ^ ((Nat.card K - 1) / r))) = r
    rw [Nat.card_zpowers]
    rw [show (Nat.card K - 1) / r = orderOf g / r by rw [hordg]]
    exact orderOf_pow_orderOf_div (by rw [hordg]; omega) (by rwa [hordg])
  refine ⟨r, Hr, hrprime, hrodd, hHr, fun φ hφ => ?_⟩
  exact (IsCyclic.subgroup_eq_iff_card_eq).mpr (Subgroup.card_map_of_injective hφ)

private noncomputable def torusSubgroup (h2 : (2 : K) ≠ 0) (Hr : Subgroup Kˣ) :
    Subgroup (projectiveSL 3 K) :=
  Hr.map (symTorusHom (K := K) h2)

private theorem card_torusSubgroup (h2 : (2 : K) ≠ 0) (Hr : Subgroup Kˣ) :
    Nat.card (torusSubgroup (K := K) h2 Hr) = Nat.card Hr :=
  Subgroup.card_map_of_injective (symTorusHom_injective h2)

private theorem not_two_dvd_index_zpowers_neg_one (hq4 : Nat.card K % 4 = 3) :
    ¬ 2 ∣ (Subgroup.zpowers (-1 : Kˣ)).index := by
  have hq_eq : Nat.card K = 4 * (Nat.card K / 4) + 3 := by
    have h := Nat.div_add_mod (Nat.card K) 4
    omega
  have hcard_neg : Nat.card (Subgroup.zpowers (-1 : Kˣ)) = 2 := by
    rw [Nat.card_zpowers]
    haveI : Fintype K := Fintype.ofFinite K
    have hchar : ringChar K ≠ 2 := by
      intro h
      have h2 : Fintype.card K % 2 = 0 := (FiniteField.even_card_iff_char_two).mp h
      rw [← Nat.card_eq_fintype_card, hq_eq] at h2
      omega
    rw [← orderOf_injective (Units.coeHom K) Units.val_injective (-1 : Kˣ)]
    simp only [Units.coeHom_apply, Units.coe_neg_one]
    rw [orderOf_neg_one, if_neg hchar]
  have h := Subgroup.index_mul_card (Subgroup.zpowers (-1 : Kˣ))
  rw [hcard_neg, Nat.card_units, hq_eq] at h
  have hidx : (Subgroup.zpowers (-1 : Kˣ)).index = 2 * (Nat.card K / 4) + 1 := by
    omega
  rw [hidx]
  omega

private theorem exists_sylow_two_units (hq4 : Nat.card K % 4 = 3) :
    ∃ S : Sylow 2 Kˣ, (S : Subgroup Kˣ) = Subgroup.zpowers (-1 : Kˣ) := by
  have hcard_neg : Nat.card (Subgroup.zpowers (-1 : Kˣ)) = 2 := by
    rw [Nat.card_zpowers]
    haveI : Fintype K := Fintype.ofFinite K
    have hq_eq : Nat.card K = 4 * (Nat.card K / 4) + 3 := by
      have h := Nat.div_add_mod (Nat.card K) 4
      omega
    have hchar : ringChar K ≠ 2 := by
      intro h
      have h2 : Fintype.card K % 2 = 0 := (FiniteField.even_card_iff_char_two).mp h
      rw [← Nat.card_eq_fintype_card, hq_eq] at h2
      omega
    rw [← orderOf_injective (Units.coeHom K) Units.val_injective (-1 : Kˣ)]
    simp only [Units.coeHom_apply, Units.coe_neg_one]
    rw [orderOf_neg_one, if_neg hchar]
  let S : Sylow 2 Kˣ :=
    (IsPGroup.of_card (show Nat.card (Subgroup.zpowers (-1 : Kˣ)) = 2 ^ 1 by
      rw [hcard_neg]; norm_num)).toSylow (not_two_dvd_index_zpowers_neg_one hq4)
  exact ⟨S, IsPGroup.toSylow_coe _ _⟩

private theorem odd_ncard_d0Orbit (h2 : (2 : K) ≠ 0) (hq4 : Nat.card K % 4 = 3)
    (hq7 : 7 ≤ Nat.card K) {r : ℕ} {Hr : Subgroup Kˣ} (hrprime : r.Prime)
    (hrodd : Odd r) (hHr : Nat.card Hr = r)
    (hHr_unique : ∀ (φ : Kˣ →* Kˣ), Function.Injective φ → Hr.map φ = Hr) :
    Odd (Nat.card (d0Orbit (K := K) (torusSubgroup (K := K) h2 Hr))) := by
  classical
  let P0 : Subgroup (projectiveSL 3 K) := torusSubgroup (K := K) h2 Hr
  let act : MulAction Kˣ (Subgroup (projectiveSL 3 K)) :=
    { smul := fun δ P => P.map (d0Aut (K := K) δ).toMonoidHom
      one_smul := fun P => by
        change P.map (d0Aut (K := K) 1).toMonoidHom = P
        rw [map_one]
        exact Subgroup.map_id P
      mul_smul := fun δ ε P => by
        change P.map (d0Aut (K := K) (δ * ε)).toMonoidHom =
          (P.map (d0Aut (K := K) ε).toMonoidHom).map (d0Aut (K := K) δ).toMonoidHom
        rw [map_mul, Subgroup.map_map]
        rfl }
  letI := act
  have horbit : MulAction.orbit Kˣ P0 = d0Orbit (K := K) P0 := by
    ext Q
    simp only [MulAction.mem_orbit_iff, d0Orbit, Set.mem_setOf_eq]
    constructor
    · rintro ⟨δ, hδ⟩
      exact ⟨δ, hδ.symm⟩
    · rintro ⟨δ, hδ⟩
      exact ⟨δ, hδ.symm⟩
  obtain ⟨S, hS⟩ := exists_sylow_two_units (K := K) hq4
  have hneg_fix : P0.map (d0Aut (K := K) (-1)).toMonoidHom = P0 := by
    have hx : d0Aut (K := K) (-1) = MulAut.conj (stdX (K := K)) := by
      rw [d0Aut, MonoidHom.comp_apply, d0Proj_neg_one]
    rw [hx]
    apply le_antisymm
    · rintro _ ⟨p, hp, rfl⟩
      have hp' : stdX * p * (stdX)⁻¹ = p⁻¹ := by
        obtain ⟨lam, hlam, rfl⟩ := hp
        exact stdX_inv_symTorusHom h2 lam
      change stdX * p * (stdX)⁻¹ ∈ P0
      rw [hp']
      exact Subgroup.inv_mem P0 hp
    · intro p hp
      refine ⟨p⁻¹, Subgroup.inv_mem P0 hp, ?_⟩
      change stdX * p⁻¹ * (stdX)⁻¹ = p
      obtain ⟨lam, hlam, rfl⟩ := hp
      rw [← map_inv]
      rw [stdX_inv_symTorusHom h2 lam⁻¹]
      simp
  have hle : (S : Subgroup Kˣ) ≤ MulAction.stabilizer Kˣ P0 := by
    rw [hS]
    refine Subgroup.zpowers_le.mpr ?_
    change (-1 : Kˣ) • P0 = P0
    exact hneg_fix
  have hfix : P0 ∈ MulAction.fixedPoints S (Subgroup (projectiveSL 3 K)) :=
    MulAction.mem_fixedPoints.mpr fun s => MulAction.mem_stabilizer_iff.mp (hle s.2)
  have hnotdvd :=
    FiveTransitive.SylowThreeFixedOrbits.odd_orbit_of_sylow_fixed P0 S hfix
  rw [horbit] at hnotdvd
  exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hnotdvd)

private noncomputable def entryUnitHom (σ : K ≃+* K) (ε : ℕ) : Kˣ →* Kˣ where
  toFun η := Units.mk0 (entryMap σ ε (η : K)) (entryMap_ne_zero σ ε η.ne_zero)
  map_one' := Units.ext (by simp [entryMap_one])
  map_mul' η θ := Units.ext (by simp [entryMap_mul])

private theorem entryUnitHom_injective (σ : K ≃+* K) (ε : ℕ) :
    Function.Injective (entryUnitHom (K := K) σ ε) := by
  intro η θ h
  apply Units.ext
  apply entryMap_injective σ ε
  exact congrArg (fun u : Kˣ => (u : K)) h

private theorem fieldAut_symTorusHom_entry (h2 : (2 : K) ≠ 0) (σ : K ≃+* K) (lam : Kˣ) :
    fieldAut 3 K σ (symTorusHom (K := K) h2 lam) =
      symTorusHom (K := K) h2 (entryUnitHom (K := K) σ 0 lam) := by
  rw [fieldAut_symTorusHom]
  congr 1
  apply Units.ext
  simp [entryUnitHom, entryMap]

private theorem fieldAut_dualAut_pow_symTorusHom (h2 : (2 : K) ≠ 0) (σ : K ≃+* K)
    {ε : ℕ} (hε : ε ≤ 1) (lam : Kˣ) :
    fieldAut 3 K σ ((dualAut 3 K ^ ε) (symTorusHom (K := K) h2 lam)) =
      symTorusHom (K := K) h2 (entryUnitHom (K := K) σ ε lam) := by
  interval_cases ε
  · rw [pow_zero, MulAut.one_apply]
    exact fieldAut_symTorusHom_entry h2 σ lam
  · rw [pow_one, dualAut_symTorusHom, fieldAut_symTorusHom]
    congr 1
    apply Units.ext
    simp [entryUnitHom, entryMap, map_inv]

private theorem fieldAut_dualAut_pow_d0Proj (σ : K ≃+* K) {ε : ℕ} (hε : ε ≤ 1) (η : Kˣ) :
    fieldAut 3 K σ ((dualAut 3 K ^ ε) (d0Proj (K := K) η)) =
      d0Proj (K := K) (entryUnitHom (K := K) σ ε η) := by
  interval_cases ε
  · rw [pow_zero, MulAut.one_apply]
    change fieldAut 3 K σ (proj 3 K (d0Hom (K := K) η)) =
      proj 3 K (d0Hom (K := K) (entryUnitHom (K := K) σ 0 η))
    rw [fieldAut_d0Hom]
    congr 1
    congr 1
    apply Units.ext
    simp [entryUnitHom, entryMap]
  · rw [pow_one]
    change fieldAut 3 K σ (dualAut 3 K (proj 3 K (d0Hom (K := K) η))) =
      proj 3 K (d0Hom (K := K) (entryUnitHom (K := K) σ 1 η))
    rw [dualAut_d0Hom]
    change fieldAut 3 K σ (proj 3 K (d0Hom (K := K) (η⁻¹))) =
      proj 3 K (d0Hom (K := K) (entryUnitHom (K := K) σ 1 η))
    rw [fieldAut_d0Hom]
    congr 1
    congr 1
    apply Units.ext
    simp [entryUnitHom, entryMap, map_inv]

private theorem conjAut_symTorusHom_of_diagonal (h2 : (2 : K) ≠ 0) {A : GL (Fin 3) K}
    {a0 a1 a2 : K} (hA : (A : Matrix (Fin 3) (Fin 3) K) = diagonal ![a0, a1, a2])
    (ha0 : a0 ≠ 0) (ha2 : a2 ≠ 0) (lam : Kˣ) :
    let δ : Kˣ := Units.mk0 (a0 / a2) (div_ne_zero ha0 ha2)
    conjAut 3 K A (symTorusHom (K := K) h2 lam) =
      d0Proj (K := K) δ * symTorusHom (K := K) h2 lam * (d0Proj (K := K) δ)⁻¹ := by
  intro δ
  rw [symTorusHom_apply, conjAut_proj]
  rw [slConjugation_symTorusMat_of_diagonal h2 hA ha0 ha2 lam]
  rw [map_mul, map_mul, map_inv]
  rfl

private theorem conjAut_mul_fieldAut_mul_dualAut_pow_symTorusHom (h2 : (2 : K) ≠ 0)
    {A : GL (Fin 3) K} {σ : K ≃+* K} {ε : ℕ} (hε : ε ≤ 1) {a0 a1 a2 : K}
    (hA : (A : Matrix (Fin 3) (Fin 3) K) = diagonal ![a0, a1, a2]) (ha0 : a0 ≠ 0)
    (ha2 : a2 ≠ 0) (lam : Kˣ) :
    let δ : Kˣ := Units.mk0 (a0 / a2) (div_ne_zero ha0 ha2)
    (conjAut 3 K A * fieldAut 3 K σ * dualAut 3 K ^ ε) (symTorusHom (K := K) h2 lam) =
      d0Proj (K := K) δ * symTorusHom (K := K) h2 (entryUnitHom (K := K) σ ε lam) *
        (d0Proj (K := K) δ)⁻¹ := by
  intro δ
  rw [MulAut.mul_apply, MulAut.mul_apply,
    fieldAut_dualAut_pow_symTorusHom h2 σ hε lam,
    conjAut_symTorusHom_of_diagonal h2 hA ha0 ha2]

private theorem conjAut_mul_fieldAut_mul_dualAut_pow_d0Proj {A : GL (Fin 3) K} {σ : K ≃+* K}
    {ε : ℕ} (hε : ε ≤ 1) {a0 a1 a2 : K}
    (hA : (A : Matrix (Fin 3) (Fin 3) K) = diagonal ![a0, a1, a2]) (η : Kˣ) :
    (conjAut 3 K A * fieldAut 3 K σ * dualAut 3 K ^ ε) (d0Proj (K := K) η) =
      d0Proj (K := K) (entryUnitHom (K := K) σ ε η) := by
  rw [MulAut.mul_apply, MulAut.mul_apply,
    fieldAut_dualAut_pow_d0Proj σ hε η]
  change conjAut 3 K A (proj 3 K (d0Hom (K := K) (entryUnitHom (K := K) σ ε η))) =
    proj 3 K (d0Hom (K := K) (entryUnitHom (K := K) σ ε η))
  exact conjAut_d0Hom_of_diagonal hA (entryUnitHom (K := K) σ ε η)

private theorem d0Orbit_invariant_of_fixes (h2 : (2 : K) ≠ 0) {r : ℕ} {Hr : Subgroup Kˣ}
    (hHr : Nat.card Hr = r)
    (hHr_unique : ∀ (φ : Kˣ →* Kˣ), Function.Injective φ → Hr.map φ = Hr)
    (α : MulAut (projectiveSL 3 K)) (hαx : α (stdX (K := K)) = stdX (K := K))
    (hαy : α (stdY (K := K)) = stdY (K := K)) :
    ∀ P ∈ d0Orbit (K := K) (torusSubgroup (K := K) h2 Hr),
      P.map α.toMonoidHom ∈ d0Orbit (K := K) (torusSubgroup (K := K) h2 Hr) := by
  intro P hP
  obtain ⟨A, σ, ε, a0, a1, a2, hε, hα, hA, ha0, ha2⟩ :=
    exists_diagonal_form_of_fixes h2 α hαx hαy
  let δ : Kˣ := Units.mk0 (a0 / a2) (div_ne_zero ha0 ha2)
  let φ : Kˣ →* Kˣ := entryUnitHom (K := K) σ ε
  have hφHr : Hr.map φ = Hr := hHr_unique φ (entryUnitHom_injective σ ε)
  have hαR : ∀ lam : Kˣ, α (symTorusHom (K := K) h2 lam) =
      d0Proj (K := K) δ * symTorusHom (K := K) h2 (φ lam) * (d0Proj (K := K) δ)⁻¹ := by
    intro lam
    rw [hα]
    exact conjAut_mul_fieldAut_mul_dualAut_pow_symTorusHom h2 hε hA ha0 ha2 lam
  have hαd0 : ∀ η : Kˣ, α (d0Proj (K := K) η) = d0Proj (K := K) (φ η) := by
    intro η
    rw [hα]
    exact conjAut_mul_fieldAut_mul_dualAut_pow_d0Proj hε hA η
  obtain ⟨η, rfl⟩ := hP
  have hcomp : (α.toMonoidHom.comp (d0Aut (K := K) η).toMonoidHom).comp
        (symTorusHom (K := K) h2) =
      (d0Aut (K := K) (φ η * δ)).toMonoidHom.comp
        ((symTorusHom (K := K) h2).comp φ) := by
    ext lam
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [show (d0Aut (K := K) η) (symTorusHom (K := K) h2 lam) =
        d0Proj (K := K) η * symTorusHom (K := K) h2 lam * (d0Proj (K := K) η)⁻¹ by
      rw [d0Aut, MonoidHom.comp_apply, MulAut.conj_apply]]
    rw [map_mul, map_mul, map_inv, hαd0, hαR]
    rw [show (d0Aut (K := K) (φ η * δ)) (symTorusHom (K := K) h2 (φ lam)) =
        d0Proj (K := K) (φ η * δ) * symTorusHom (K := K) h2 (φ lam) *
          (d0Proj (K := K) (φ η * δ))⁻¹ by
      rw [d0Aut, MonoidHom.comp_apply, MulAut.conj_apply]]
    rw [map_mul]
    group
  refine ⟨φ η * δ, ?_⟩
  calc
    ((torusSubgroup (K := K) h2 Hr).map (d0Aut (K := K) η).toMonoidHom).map
        α.toMonoidHom
        = (torusSubgroup (K := K) h2 Hr).map
            (α.toMonoidHom.comp (d0Aut (K := K) η).toMonoidHom) := by
          rw [Subgroup.map_map]
    _ = (Hr.map (symTorusHom (K := K) h2)).map
            (α.toMonoidHom.comp (d0Aut (K := K) η).toMonoidHom) := rfl
    _ = Hr.map ((α.toMonoidHom.comp (d0Aut (K := K) η).toMonoidHom).comp
            (symTorusHom (K := K) h2)) := by rw [Subgroup.map_map]
    _ = Hr.map ((d0Aut (K := K) (φ η * δ)).toMonoidHom.comp
            ((symTorusHom (K := K) h2).comp φ)) := by rw [hcomp]
    _ = Hr.map ((d0Aut (K := K) (φ η * δ)).toMonoidHom.comp
            (symTorusHom (K := K) h2)) := by
          rw [← Subgroup.map_map, ← Subgroup.map_map, hφHr, Subgroup.map_map]
    _ = (Hr.map (symTorusHom (K := K) h2)).map
            (d0Aut (K := K) (φ η * δ)).toMonoidHom := by
          rw [← Subgroup.map_map]
    _ = (torusSubgroup (K := K) h2 Hr).map
            (d0Aut (K := K) (φ η * δ)).toMonoidHom := rfl

private theorem card_of_mem_d0Orbit (h2 : (2 : K) ≠ 0) {Hr : Subgroup Kˣ}
    {P : Subgroup (projectiveSL 3 K)}
    (hP : P ∈ d0Orbit (K := K) (torusSubgroup (K := K) h2 Hr)) :
    Nat.card P = Nat.card Hr := by
  obtain ⟨η, rfl⟩ := hP
  rw [Subgroup.card_map_of_injective (d0Aut (K := K) η).injective,
    card_torusSubgroup]

private theorem stdX_comm_d0Proj (η : Kˣ) :
    stdX (K := K) * d0Proj (K := K) η = d0Proj (K := K) η * stdX (K := K) := by
  change proj 3 K (oddDiag₃SL (K := K)) * proj 3 K (d0Hom (K := K) η) =
    proj 3 K (d0Hom (K := K) η) * proj 3 K (oddDiag₃SL (K := K))
  rw [← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    coe_oddDiag₃SL, coe_d0Hom]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

private theorem stdY_comm_d0Proj (η : Kˣ) :
    stdY (K := K) * d0Proj (K := K) η = d0Proj (K := K) η * stdY (K := K) := by
  change proj 3 K (oddDiag₂SL (K := K)) * proj 3 K (d0Hom (K := K) η) =
    proj 3 K (d0Hom (K := K) η) * proj 3 K (oddDiag₂SL (K := K))
  rw [← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    coe_oddDiag₂SL, coe_d0Hom]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

private theorem stdX_inv_torusSubgroup (h2 : (2 : K) ≠ 0) {Hr : Subgroup Kˣ}
    {p : projectiveSL 3 K} (hp : p ∈ torusSubgroup (K := K) h2 Hr) :
    stdX (K := K) * p * (stdX (K := K))⁻¹ = p⁻¹ := by
  obtain ⟨lam, hlam, rfl⟩ := hp
  exact stdX_inv_symTorusHom h2 lam

private theorem stdY_comm_torusSubgroup (h2 : (2 : K) ≠ 0) {Hr : Subgroup Kˣ}
    {p : projectiveSL 3 K} (hp : p ∈ torusSubgroup (K := K) h2 Hr) :
    stdY (K := K) * p * (stdY (K := K))⁻¹ = p := by
  obtain ⟨lam, hlam, rfl⟩ := hp
  exact stdY_comm_symTorusHom h2 lam

private theorem stdX_inv_of_mem_d0Orbit (h2 : (2 : K) ≠ 0) {Hr : Subgroup Kˣ}
    {P : Subgroup (projectiveSL 3 K)}
    (hP : P ∈ d0Orbit (K := K) (torusSubgroup (K := K) h2 Hr)) :
    ∀ p ∈ P, stdX (K := K) * p * (stdX (K := K))⁻¹ = p⁻¹ := by
  obtain ⟨η, rfl⟩ := hP
  intro p hp
  obtain ⟨p0, hp0, rfl⟩ := hp
  have hη : stdX (K := K) * d0Proj (K := K) η * (stdX (K := K))⁻¹ =
      d0Proj (K := K) η := by
    rw [stdX_comm_d0Proj]
    group
  calc
    stdX (K := K) * (d0Proj (K := K) η * p0 * (d0Proj (K := K) η)⁻¹) *
        (stdX (K := K))⁻¹
        = (stdX (K := K) * d0Proj (K := K) η * (stdX (K := K))⁻¹) *
            (stdX (K := K) * p0 * (stdX (K := K))⁻¹) *
            (stdX (K := K) * d0Proj (K := K) η * (stdX (K := K))⁻¹)⁻¹ := by
          group
    _ = d0Proj (K := K) η * p0⁻¹ * (d0Proj (K := K) η)⁻¹ := by
          rw [hη, stdX_inv_torusSubgroup h2 hp0]
    _ = (d0Proj (K := K) η * p0 * (d0Proj (K := K) η)⁻¹)⁻¹ := by group

private theorem stdY_comm_of_mem_d0Orbit (h2 : (2 : K) ≠ 0) {Hr : Subgroup Kˣ}
    {P : Subgroup (projectiveSL 3 K)}
    (hP : P ∈ d0Orbit (K := K) (torusSubgroup (K := K) h2 Hr)) :
    ∀ p ∈ P, stdY (K := K) * p * (stdY (K := K))⁻¹ = p := by
  obtain ⟨η, rfl⟩ := hP
  intro p hp
  obtain ⟨p0, hp0, rfl⟩ := hp
  have hη : stdY (K := K) * d0Proj (K := K) η * (stdY (K := K))⁻¹ =
      d0Proj (K := K) η := by
    rw [stdY_comm_d0Proj]
    group
  calc
    stdY (K := K) * (d0Proj (K := K) η * p0 * (d0Proj (K := K) η)⁻¹) *
        (stdY (K := K))⁻¹
        = (stdY (K := K) * d0Proj (K := K) η * (stdY (K := K))⁻¹) *
            (stdY (K := K) * p0 * (stdY (K := K))⁻¹) *
            (stdY (K := K) * d0Proj (K := K) η * (stdY (K := K))⁻¹)⁻¹ := by
          group
    _ = d0Proj (K := K) η * p0 * (d0Proj (K := K) η)⁻¹ := by
          rw [hη, stdY_comm_torusSubgroup h2 hp0]
    _ = d0Proj (K := K) η * p0 * (d0Proj (K := K) η)⁻¹ := rfl

private theorem not_le_centralizer_stdX_of_mem_d0Orbit (h2 : (2 : K) ≠ 0) {r : ℕ}
    {Hr : Subgroup Kˣ} (hrprime : r.Prime) (hrodd : Odd r) (hHr : Nat.card Hr = r)
    {P : Subgroup (projectiveSL 3 K)}
    (hP : P ∈ d0Orbit (K := K) (torusSubgroup (K := K) h2 Hr)) :
    ¬ P ≤ Subgroup.centralizer ({stdX (K := K)} : Set (projectiveSL 3 K)) := by
  intro hle
  have hcard : Nat.card P = r := by
    rw [card_of_mem_d0Orbit h2 hP, hHr]
  have hPne : P ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hcard
    exact hrprime.ne_one hcard.symm
  obtain ⟨p, hp1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hPne
  let pval : projectiveSL 3 K := (p : projectiveSL 3 K)
  have hpP : pval ∈ P := p.2
  have hp1' : pval ≠ 1 := fun h => hp1 (Subtype.ext h)
  have hcentral' : pval * stdX (K := K) = stdX (K := K) * pval :=
    Subgroup.mem_centralizer_singleton_iff.mp (hle hpP)
  have hcentral : stdX (K := K) * pval * (stdX (K := K))⁻¹ = pval := by
    rw [← hcentral']
    group
  have hinv : stdX (K := K) * pval * (stdX (K := K))⁻¹ = pval⁻¹ :=
    stdX_inv_of_mem_d0Orbit h2 hP pval hpP
  have hsq : pval * pval = 1 := by
    have hp_eq : pval = pval⁻¹ := hcentral.symm.trans hinv
    nth_rewrite 1 [hp_eq]
    exact inv_mul_cancel pval
  have hdvd : orderOf pval ∣ r := by
    rw [← hcard]
    exact Subgroup.orderOf_dvd_natCard P hpP
  have hord : orderOf pval = r := by
    have hd : orderOf pval = 1 ∨ orderOf pval = r := (Nat.dvd_prime hrprime).mp hdvd
    cases hd with
    | inl h1 => exact absurd (orderOf_eq_one_iff.mp h1) hp1'
    | inr hr => exact hr
  have hdvd2 : orderOf pval ∣ 2 := orderOf_dvd_of_pow_eq_one (by rwa [pow_two])
  have hr2 : r ∣ 2 := by rwa [hord] at hdvd2
  have hr_ne_two : r ≠ 2 := by
    have := Nat.odd_iff.mp hrodd
    omega
  rcases (Nat.dvd_prime Nat.prime_two).mp hr2 with h1 | h2
  · exact hrprime.ne_one h1
  · exact hr_ne_two h2

private theorem two_ne_zero_of_natCard_mod_four (hq4 : Nat.card K % 4 = 3) : (2 : K) ≠ 0 := by
  haveI : Fintype K := Fintype.ofFinite K
  exact CFSG.ComponentClassification.CatFactsL4U4.StabL.two_ne_zero_of_card_mod_four (by
    rwa [Nat.card_eq_fintype_card] at hq4)

private theorem projectiveSLMulEquivStatedProj_mk (g : SpecialLinearGroup (Fin 3) K) :
    CFSG.CGT.Timmesfeld75.projectiveSLMulEquivStatedProj 3 K (proj 3 K g) =
      statedProjMk (StatedSL 3 K) (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 K g) := by
  rw [CFSG.CGT.Timmesfeld75.projectiveSLMulEquivStatedProj, MulEquiv.trans_apply]
  have h1 : (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 K).symm
      (proj 3 K g) =
      (QuotientGroup.mk g : ProjectiveSpecialLinearGroup (Fin 3) K) := by
    apply (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 K).injective
    rw [MulEquiv.apply_symm_apply]
    rw [CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL]
    rfl
  rw [h1]
  rw [CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj]
  simp only [QuotientGroup.congr, Quotient.congr_mk]
  rfl

private theorem projectiveSLMulEquivStatedProj_stdX :
    CFSG.CGT.Timmesfeld75.projectiveSLMulEquivStatedProj 3 K (stdX (K := K)) =
      CFSG.GH74.GLS.IVK.Proofs2.linU₀ (F := K) := by
  rw [stdX, projectiveSLMulEquivStatedProj_mk]
  rw [CFSG.GH74.GLS.IVK.Proofs2.linU₀]
  congr 1
  apply Subtype.ext
  apply Units.ext
  rw [CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL_coe]
  rfl

private theorem projectiveSLMulEquivStatedProj_stdY :
    CFSG.CGT.Timmesfeld75.projectiveSLMulEquivStatedProj 3 K (stdY (K := K)) =
      CFSG.GH74.GLS.IVK.Proofs2.linU₀' (F := K) := by
  rw [stdY, projectiveSLMulEquivStatedProj_mk]
  rw [CFSG.GH74.GLS.IVK.Proofs2.linU₀']
  congr 1
  apply Subtype.ext
  apply Units.ext
  rw [CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL_coe]
  rfl

private theorem exists_inner_torus_standard (h2 : (2 : K) ≠ 0) (hq4 : Nat.card K % 4 = 3)
    (hq7 : 7 ≤ Nat.card K) {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hLn : L.Normal) (e : L ≃* projectiveSL 3 K) {x y : G} (hxL : x ∈ L) (hyL : y ∈ L)
    (hx_std : e ⟨x, hxL⟩ = stdX (K := K)) (hy_std : e ⟨y, hyL⟩ = stdY (K := K))
    (Q : Subgroup G) (hQ : IsPGroup 2 Q)
    (hQle : Q ≤ Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer ({y} : Set G)) :
    ∃ P : Subgroup G, P ≤ L ∧ (Nat.card P).Prime ∧ Nat.card P ≠ 2 ∧
      Q ≤ Subgroup.normalizer (P : Set G) ∧
      ¬ P ≤ Subgroup.centralizer ({x} : Set G) ∧
      P ≤ Subgroup.centralizer ({y} : Set G) := by
  classical
  obtain ⟨r, Hr, hrprime, hrodd, hHr, hHr_unique⟩ := exists_odd_torus_data (K := K) hq4 hq7
  let Ω : Set (Subgroup (projectiveSL 3 K)) := d0Orbit (K := K) (torusSubgroup (K := K) h2 Hr)
  have hfin : Ω.Finite := Set.finite_univ.subset (Set.subset_univ Ω)
  have hodd : Odd Ω.ncard := by
    have h := odd_ncard_d0Orbit h2 hq4 hq7 hrprime hrodd hHr hHr_unique
    rwa [Nat.card_coe_set_eq] at h
  have hβx : ∀ q ∈ Q, MulAut.congr e (MulAut.conjNormal (H := L) q) (stdX (K := K)) =
      stdX (K := K) := by
    intro q hq
    rw [← hx_std]
    rw [show MulAut.congr e (MulAut.conjNormal (H := L) q) (e ⟨x, hxL⟩) =
        e (MulAut.conjNormal (H := L) q ⟨x, hxL⟩) by
      simp [MulAut.congr_apply]]
    congr 1
    apply Subtype.ext
    rw [MulAut.conjNormal_apply]
    have hqcx : q * x = x * q := Subgroup.mem_centralizer_singleton_iff.mp (hQle hq).1
    change q * x * q⁻¹ = x
    calc
      q * x * q⁻¹ = x * q * q⁻¹ := by rw [hqcx]
      _ = x := by group
  have hβy : ∀ q ∈ Q, MulAut.congr e (MulAut.conjNormal (H := L) q) (stdY (K := K)) =
      stdY (K := K) := by
    intro q hq
    rw [← hy_std]
    rw [show MulAut.congr e (MulAut.conjNormal (H := L) q) (e ⟨y, hyL⟩) =
        e (MulAut.conjNormal (H := L) q ⟨y, hyL⟩) by
      simp [MulAut.congr_apply]]
    congr 1
    apply Subtype.ext
    rw [MulAut.conjNormal_apply]
    have hqcy : q * y = y * q := Subgroup.mem_centralizer_singleton_iff.mp (hQle hq).2
    change q * y * q⁻¹ = y
    calc
      q * y * q⁻¹ = y * q * q⁻¹ := by rw [hqcy]
      _ = y := by group
  have hinv : ∀ q ∈ Q, ∀ P ∈ Ω,
      P.map (MulAut.congr e (MulAut.conjNormal (H := L) q)).toMonoidHom ∈ Ω := by
    intro q hq P hP
    exact d0Orbit_invariant_of_fixes h2 hHr hHr_unique _ (hβx q hq) (hβy q hq) P hP
  obtain ⟨P, hPΩ, hPN⟩ := exists_le_normalizer_of_odd_ncard e Q hQ Ω hfin hodd hinv
  let PG : Subgroup G := P.map (L.subtype.comp e.symm.toMonoidHom)
  have hPG_le : PG ≤ L := by
    intro pg hpg
    obtain ⟨p, hp, rfl⟩ := hpg
    exact (e.symm p).2
  have hmap_inj : Function.Injective (L.subtype.comp e.symm.toMonoidHom) :=
    L.subtype_injective.comp e.symm.injective
  have hcardPG : Nat.card PG = r := by
    rw [Subgroup.card_map_of_injective hmap_inj, card_of_mem_d0Orbit h2 hPΩ, hHr]
  have hPG_prime : (Nat.card PG).Prime := by
    rw [hcardPG]
    exact hrprime
  have hPG_ne_two : Nat.card PG ≠ 2 := by
    rw [hcardPG]
    have h := Nat.odd_iff.mp hrodd
    omega
  have hPG_not_central_x : ¬ PG ≤ Subgroup.centralizer ({x} : Set G) := by
    intro hle
    have hcent : P ≤ Subgroup.centralizer ({stdX (K := K)} : Set (projectiveSL 3 K)) := by
      intro p hp
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hpG : (e.symm p : G) ∈ PG := ⟨p, hp, rfl⟩
      have hcommG : (e.symm p : G) * x = x * (e.symm p : G) :=
        Subgroup.mem_centralizer_singleton_iff.mp (hle hpG)
      have hcommL : e.symm p * ⟨x, hxL⟩ = ⟨x, hxL⟩ * e.symm p := by
        apply Subtype.ext
        simpa using hcommG
      have hcommPSL := congrArg e hcommL
      simpa [hx_std] using hcommPSL
    exact not_le_centralizer_stdX_of_mem_d0Orbit h2 hrprime hrodd hHr hPΩ hcent
  have hPG_central_y : PG ≤ Subgroup.centralizer ({y} : Set G) := by
    intro pg hpg
    rw [Subgroup.mem_centralizer_singleton_iff]
    obtain ⟨p, hp, rfl⟩ := hpg
    have hpY : p * stdY (K := K) = stdY (K := K) * p := by
      have hcomm := stdY_comm_of_mem_d0Orbit h2 hPΩ p hp
      calc
        p * stdY (K := K) = (stdY (K := K) * p * (stdY (K := K))⁻¹) * stdY (K := K) := by
          rw [hcomm]
        _ = stdY (K := K) * p := by group
    have hcommL : e.symm p * ⟨y, hyL⟩ = ⟨y, hyL⟩ * e.symm p := by
      apply e.injective
      rw [map_mul, map_mul]
      simpa [hy_std] using hpY
    have hcommG : (e.symm p : G) * y = y * (e.symm p : G) := by
      simpa using congrArg Subtype.val hcommL
    exact hcommG
  exact ⟨PG, hPG_le, hPG_prime, hPG_ne_two, hPN, hPG_not_central_x, hPG_central_y⟩

theorem exists_inner_torus_of_psl3 (hq4 : Nat.card K % 4 = 3)
    (hq7 : 7 ≤ Nat.card K) {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hLn : L.Normal) (e : L ≃* projectiveSL 3 K) {x y : G} (hxL : x ∈ L) (hyL : y ∈ L)
    (hx2 : orderOf x = 2) (hy2 : orderOf y = 2) (hxy : x ≠ y) (hcomm : x * y = y * x)
    (Q : Subgroup G) (hQ : IsPGroup 2 Q)
    (hQle : Q ≤ Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer ({y} : Set G)) :
    ∃ P : Subgroup G, P ≤ L ∧ (Nat.card P).Prime ∧ Nat.card P ≠ 2 ∧
      Q ≤ Subgroup.normalizer (P : Set G) ∧
      ¬ P ≤ Subgroup.centralizer ({x} : Set G) ∧
      P ≤ Subgroup.centralizer ({y} : Set G) := by
  classical
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_natCard_mod_four hq4
  let Φ : projectiveSL 3 K ≃* StatedProj (StatedSL 3 K) :=
    CFSG.CGT.Timmesfeld75.projectiveSLMulEquivStatedProj 3 K
  let x0 : projectiveSL 3 K := e ⟨x, hxL⟩
  let y0 : projectiveSL 3 K := e ⟨y, hyL⟩
  have hq_eq : Nat.card K = 4 * (Nat.card K / 4) + 3 := by
    have h := Nat.div_add_mod (Nat.card K) 4
    omega
  have hoddK : Odd (Nat.card K) := by
    rw [hq_eq]
    exact ⟨2 * (Nat.card K / 4) + 1, by ring⟩
  have hordx0 : orderOf x0 = 2 := by
    have h1 : orderOf (⟨x, hxL⟩ : L) = orderOf x := by
      rw [← Subgroup.orderOf_coe]
    rw [show x0 = e ⟨x, hxL⟩ from rfl, MulEquiv.orderOf_eq, h1, hx2]
  have hordy0 : orderOf y0 = 2 := by
    have h1 : orderOf (⟨y, hyL⟩ : L) = orderOf y := by
      rw [← Subgroup.orderOf_coe]
    rw [show y0 = e ⟨y, hyL⟩ from rfl, MulEquiv.orderOf_eq, h1, hy2]
  have hne0 : x0 ≠ y0 := by
    intro h
    have h' : e ⟨x, hxL⟩ = e ⟨y, hyL⟩ := by simpa only [x0, y0] using h
    exact hxy (congrArg Subtype.val (e.injective h'))
  have hcomm0 : x0 * y0 = y0 * x0 := by
    have h1 : (⟨x, hxL⟩ : L) * ⟨y, hyL⟩ = ⟨y, hyL⟩ * ⟨x, hxL⟩ := by
      apply Subtype.ext
      exact hcomm
    simpa only [x0, y0, map_mul] using congrArg e h1
  obtain ⟨gS, hgSx, hgSy⟩ :=
    CFSG.GH74.GLS.IVK.Proofs2.linConj K hoddK (Φ x0) (Φ y0)
      (by rw [MulEquiv.orderOf_eq]; exact hordx0)
      (by rw [MulEquiv.orderOf_eq]; exact hordy0)
      (fun h => hne0 (Φ.injective h))
      (by simpa only [map_mul] using congrArg Φ hcomm0)
  let g : projectiveSL 3 K := Φ.symm gS
  have hΦg : Φ g = gS := Φ.apply_symm_apply gS
  have hgx : g * x0 * g⁻¹ = stdX (K := K) := by
    apply Φ.injective
    rw [map_mul, map_mul, map_inv, hΦg, hgSx]
    exact (projectiveSLMulEquivStatedProj_stdX (K := K)).symm
  have hgy : g * y0 * g⁻¹ = stdY (K := K) := by
    apply Φ.injective
    rw [map_mul, map_mul, map_inv, hΦg, hgSy]
    exact (projectiveSLMulEquivStatedProj_stdY (K := K)).symm
  let e' : L ≃* projectiveSL 3 K := e.trans (MulAut.conj g)
  have hx_std' : e' ⟨x, hxL⟩ = stdX (K := K) := by
    change (MulAut.conj g) (e ⟨x, hxL⟩) = stdX (K := K)
    rw [show e ⟨x, hxL⟩ = x0 from rfl, MulAut.conj_apply]
    exact hgx
  have hy_std' : e' ⟨y, hyL⟩ = stdY (K := K) := by
    change (MulAut.conj g) (e ⟨y, hyL⟩) = stdY (K := K)
    rw [show e ⟨y, hyL⟩ = y0 from rfl, MulAut.conj_apply]
    exact hgy
  exact exists_inner_torus_standard h2 hq4 hq7 hLn e' hxL hyL hx_std' hy_std' Q hQ hQle

end CFSG.LocalAnalysis.WeakClosure81

end
