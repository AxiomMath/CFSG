module

public import CFSG.LocalAnalysis.StandardType.GGKD2Leaf6D3Contracts
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitarySixThreeFieldAlg
public import CFSG.LocalAnalysis.StandardType.GGKD2Leaf6D3LinearCentralizer
public import CFSG.LocalAnalysis.StandardType.GGHermTools
public import CFSG.RankThree.PartOne.KC.UnitaryOrthonormalEigenbasis
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryTransvectionGeneration
public import CFSG.LocalAnalysis.StandardType.GGKD2Leaf6D3CubicBlock

public section

namespace S2MathAs3_1624

noncomputable section

open Polynomial Module Matrix
open CFSG CFSG.Assembly CFSG.StandardType
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCUnitary CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.RankThree.PartOne.KCUnitaryPlane

open scoped MatrixGroups BigOperators

private lemma ltrd3j4_toLinU_apply_mulVec {K : Type} [Field K] {n : ℕ}
    (h : UnitaryFieldData 2 n K) (d : ℕ) (A : primeFormUnitary h (idGram K d)) (v : Fin d → K) :
    ((toLinU h d A : LinearMap.GeneralLinearGroup K (Fin d → K)) : Module.End K (Fin d → K)) v =
      ((A : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *ᵥ v := rfl

private lemma ltrd3j4_toLinU_pow_apply {K : Type} [Field K] {n : ℕ}
    (h : UnitaryFieldData 2 n K) (d : ℕ) (A : primeFormUnitary h (idGram K d)) (k : ℕ)
    (v : Fin d → K) :
    (((toLinU h d A : LinearMap.GeneralLinearGroup K (Fin d → K)) :
      Module.End K (Fin d → K)) ^ k) v =
      (((A : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) ^ k) *ᵥ v := by
  induction k generalizing v with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Module.End.mul_apply, ih, ltrd3j4_toLinU_apply_mulVec, mulVec_mulVec,
      ← pow_succ]

theorem unitaryPrimaryBlock_holds : UnitaryPrimaryBlockContract := by
  intro K _ _ _ n h d hd M κ hnc hM3
  classical
  let : Nontrivial (Fin d → K) := by
    have hd0 : 0 < d := by omega
    refine ⟨Pi.single ⟨0, hd0⟩ (1 : K), 0, fun hcon => ?_⟩
    have h1 := congrFun hcon ⟨0, hd0⟩
    rw [Pi.single_eq_same, Pi.zero_apply] at h1
    exact one_ne_zero h1
  set x := toLinU h d M with hx
  have hc : ∀ c : K, c ^ 3 ≠ (κ : K) := fun c hcd => by
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [zero_pow (by norm_num)] at hcd
      exact κ.ne_zero hcd.symm
    exact hnc (Units.mk0 c hc0)
      (Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_mk0, hcd]))
  have hirr := CFSG.StandardType.TableBU63.irreducible_X_pow_three_sub_C hc
  have hx3 : (x : Module.End K (Fin d → K)) ^ 3 = algebraMap K _ (κ : K) := by
    refine LinearMap.ext fun v => ?_
    rw [hx, ltrd3j4_toLinU_pow_apply, ← Units.val_pow_eq_pow_val, hM3,
      GeneralLinearGroup.coe_scalar, Module.algebraMap_end_apply, Matrix.scalar_apply]
    funext i
    rw [Matrix.mulVec_diagonal]
    rfl
  have hPx : aeval (x : Module.End K (Fin d → K)) (X ^ 3 - C (κ : K)) = 0 := by
    rw [map_sub, map_pow, aeval_X, aeval_C, hx3, sub_self]
  have hmon : (X ^ 3 - C (κ : K) : K[X]).Monic := monic_X_pow_sub_C _ (by norm_num)
  have hmin : minpoly K (x : Module.End K (Fin d → K)) = X ^ 3 - C (κ : K) :=
    (minpoly.eq_of_irreducible_of_monic hirr hPx hmon).symm
  have H0 : UnitaryPrimaryData h.bar (idForm h d) x :=
    ⟨h.bar_bar, idForm_isSymm h d, idForm_separatingLeft h d, toLinU_mem M,
      hmin ▸ hirr.squarefree⟩
  have ha : (X ^ 3 - C (κ : K) : K[X]) ∈ primaryFactors (x : Module.End K (Fin d → K)) :=
    mem_primaryFactors.mpr ⟨hirr, hmon, hmin.symm ▸ dvd_rfl⟩
  have honly : ∀ b ∈ primaryFactors (x : Module.End K (Fin d → K)),
      b = X ^ 3 - C (κ : K) := by
    intro b hb
    obtain ⟨hbirr, hbmon, hbdvd⟩ := mem_primaryFactors.mp hb
    rw [hmin] at hbdvd
    exact eq_of_monic_of_associated hbmon hmon (hbirr.associated_of_dvd hirr hbdvd)
  obtain ⟨a, hac⟩ : ∃ a : primaryFactors (x : Module.End K (Fin d → K)),
      (a : K[X]) = X ^ 3 - C (κ : K) := ⟨⟨_, ha⟩, rfl⟩
  have hself : dualPoly h.bar (a : K[X]) = a := by
    rw [honly _ (dualPoly_mem_primaryFactors H0 a.2), hac]
  have htop : primaryComponent (x : Module.End K (Fin d → K)) (a : K[X]) = ⊤ := by
    rw [eq_top_iff]
    intro v _
    rw [mem_primaryComponent, hac, hPx, LinearMap.zero_apply]
  have hmult : d = 3 * primaryMultiplicity (x : Module.End K (Fin d → K)) (a : K[X]) := by
    have hfr := finrank_primaryComponent (x : Module.End K (Fin d → K)) (a : K[X])
    have hn' : Module.finrank K
        (primaryComponent (x : Module.End K (Fin d → K)) (a : K[X])) = d := by
      rw [htop, finrank_top, Module.finrank_fin_fun]
    have hdeg : (a : K[X]).natDegree = 3 := by rw [hac]; exact natDegree_X_pow_sub_C
    rw [hn', hdeg] at hfr
    exact hfr
  have hsq : Squarefree (minpoly K (x : Module.End K (Fin d → K))) := hmin ▸ hirr.squarefree
  have Hrec := r3e_unitary_semisimple_primary_algebra_and_full_centralizer h
    (idForm h d) (idForm_isSymm h d) (idForm_separatingLeft h d) x (toLinU_mem M) hsq
  exact ⟨a, hac, htop, hmult, Hrec.selfDual a hself,
    fun b => Subtype.ext ((honly b b.2).trans hac.symm)⟩

variable {K E V : Type} [Field K] [Field E] [Algebra K E]
  [Fintype K] [Fintype E] [FiniteDimensional K E]
  {f : ℕ} (hKdata : UnitaryFieldData 2 f K) (hEdata : UnitaryFieldData 2 (3 * f) E)

end

end S2MathAs3_1624

end
