module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeLinDefs
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeRLeaf
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.LinearInner
public import CFSG.CharacterTheory.Wreathed.BrauerWongTypes
public import CFSG.CharacterTheory.Wreathed.WreathCentralSquare
public import CFSG.ClassicalInvolution.Balance.LocalBalance.Faithful
public import CFSG.HardMathSupport.Solomon.Coordinator.B3FamPC
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma28
public import CFSG.HardMathSupport.Solomon.LocalBalance.Sec5Statements
public import CFSG.HardMathSupport.Timmesfeld.Proving.ExistsOrderPCentralizer
public import CFSG.HardMathSupport.Timmesfeld.Proving.GLAPrimeCoreCentralizer
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Defs
public import CFSG.LocalAnalysis.GLTheoremB.SchreierTools
public import CFSG.RankThree.PartOne.KC.LinearCommutantFactors

public section

namespace CFSG.StandardType.TablePThreeKG

open CFSG CFSG.Assembly
open Polynomial CFSG.RankThree.PartOne.KCPrimary CFSG.LocalAnalysis.ComponentInitial
open CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple CFSG.RankThree.CALinearPrimary

private lemma largeEvenSLGroup_conj_mem
    {K : Type} [Field K] {N : ℕ} (d : GL (Fin N) K)
    (k : ↥(LargeEvenSLGroup (Fin N) K)) :
    d * (k : GL (Fin N) K) * d⁻¹ ∈ LargeEvenSLGroup (Fin N) K :=
  (CFSG.StandardType.TableB.largeEvenSLGroup_normal (Fin N) K).conj_mem
    (k : GL (Fin N) K) k.2 d

private theorem scalar_eq_one_of_conj_transvection_gl
    {K : Type} [Field K] {n : ℕ} (u : GL (Fin n) K)
    (a b j : Fin n) (hab : a ≠ b) (hja : j ≠ a) (c s : K)
    (h : (u : Matrix (Fin n) (Fin n) K) * Matrix.transvection a b c *
          (((u⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) =
        Matrix.scalar (Fin n) s * Matrix.transvection a b c) :
    s = 1 := by
  have hUUi : (u : Matrix (Fin n) (Fin n) K) *
      ((u⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
    rw [← Matrix.GeneralLinearGroup.coe_mul, mul_inv_cancel, Matrix.GeneralLinearGroup.coe_one]
  have hUiU : ((u⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      (u : Matrix (Fin n) (Fin n) K) = 1 := by
    rw [← Matrix.GeneralLinearGroup.coe_mul, inv_mul_cancel, Matrix.GeneralLinearGroup.coe_one]
  set U : Matrix (Fin n) (Fin n) K := (u : Matrix (Fin n) (Fin n) K) with hU
  set Ui : Matrix (Fin n) (Fin n) K := ((u⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hUi
  set E : Matrix (Fin n) (Fin n) K := Matrix.single a b c with hE
  have hT : Matrix.transvection a b c = 1 + E := rfl
  rw [hT] at h
  have hN : Matrix.scalar (Fin n) s * (1 + E) - 1 = U * E * Ui := by
    rw [← h, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hUUi, add_sub_cancel_left]
  have hEE : E * E = 0 := by
    rw [hE]
    exact Matrix.single_mul_single_of_ne c a b a hab.symm c
  have hNN : (Matrix.scalar (Fin n) s * (1 + E) - 1) *
      (Matrix.scalar (Fin n) s * (1 + E) - 1) = 0 := by
    rw [hN]
    calc U * E * Ui * (U * E * Ui) = U * E * (Ui * U) * E * Ui := by
          simp only [Matrix.mul_assoc]
      _ = U * (E * E) * Ui := by rw [hUiU]; simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = 0 := by rw [hEE, Matrix.mul_zero, Matrix.zero_mul]
  have hrow : ∀ k, (Matrix.scalar (Fin n) s * (1 + E) - 1) j k =
      if j = k then s - 1 else 0 := by
    intro k
    by_cases hjk : j = k
    · subst hjk
      simp [hE, Matrix.sub_apply, Matrix.mul_add, hja.symm]
    · simp [hE, Matrix.sub_apply, Matrix.mul_add, hja.symm, hjk]
  have entry := congrFun (congrFun hNN j) j
  rw [Matrix.mul_apply, Finset.sum_eq_single j (fun k _ hk => by rw [hrow k]; simp [Ne.symm hk])
    (by simp), hrow j] at entry
  simp only [ite_true, Matrix.zero_apply] at entry
  exact sub_eq_zero.mp (mul_self_eq_zero.mp entry)

private lemma conj_pow_three_eq_scalar_mul
    {K : Type} [Field K] [Finite K] {N : ℕ}
    {δ' : MulAut (LargeEvenProj (LargeEvenSLGroup (Fin N) K))}
    {d : GL (Fin N) K}
    (hd : LargeEvenGraphAut (LargeEvenProjMk (LargeEvenSLGroup (Fin N) K))
        (fun h h' => (h' : GL (Fin N) K) = d * h * d⁻¹) δ')
    (hδ'3 : δ' ^ 3 = 1) (k : ↥(LargeEvenSLGroup (Fin N) K)) :
    ∃ c : Kˣ, (d ^ 3 : GL (Fin N) K) * (k : GL (Fin N) K) * (d ^ 3)⁻¹ =
      Matrix.GeneralLinearGroup.scalar (Fin N) c * (k : GL (Fin N) K) := by
  have hmem : ∀ m : ↥(LargeEvenSLGroup (Fin N) K),
      d * (m : GL (Fin N) K) * d⁻¹ ∈ LargeEvenSLGroup (Fin N) K :=
    fun m => largeEvenSLGroup_conj_mem d m
  let conj : ↥(LargeEvenSLGroup (Fin N) K) → ↥(LargeEvenSLGroup (Fin N) K) :=
    fun m => ⟨d * (m : GL (Fin N) K) * d⁻¹, hmem m⟩
  have hstep : ∀ m, δ' (LargeEvenProjMk (LargeEvenSLGroup (Fin N) K) m) =
      LargeEvenProjMk (LargeEvenSLGroup (Fin N) K) (conj m) :=
    fun m => hd m (conj m) rfl
  have hiter : (δ' ^ 3) (LargeEvenProjMk (LargeEvenSLGroup (Fin N) K) k) =
      LargeEvenProjMk (LargeEvenSLGroup (Fin N) K) (conj (conj (conj k))) := by
    show δ' (δ' (δ' (LargeEvenProjMk (LargeEvenSLGroup (Fin N) K) k))) = _
    rw [hstep k, hstep (conj k), hstep (conj (conj k))]
  have hfix : LargeEvenProjMk (LargeEvenSLGroup (Fin N) K) (conj (conj (conj k))) =
      LargeEvenProjMk (LargeEvenSLGroup (Fin N) K) k := by
    have h3 : (δ' ^ 3) (LargeEvenProjMk (LargeEvenSLGroup (Fin N) K) k) =
        LargeEvenProjMk (LargeEvenSLGroup (Fin N) K) k := by
      rw [hδ'3]; rfl
    exact hiter.symm.trans h3
  have hker : conj (conj (conj k)) * k⁻¹ ∈
      (LargeEvenProjMk (LargeEvenSLGroup (Fin N) K)).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hfix, mul_inv_cancel]
  have hker' : conj (conj (conj k)) * k⁻¹ ∈
      (LargeEvenScalars (Fin N) K).subgroupOf (LargeEvenSLGroup (Fin N) K) := by
    have hK : (LargeEvenProjMk (LargeEvenSLGroup (Fin N) K)).ker =
        (LargeEvenScalars (Fin N) K).subgroupOf (LargeEvenSLGroup (Fin N) K) :=
      QuotientGroup.ker_mk' _
    rw [← hK]
    exact hker
  rw [Subgroup.mem_subgroupOf, CFSG.Assembly.largeEvenScalars_def,
    MonoidHom.mem_range] at hker'
  obtain ⟨c, hc⟩ := hker'
  refine ⟨c, ?_⟩
  have hd3 : (d : GL (Fin N) K) ^ 3 = d * d * d := by rw [pow_succ, pow_succ, pow_one]
  have hd3inv : ((d * d * d : GL (Fin N) K))⁻¹ = d⁻¹ * d⁻¹ * d⁻¹ := by
    rw [mul_inv_rev, mul_inv_rev, mul_assoc]
  have hcoeeq : (conj (conj (conj k)) : GL (Fin N) K) =
      d ^ 3 * (k : GL (Fin N) K) * (d ^ 3)⁻¹ := by
    show d * (d * (d * (k : GL (Fin N) K) * d⁻¹) * d⁻¹) * d⁻¹ = _
    rw [hd3, hd3inv]
    group
  have hc' : Matrix.GeneralLinearGroup.scalar (Fin N) c =
      (conj (conj (conj k)) : GL (Fin N) K) * (k : GL (Fin N) K)⁻¹ := by
    rw [hc]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  rw [hc', hcoeeq]
  simp only [mul_assoc, inv_mul_cancel, mul_one]

private lemma conj_transvection_matrix
    {K : Type} [Field K] [Finite K] {N : ℕ}
    {δ' : MulAut (LargeEvenProj (LargeEvenSLGroup (Fin N) K))}
    {d : GL (Fin N) K}
    (hd : LargeEvenGraphAut (LargeEvenProjMk (LargeEvenSLGroup (Fin N) K))
        (fun h h' => (h' : GL (Fin N) K) = d * h * d⁻¹) δ')
    (hδ'3 : δ' ^ 3 = 1) {i j : Fin N} (hij : i ≠ j) :
    ∃ c : Kˣ, ((d ^ 3 : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) *
        Matrix.transvection i j 1 *
        (((d ^ 3)⁻¹ : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) =
      Matrix.scalar (Fin N) (c : K) * Matrix.transvection i j 1 := by
  let h : ↥(LargeEvenSLGroup (Fin N) K) :=
    ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.transvection i j 1)
        (by rw [Matrix.det_transvection_of_ne i j hij 1]; exact one_ne_zero),
      by
        rw [CFSG.StandardType.TypeA.mem_largeEvenSLGroup_iff,
          Matrix.GeneralLinearGroup.val_mkOfDetNeZero]
        exact Matrix.det_transvection_of_ne i j hij 1⟩
  obtain ⟨c, hc⟩ := conj_pow_three_eq_scalar_mul hd hδ'3 h
  refine ⟨c, ?_⟩
  have hk : ((h : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) = Matrix.transvection i j 1 :=
    Matrix.GeneralLinearGroup.val_mkOfDetNeZero _ _
  have hc' := congrArg (fun g : GL (Fin N) K => (g : Matrix (Fin N) (Fin N) K)) hc
  rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul] at hc'
  rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_scalar] at hc'
  rw [hk] at hc'
  exact hc'

private lemma comm_transvection_of_graphAut
    {K : Type} [Field K] [Finite K] {N : ℕ}
    {δ' : MulAut (LargeEvenProj (LargeEvenSLGroup (Fin N) K))}
    {d : GL (Fin N) K}
    (hd : LargeEvenGraphAut (LargeEvenProjMk (LargeEvenSLGroup (Fin N) K))
        (fun h h' => (h' : GL (Fin N) K) = d * h * d⁻¹) δ')
    (hδ'3 : δ' ^ 3 = 1) {i j : Fin N} (hij : i ≠ j) :
    ((d ^ 3 : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) * Matrix.transvection i j 1 =
      Matrix.transvection i j 1 * ((d ^ 3 : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) := by
  obtain ⟨c, hmat⟩ := conj_transvection_matrix hd hδ'3 hij
  have hc1 : (c : K) = 1 :=
    scalar_eq_one_of_conj_transvection_gl (d ^ 3) i j j hij hij.symm 1 (c : K) hmat
  have hmat1 : ((d ^ 3 : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) * Matrix.transvection i j 1 *
        (((d ^ 3)⁻¹ : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) =
      Matrix.transvection i j 1 := by
    rw [hc1] at hmat
    simpa using hmat
  have hUiU : (((d ^ 3)⁻¹ : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) *
      ((d ^ 3 : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) = 1 := by
    rw [← Matrix.GeneralLinearGroup.coe_mul, inv_mul_cancel, Matrix.GeneralLinearGroup.coe_one]
  calc ((d ^ 3 : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) * Matrix.transvection i j 1
      = ((d ^ 3 : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) * Matrix.transvection i j 1 *
          (((d ^ 3)⁻¹ : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) *
          ((d ^ 3 : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) := by
          simp only [Matrix.mul_assoc, hUiU, Matrix.mul_one]
    _ = Matrix.transvection i j 1 *
          ((d ^ 3 : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) := by rw [hmat1]

theorem linShape_lift
    {K : Type} [Field K] [Finite K]
    {N : ℕ}
    {Ā : Subgroup (MulAut (PSLg N K))}
    {δ' : MulAut (PSLg N K)}
    {J' : Subgroup (PSLg N K)} (hN : 2 ≤ N) (hR : RDatum Ā δ' J')
    (hδ' : δ' ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin N) K)) Set.univ) :
    ∃ d : GL (Fin N) K,
      LargeEvenGraphAut (LargeEvenProjMk (LargeEvenSLGroup (Fin N) K))
          (fun h h' => (h' : GL (Fin N) K) = d * h * d⁻¹) δ' ∧
        d ^ 3 ∈ LargeEvenScalars (Fin N) K ∧ d ∉ LargeEvenScalars (Fin N) K := by
  simp only [LargeEvenMatConjImage, Set.mem_setOf_eq, Set.mem_univ, true_and] at hδ'
  obtain ⟨d, hd⟩ := hδ'
  have hδ'3 : δ' ^ 3 = 1 := hR.elem.2 δ' hR.mem
  refine ⟨d, hd, ?_, ?_⟩
  · have hcomm : ∀ i j : Fin N, i ≠ j →
        Matrix.transvection i j (1 : K) *
            ((d ^ 3 : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) =
        ((d ^ 3 : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) *
            Matrix.transvection i j (1 : K) :=
      fun i j hij => (comm_transvection_of_graphAut hd hδ'3 hij).symm
    obtain ⟨a, ha⟩ := exists_eq_smul_one_of_commute_transvection hcomm
    have ha0 : a ≠ 0 := by
      intro ha0
      have hdet : (((d ^ 3 : GL (Fin N) K) : Matrix (Fin N) (Fin N) K)).det = a ^ N := by
        rw [ha, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]
      have hne := Matrix.GeneralLinearGroup.det_ne_zero (d ^ 3)
      rw [hdet] at hne
      exact hne ((pow_eq_zero_iff (by omega : N ≠ 0)).mpr ha0)
    exact CFSG.RankThree.PartTwo.Sec4.mem_statedScalars_of_eq_smul ha ha0
  · intro hdscal
    rw [CFSG.Assembly.largeEvenScalars_def, MonoidHom.mem_range] at hdscal
    obtain ⟨c, hc⟩ := hdscal
    have hπsurj : Function.Surjective (LargeEvenProjMk (LargeEvenSLGroup (Fin N) K)) :=
      QuotientGroup.mk'_surjective ((LargeEvenScalars (Fin N) K).subgroupOf
        (LargeEvenSLGroup (Fin N) K))
    have hfix : ∀ x : LargeEvenProj (LargeEvenSLGroup (Fin N) K), δ' x = x := by
      intro x
      obtain ⟨h, rfl⟩ := hπsurj x
      have hconj : d * (h : GL (Fin N) K) * d⁻¹ = (h : GL (Fin N) K) := by
        rw [← hc]
        rw [Matrix.GeneralLinearGroup.scalar_commute c (h : GL (Fin N) K)]
        group
      exact hd h h hconj.symm
    exact hR.ne_one (MulEquiv.ext hfix)

end CFSG.StandardType.TablePThreeKG

end
