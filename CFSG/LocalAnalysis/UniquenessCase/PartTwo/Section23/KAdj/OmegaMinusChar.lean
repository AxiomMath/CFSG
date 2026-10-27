module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.OmegaMinusHall
public import CFSG.LocalAnalysis.UniquenessCase.UC22S20
import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsOmegaRegular
import CFSG.RankThree.PartOne.F106.OddRadSpTwo
import CFSG.RankThree.PartTwo.Sec18.Tools
import CFSG.LocalAnalysis.UniquenessCase.UC22P22m
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockOrthMinusRes

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KAdjE

open CFSG.ClassicalGroups.Orthogonal CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
open CFSG.AGLEmbedding.LeviBlock

private theorem perfectResidual_le_ker_of_range_E14 {G H : Type*} [Group G] [Group H] (φ : G →* H)
    (S : Subgroup H) [Group.IsSolvable S] (hS : ∀ g, φ g ∈ S) :
    CFSG.perfectResidual G ≤ φ.ker := by
  obtain ⟨n, hn⟩ := (inferInstance : Group.IsSolvable S).solvable
  have h1 : (CFSG.perfectResidual G).map (φ.codRestrict S hS) ≤ CFSG.perfectResidual S :=
    CFSG.RankThree.PartTwo.Sec18.map_perfectResidual_le _
  have h2 : CFSG.perfectResidual S ≤ derivedSeries S n := iInf_le _ n
  have h3 : (CFSG.perfectResidual G).map (φ.codRestrict S hS) ≤ ⊥ := by
    rw [← hn]
    exact h1.trans h2
  intro g hg
  have hg' : (φ.codRestrict S hS) g = 1 := by
    have := Subgroup.map_le_iff_le_comap.1 h3 hg
    rwa [Subgroup.mem_comap, Subgroup.mem_bot] at this
  rw [MonoidHom.mem_ker]
  simpa using congrArg (Subtype.val) hg'

private theorem orthCuts_tailQAlpha_E14 : OrthCuts 3 (![0, 2, 3] : Fin 3 → ℕ) :=
  ⟨Fin.strictMono_iff_lt_succ.2 (by decide), rfl, by decide⟩

private theorem orthCoefMat_tailDiag_E14 {K : Type} [Field K] {A : Type} [AddCommGroup A]
    [Module K A] {r : ℕ} (t : Fin r → Kˣ) (h : A ≃ₗ[K] A) :
    orthCoefMat (tailDiag r t h) = Matrix.diagonal (fun i => ((t i : Kˣ) : K)) := by
  ext i j
  simp only [orthCoefMat_apply, tailDiag_apply, torusElt_apply, hypVec, Matrix.diagonal_apply]
  by_cases hij : i = j
  · subst hij
    simp
  · rw [if_neg hij]
    have hne : (Sum.inl i : Fin r ⊕ Fin r) ≠ Sum.inl j := fun hh => hij (Sum.inl.inj hh)
    rw [Pi.single_eq_of_ne hne, mul_zero]

private theorem orthBlockIdx_zero_castSucc_E14 (i : Fin 2) :
    orthBlockIdx orthCuts_tailQAlpha_E14 0 i = i.castSucc := by
  fin_cases i
  · decide
  · decide

private theorem det_submatrix_zero_E14 {K : Type} [Field K] (f : Fin 3 → K) :
    ((Matrix.diagonal f).submatrix (orthBlockIdx orthCuts_tailQAlpha_E14 0)
      (orthBlockIdx orthCuts_tailQAlpha_E14 0)).det = f 0 * f 1 := by
  rw [Matrix.submatrix_diagonal f (orthBlockIdx orthCuts_tailQAlpha_E14 0)
    (orthBlockIdx_injective orthCuts_tailQAlpha_E14 0), Matrix.det_diagonal]
  simp only [Function.comp_apply]
  change (∏ x : Fin 2, f (orthBlockIdx orthCuts_tailQAlpha_E14 0 x)) = f 0 * f 1
  rw [Fin.prod_univ_two]
  simp [orthBlockIdx_zero_castSucc_E14]

private theorem det_submatrix_one_E14 {K : Type} [Field K] (f : Fin 3 → K) :
    ((Matrix.diagonal f).submatrix (orthBlockIdx orthCuts_tailQAlpha_E14 1)
      (orthBlockIdx orthCuts_tailQAlpha_E14 1)).det = f 2 := by
  rw [Matrix.submatrix_diagonal f (orthBlockIdx orthCuts_tailQAlpha_E14 1)
    (orthBlockIdx_injective orthCuts_tailQAlpha_E14 1), Matrix.det_diagonal]
  simp only [Function.comp_apply]
  change (∏ x : Fin 1, f (orthBlockIdx orthCuts_tailQAlpha_E14 1 x)) = f 2
  rw [Fin.prod_univ_one]
  rfl

private theorem det_block_zero_tailDiag_E14 {K : Type} [Field K] {b c : K}
    {q : ↥(omegaMinusTailQAlpha K b c)} {a : Fin 3 → Kˣ} {h : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K)}
    (hq : ((q : OmegaMinusE K b c) :
      ((Fin 3 ⊕ Fin 3 → K) × (Fin 2 → K)) ≃ₗ[K] ((Fin 3 ⊕ Fin 3 → K) × (Fin 2 → K))) =
        tailDiag 3 a h) :
    ((Matrix.GeneralLinearGroup.det
      (orthBlockHom (minusTailForm K b c) orthCuts_tailQAlpha_E14 0 q) : Kˣ) : K) =
        (a 0 : K) * (a 1 : K) := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, coe_orthBlockHom, hq, orthBlockMat,
    orthCoefMat_tailDiag_E14]
  exact det_submatrix_zero_E14 (fun i => (a i : K))

private theorem det_block_one_tailDiag_E14 {K : Type} [Field K] {b c : K}
    {q : ↥(omegaMinusTailQAlpha K b c)} {a : Fin 3 → Kˣ} {h : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K)}
    (hq : ((q : OmegaMinusE K b c) :
      ((Fin 3 ⊕ Fin 3 → K) × (Fin 2 → K)) ≃ₗ[K] ((Fin 3 ⊕ Fin 3 → K) × (Fin 2 → K))) =
        tailDiag 3 a h) :
    ((Matrix.GeneralLinearGroup.det
      (orthBlockHom (minusTailForm K b c) orthCuts_tailQAlpha_E14 1 q) : Kˣ) : K) =
        (a 2 : K) := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, coe_orthBlockHom, hq, orthBlockMat,
    orthCoefMat_tailDiag_E14]
  exact det_submatrix_one_E14 (fun i => (a i : K))

private theorem orthResHom_tailDiag_E14 {K : Type} [Field K] {b c : K}
    {q : ↥(omegaMinusTailQAlpha K b c)} {a : Fin 3 → Kˣ} {h : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K)}
    (hq : ((q : OmegaMinusE K b c) :
      ((Fin 3 ⊕ Fin 3 → K) × (Fin 2 → K)) ≃ₗ[K] ((Fin 3 ⊕ Fin 3 → K) × (Fin 2 → K))) =
        tailDiag 3 a h)
    (h1 : orthResHom (minusTailForm K b c) orthCuts_tailQAlpha_E14 q = 1) : h = 1 := by
  refine LinearEquiv.ext fun v => ?_
  have h2 : orthResHom (minusTailForm K b c) orthCuts_tailQAlpha_E14 q (0, v) = (0, v) := by
    rw [h1]
    rfl
  rw [orthResHom_apply, orthResMat_apply, orthResIncl_apply, hq, tailDiag_apply,
    orthResProj_apply] at h2
  simpa using congrArg Prod.snd h2

private theorem isSolvable_orthogonalGroup_tail_E14 {K : Type} [Field K] [Finite K] [CharP K 2]
    {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {m : ℕ} (hm : m = 0) :
    Group.IsSolvable
      ↥(TauCeti.QuadraticMap.orthogonalGroup (quadTail m (minusTailForm K b c))) := by
  subst hm
  refine CFSG.StandardType.LayerCores.OrthRegular.isSolvable_orthogonalGroup_of_finrank_le_two
    ?_ ?_
  · exact nondegenerate_polarBilin_quadTail (nondegenerate_minusTailForm hirr)
  · rw [finrank_tailSpace (r := 0) (A := Fin 2 → K), finrank_fin_two_fun]

private theorem prodHom_injective_E14 {K : Type} [Field K] {A : Type} [AddCommGroup A]
    [Module K A] {r : ℕ} : Function.Injective (prodHom (K := K) (r := r) A) := by
  intro g h hgh
  apply LinearEquiv.ext
  intro v
  have h' := congrArg
    (fun e : ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A) => e (v, 0)) hgh
  rw [prodHom_apply, prodHom_apply, LinearEquiv.prodCongr_apply,
    LinearEquiv.prodCongr_apply] at h'
  exact (Prod.ext_iff.1 h').1

private theorem orderOf_prodHom_torusElt_coroot_E14 {K : Type} [Field K] (u : Kˣ) :
    orderOf (prodHom (Fin 2 → K) (torusElt 3 K ![u, u⁻¹, 1])) = orderOf u := by
  rw [orderOf_injective (prodHom (K := K) (r := 3) (Fin 2 → K))
      (prodHom_injective_E14 (K := K) (A := Fin 2 → K) (r := 3)) (torusElt 3 K ![u, u⁻¹, 1]),
    orderOf_injective (torusElt 3 K) torusElt_injective ![u, u⁻¹, 1], orderOf_eq_orderOf_iff]
  intro n
  constructor
  · intro hh
    have := congrFun hh 0
    simpa using this
  · intro hh
    funext i
    fin_cases i
    · simpa using hh
    · have : (u⁻¹) ^ n = 1 := by rw [inv_pow, hh, inv_one]
      simpa using this
    · simp

theorem omegaMinus_tailDiag_of_mem_hinf {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {τ : OmegaMinusE K b c}
    (hτ : τ ∈ Hinf (omegaMinusTailQAlpha K b c)) {a : Fin 3 → Kˣ}
    {h : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K)}
    (hτa : ((τ : OmegaMinusE K b c) :
      ((Fin 3 ⊕ Fin 3 → K) × (Fin 2 → K)) ≃ₗ[K] ((Fin 3 ⊕ Fin 3 → K) × (Fin 2 → K))) =
        tailDiag 3 a h) :
    a 0 * a 1 = 1 ∧ a 2 = 1 ∧ h = 1 := by
  have hτ' : τ ∈ (CFSG.perfectResidual ↥(omegaMinusTailQAlpha K b c)).map
      (omegaMinusTailQAlpha K b c).subtype := hτ
  obtain ⟨q, hq_perf, hq_eq⟩ := Subgroup.mem_map.1 hτ'
  have hq : ((q : OmegaMinusE K b c) :
      ((Fin 3 ⊕ Fin 3 → K) × (Fin 2 → K)) ≃ₗ[K] ((Fin 3 ⊕ Fin 3 → K) × (Fin 2 → K))) =
        tailDiag 3 a h := by
    rw [show (q : OmegaMinusE K b c) = τ from hq_eq, hτa]
  have hker0 := CFSG.RankThree.PartOne.F106.OddRadSp.perfectResidual_le_ker_of_comm
    (Matrix.GeneralLinearGroup.det.comp
      (orthBlockHom (minusTailForm K b c) orthCuts_tailQAlpha_E14 0)) hq_perf
  have hker1 := CFSG.RankThree.PartOne.F106.OddRadSp.perfectResidual_le_ker_of_comm
    (Matrix.GeneralLinearGroup.det.comp
      (orthBlockHom (minusTailForm K b c) orthCuts_tailQAlpha_E14 1)) hq_perf
  have h01K : (a 0 : K) * (a 1 : K) = 1 := by
    have hdet : Matrix.GeneralLinearGroup.det
        (orthBlockHom (minusTailForm K b c) orthCuts_tailQAlpha_E14 0 q) = 1 := by
      simpa only [MonoidHom.mem_ker, MonoidHom.comp_apply] using hker0
    rw [← det_block_zero_tailDiag_E14 hq, hdet, Units.val_one]
  have h2K : (a 2 : K) = 1 := by
    have hdet : Matrix.GeneralLinearGroup.det
        (orthBlockHom (minusTailForm K b c) orthCuts_tailQAlpha_E14 1 q) = 1 := by
      simpa only [MonoidHom.mem_ker, MonoidHom.comp_apply] using hker1
    rw [← det_block_one_tailDiag_E14 hq, hdet, Units.val_one]
  refine ⟨?_, ?_, ?_⟩
  · apply Units.ext
    simpa using h01K
  · apply Units.ext
    simpa using h2K
  · haveI : Group.IsSolvable ↥(TauCeti.QuadraticMap.orthogonalGroup
        (quadTail (3 - ![0, 2, 3] (Fin.last 2)) (minusTailForm K b c))) :=
      isSolvable_orthogonalGroup_tail_E14 hirr (m := 3 - ![0, 2, 3] (Fin.last 2)) (by decide)
    have hres : orthResHom (minusTailForm K b c) orthCuts_tailQAlpha_E14 q = 1 := by
      have := perfectResidual_le_ker_of_range_E14
        (orthResHom (minusTailForm K b c) orthCuts_tailQAlpha_E14)
        (TauCeti.QuadraticMap.orthogonalGroup
          (quadTail (3 - ![0, 2, 3] (Fin.last 2)) (minusTailForm K b c)))
        (fun g => orthResHom_mem_orthogonalGroup orthCuts_tailQAlpha_E14 g) hq_perf
      simpa only [MonoidHom.mem_ker] using this
    exact orthResHom_tailDiag_E14 hq hres

theorem omegaMinus_exists_conj_coroot {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {t : OmegaMinusE K b c}
    (ht : t ∈ Hinf (omegaMinusTailQAlpha K b c) ⊓ omegaMinusTailQZero K b c)
    (hodd : Odd (orderOf t)) :
    ∃ e ∈ (tailUnipotent 3 (minusTailForm K b c)).subgroupOf
        (orthElementaryGroup (quadTail 3 (minusTailForm K b c))), ∃ u : Kˣ,
      ((e * t * e⁻¹ : OmegaMinusE K b c) :
        ((Fin 3 ⊕ Fin 3 → K) × (Fin 2 → K)) ≃ₗ[K] ((Fin 3 ⊕ Fin 3 → K) × (Fin 2 → K))) =
          prodHom (Fin 2 → K) (torusElt 3 K ![u, u⁻¹, 1]) ∧ orderOf u = orderOf t := by
  have ht_Qα : t ∈ omegaMinusTailQAlpha K b c :=
    Subgroup.map_subtype_le (CFSG.perfectResidual ↥(omegaMinusTailQAlpha K b c)) ht.1
  have ht_borel : t ∈ (tailBorel 3 (minusTailForm K b c)).subgroupOf
      (orthElementaryGroup (quadTail 3 (minusTailForm K b c))) := by
    rw [← omegaMinusTailQZero_inf_QAlpha K b c]
    exact ⟨ht.2, ht_Qα⟩
  obtain ⟨e, he_Ū, hτ_T⟩ := omegaMinus_exists_conj_mem_tailTorus hirr ht_borel hodd
  have hτ_hinf : e * t * e⁻¹ ∈ Hinf (omegaMinusTailQAlpha K b c) := by
    have he_Qα : e ∈ omegaMinusTailQAlpha K b c :=
      (omegaMinus_tailUnipotent_le_inf hirr he_Ū).2
    have he_norm := uc22p22m_le_normalizer_Hinf (omegaMinusTailQAlpha K b c) he_Qα
    exact (Subgroup.mem_normalizer_iff.1 he_norm t).1 ht.1
  obtain ⟨-, a, h, hh, hdiag⟩ := mem_tailTorus.1 (Subgroup.mem_subgroupOf.1 hτ_T)
  obtain ⟨ha01, ha2, hh1⟩ := omegaMinus_tailDiag_of_mem_hinf hirr hτ_hinf hdiag.symm
  have ha : a = ![a 0, (a 0)⁻¹, 1] := by
    funext i
    fin_cases i
    · rfl
    · exact eq_inv_of_mul_eq_one_right ha01
    · exact ha2
  have hmain : ((e * t * e⁻¹ : OmegaMinusE K b c) :
      ((Fin 3 ⊕ Fin 3 → K) × (Fin 2 → K)) ≃ₗ[K] ((Fin 3 ⊕ Fin 3 → K) × (Fin 2 → K))) =
        prodHom (Fin 2 → K) (torusElt 3 K ![a 0, (a 0)⁻¹, 1]) := by
    rw [hdiag.symm, hh1]
    conv_lhs => rw [ha]
    rfl
  refine ⟨e, he_Ū, a 0, hmain, ?_⟩
  calc
    orderOf (a 0) = orderOf (prodHom (Fin 2 → K) (torusElt 3 K ![a 0, (a 0)⁻¹, 1])) :=
      (orderOf_prodHom_torusElt_coroot_E14 (a 0)).symm
    _ = orderOf ((e * t * e⁻¹ : OmegaMinusE K b c) :
        ((Fin 3 ⊕ Fin 3 → K) × (Fin 2 → K)) ≃ₗ[K]
          ((Fin 3 ⊕ Fin 3 → K) × (Fin 2 → K))) := by rw [← hmain]
    _ = orderOf (e * t * e⁻¹ : OmegaMinusE K b c) := Subgroup.orderOf_coe _
    _ = orderOf t := by
      simpa [MulAut.conj_apply] using
        orderOf_injective (MulAut.conj e).toMonoidHom (MulAut.conj e).injective t

end CFSG.LocalAnalysis.UniquenessCase.UC22.KAdjE
