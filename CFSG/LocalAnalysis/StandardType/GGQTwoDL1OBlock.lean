module

public import CFSG.ClassicalInvolution.Phan.PhanDn.DiagTorus
public import CFSG.ClassicalInvolution.Phan.PhanDn.NormForm
public import CFSG.ClassicalInvolution.Balance.StrongPowSuBlocks
public import CFSG.RankThree.OrthogonalInvolutions.Dickson
import CFSG.ClassicalInvolution.Phan.PhanDn.KLinearIsometry
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.ClassicalInvolution.Balance.PassTwoFinal
public import CFSG.ClassicalInvolution.Models.LinearFrames
public import CFSG.ClassicalInvolution.Models.LinearPairs
public import CFSG.ClassicalInvolution.Models.OrthogonalPairs.Anisotropic.Plane
public import CFSG.ClassicalInvolution.Models.OrthogonalPairs.Pairs
public import CFSG.LieType.Ree.SmallReeModelSchreier
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOddLieClassical
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOddLieE6E7Triality
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDescentEndpoint
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelModel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixComponentsCover
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixModelGeometry
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalTraceZeroCoordinates
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwo
public import CFSG.LocalAnalysis.ComponentInitial.BlockOvergroupDichotomy
public import CFSG.LocalAnalysis.ComponentInitial.GeneralizedFittingProduct
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.LowRank

public section

namespace CFSG.StandardType.QTwo

open CFSG.ClassicalInvolution.PhanDn CFSG.ClassicalInvolution.Models.OrthogonalPairs
open CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary CFSG.LieType.Steinberg
open CFSG.LieType.BorelTits CFSG.ClassicalInvolution.Phan
open CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary
open CFSG.RankThree.OrthogonalInvolutions (omegaGroup commSpace mem_commSpace mem_omegaGroup
  finrank_commSpace_reflection)
open QuadraticMap

open scoped Matrix

variable {F K : Type} [Field F] [Field K] [Algebra F K]

theorem qtwoDL1_mem_omegaGroup_of_isKLinear [CharP F 2] [CharP K 2] [FiniteDimensional F K]
    {σ : K ≃+* K} (E : QuadExt F K σ) {n : ℕ} {g : (Fin n → K) ≃ₗ[F] (Fin n → K)}
    (hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup (Qn E n))
    (hK : ∀ (a : K) (x : Fin n → K), g (a • x) = a • g x) :
    g ∈ omegaGroup (Qn E n) (Qn_polarBilin_nondegenerate E n) := by
  rw [mem_omegaGroup]
  refine ⟨hgO, ?_⟩
  let gK : (Fin n → K) →ₗ[K] (Fin n → K) :=
    { toFun := g, map_add' := g.map_add, map_smul' := hK }
  let W : Submodule K (Fin n → K) := LinearMap.range (gK - 1)
  have hEq : commSpace g = W.restrictScalars F := by
    ext x
    constructor
    · intro hx
      obtain ⟨v, hv⟩ := mem_commSpace.mp hx
      exact ⟨v, by simpa [gK] using hv⟩
    · rintro ⟨v, hv⟩
      exact mem_commSpace.mpr ⟨v, by simpa [gK] using hv⟩
  have htower := Module.finrank_mul_finrank F K (W.restrictScalars F)
  rw [hEq, ← htower, E.finrank_eq]
  exact even_two_mul _

theorem qtwoDL1_tauAt_not_mem_omegaGroup [CharP F 2] [CharP K 2] [FiniteDimensional F K]
    {σ : K ≃+* K} (E : QuadExt F K σ) {n : ℕ} (k : Fin n) :
    tauAt E k ∉ omegaGroup (Qn E n) (Qn_polarBilin_nondegenerate E n) := by
  intro hmem
  rw [mem_omegaGroup] at hmem
  have hQ : Qn E n (Pi.single k 1) = 1 := Qn_single_one E k
  haveI : Invertible (Qn E n (Pi.single k 1)) :=
    invertibleOfNonzero (by rw [hQ]; exact one_ne_zero)
  have hrefl : tauAt E k = TauCeti.QuadraticMap.reflection (Qn E n) (Pi.single k 1) := by
    rw [tauAt_eq_reflect E k, CFSG.ClassicalGroups.Orthogonal.reflect_eq_reflection]
  have hfin : Module.finrank F (commSpace (tauAt E k)) = 1 := by
    rw [hrefl]
    exact finrank_commSpace_reflection (Qn_polarBilin_nondegenerate E n) (Pi.single k 1)
  rw [hfin] at hmem
  obtain ⟨m, hm⟩ := hmem.2
  omega

theorem qtwoDL1_orthBlock [Finite K] [CharP K 2] (hK4 : Nat.card K = 4)
    (E : QuadExt F K (unitaryInvolution K 2 1)) {n : ℕ} {i j k : Fin n}
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    {ζ : normOne (unitaryInvolution K 2 1)} (hζ : ζ ≠ 1) (hζ3 : ζ ^ 3 = 1)
    {g : (Fin n → K) ≃ₗ[F] (Fin n → K)}
    (hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup (Qn E n))
    (hgc : ∀ f : Fin n → ZMod 3, f i = f j → f j = f k →
      g * diagHom F (unitaryInvolution K 2 1) n (fun l => ζ ^ (f l).val) =
        diagHom F (unitaryInvolution K 2 1) n (fun l => ζ ^ (f l).val) * g)
    (h2 : ∃ m : ℕ, g ^ (2 ^ m) = 1) :
    ∃ s ∈ coordBlockSU K 2 1 ({i, j, k} : Finset (Fin n)),
      suEndN (F := F) (unitaryInvolution K 2 1) n s = g := by
  classical
  let σ : K ≃+* K := unitaryInvolution K 2 1
  have hσ2 : ∀ c : K, σ c = c ^ 2 := by
    intro c
    change unitaryInvolution K 2 1 c = c ^ 2
    rw [unitaryInvolution_apply]
    norm_num
  let J : Finset (Fin n) := {i, j, k}
  let u : Kˣ := (ζ : Kˣ)
  let z : K := (u : K)
  have hu_ne : u ≠ 1 := fun h => hζ (Subtype.ext (by simpa [u] using h))
  have hu3 : u ^ 3 = 1 := by
    have h := congrArg (fun t : normOne σ => (t : Kˣ)) hζ3
    simpa [u] using h
  have hz_ne_one : z ≠ 1 := by
    intro h
    exact hu_ne (Units.ext (by simpa [z] using h))
  have hz1 : z - 1 ≠ 0 := sub_ne_zero.mpr hz_ne_one
  have hnorm : σ z * z = 1 := by simpa [z, u] using (mem_normOne σ).mp ζ.2
  have hz_notin : z ∉ Set.range (algebraMap F K) := by
    rintro ⟨a, ha⟩
    have hσz : σ z = z := by rw [← ha]; exact E.fix a
    have hzz : z * z = 1 := by simpa [hσz] using hnorm
    have hu2 : u ^ 2 = 1 := by
      apply Units.ext
      simpa [z, pow_two, Units.val_pow_eq_pow_val] using hzz
    have hone : u = 1 :=
      (pow_eq_one_iff_of_coprime (a := u) (m := 2) (n := 3)
        (by norm_num : Nat.Coprime 2 3)).mp ⟨hu2, hu3⟩
    exact hu_ne hone
  have hz_notin' : ∀ a : F, algebraMap F K a ≠ z := fun a ha => hz_notin ⟨a, ha⟩
  have hKlin : ∀ (a : K) (x : Fin n → K), g (a • x) = a • g x := by
    let S : Submodule F K :=
      { carrier := {a | ∀ x, g (a • x) = a • g x}
        zero_mem' := by intro x; simp
        add_mem' := by
          intro a b ha hb x
          rw [add_smul, map_add, ha x, hb x, add_smul]
        smul_mem' := by
          intro c a ha x
          rw [smul_assoc, g.map_smul, ha x, smul_assoc] }
    have hcomm1 : g * diagHom F σ n (fun _ : Fin n => ζ) =
        diagHom F σ n (fun _ : Fin n => ζ) * g := by
      have h := hgc (fun _ : Fin n => (1 : ZMod 3)) rfl rfl
      have hfun : (fun l : Fin n => ζ ^ (((fun _ : Fin n => (1 : ZMod 3)) l).val)) =
          (fun _ : Fin n => ζ) := by
        funext m
        rw [ZMod.val_one 3, pow_one]
      rwa [hfun] at h
    have hdz : ∀ y : Fin n → K, diagHom F σ n (fun _ : Fin n => ζ) y = z • y := by
      intro y
      funext m
      simp [diagHom_apply, Pi.smul_apply, smul_eq_mul, z, u]
    have h1S : (1 : K) ∈ S := by intro x; simp
    have hzS : z ∈ S := by
      intro x
      have h := congrArg (fun e : (Fin n → K) ≃ₗ[F] (Fin n → K) => e x) hcomm1
      rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hdz x, hdz (g x)] at h
      exact h
    have hspan_le : Submodule.span F ({1, z} : Set K) ≤ S := by
      rw [Submodule.span_le]
      intro a ha
      rcases ha with rfl | rfl
      · exact h1S
      · exact hzS
    have hrange : Set.range (E.basisOneR hz_notin') = ({1, z} : Set K) := by
      ext a
      constructor
      · rintro ⟨t, rfl⟩
        fin_cases t <;> simp [QuadExt.basisOneR_apply]
      · intro ha
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
        rcases ha with rfl | rfl
        · exact ⟨0, by simp [QuadExt.basisOneR_apply]⟩
        · exact ⟨1, by simp [QuadExt.basisOneR_apply]⟩
    have htop : (⊤ : Submodule F K) = Submodule.span F ({1, z} : Set K) := by
      rw [← hrange]
      exact (E.basisOneR hz_notin').span_eq.symm
    have htop_le : (⊤ : Submodule F K) ≤ S := by
      rw [htop]
      exact hspan_le
    intro a
    exact htop_le Submodule.mem_top
  let μ : Fin n → K := fun l => (g (Pi.single l (1 : K))) l
  have hDapply (l : Fin n) (x : Fin n → K) :
      diagSingle F σ n l ζ x = x + (z - 1) • Pi.single l (x l) := by
    funext m
    rw [diagSingle_apply, diagHom_apply]
    by_cases hm : m = l
    · subst hm
      simp only [Pi.mulSingle_eq_same, Pi.single_eq_same, Pi.add_apply, Pi.smul_apply,
        smul_eq_mul, z, u]
      ring
    · rw [Pi.mulSingle_eq_of_ne hm]
      simp [Pi.smul_apply, Pi.single_apply, hm, smul_eq_mul]
  have hcommD (l : Fin n) (hl : l ∉ J) :
      g * diagSingle F σ n l ζ = diagSingle F σ n l ζ * g := by
    have hl' : l ≠ i ∧ l ≠ j ∧ l ≠ k := by
      simpa only [J, Finset.mem_insert, Finset.mem_singleton, not_or] using hl
    let fz : Fin n → ZMod 3 := Pi.single l (1 : ZMod 3)
    have hcond1 : fz i = fz j := by
      simp only [fz, Pi.single_apply]
      rw [if_neg (show i ≠ l from hl'.1.symm), if_neg (show j ≠ l from hl'.2.1.symm)]
    have hcond2 : fz j = fz k := by
      simp only [fz, Pi.single_apply]
      rw [if_neg (show j ≠ l from hl'.2.1.symm), if_neg (show k ≠ l from hl'.2.2.symm)]
    have h := hgc fz hcond1 hcond2
    have hfun : (fun m => ζ ^ (fz m).val) = Pi.mulSingle l ζ := by
      funext m
      by_cases hm : m = l
      · subst hm; simp [fz, ZMod.val_one 3, pow_one]
      · rw [Pi.mulSingle_eq_of_ne hm]
        simp [fz, Pi.single_apply, hm]
    rw [hfun] at h
    rw [diagSingle_apply]
    exact h
  have hproj (l : Fin n) (hl : l ∉ J) (x : Fin n → K) :
      g (Pi.single l (x l)) = Pi.single l ((g x) l) := by
    have hx := congrArg (fun e : (Fin n → K) ≃ₗ[F] (Fin n → K) => e x) (hcommD l hl)
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hDapply l x, hDapply l (g x),
      map_add, hKlin (z - 1) (Pi.single l (x l))] at hx
    have hcancel : (z - 1) • g (Pi.single l (x l)) =
        (z - 1) • Pi.single l ((g x) l) := by
      have := congrArg (fun y : Fin n → K => y - g x) hx
      simpa using this
    funext m
    exact mul_left_cancel₀ hz1 (by
      simpa [Pi.smul_apply, smul_eq_mul] using congrFun hcancel m)
  have hsingle (l : Fin n) (hl : l ∉ J) (c : K) :
      g (Pi.single l c) = Pi.single l (c * μ l) := by
    have h1 : Pi.single l c = c • Pi.single l (1 : K) := by
      funext m
      by_cases hm : m = l
      · subst hm; simp
      · simp [Pi.single_eq_of_ne (Ne.symm hm), hm]
    rw [h1, hKlin c (Pi.single l 1)]
    have hg1 : g (Pi.single l 1) = Pi.single l (μ l) := by
      simpa [μ] using hproj l hl (Pi.single l 1)
    rw [hg1]
    funext m
    by_cases hm : m = l
    · subst hm; simp [Pi.smul_apply, smul_eq_mul]
    · simp [Pi.single_eq_of_ne hm, hm]
  have hcoord (l : Fin n) (hl : l ∉ J) (x : Fin n → K) :
      (g x) l = x l * μ l := by
    have h1 := hproj l hl x
    have h2 := hsingle l hl (x l)
    rw [h2] at h1
    have := congrFun h1 l
    simpa using this.symm
  have hμnorm (l : Fin n) (hl : l ∉ J) : σ (μ l) * μ l = 1 := by
    have h := herm_map_of_isKLinear E hgO hKlin (Pi.single l 1) (Pi.single l 1)
    rw [hsingle l hl 1, one_mul] at h
    have hL : herm σ (Pi.single l (μ l)) (Pi.single l (μ l)) = σ (μ l) * μ l := by
      rw [herm_single_left, Pi.single_eq_same]
    have hR : herm σ (Pi.single l (1 : K)) (Pi.single l (1 : K)) = 1 := by
      rw [herm_single_left, Pi.single_eq_same, map_one, one_mul]
    rwa [hL, hR] at h
  obtain ⟨m, hm⟩ := h2
  have hcop : Nat.Coprime (2 ^ m) 3 := by
    cases m with
    | zero => norm_num
    | succ m => rw [Nat.coprime_pow_left_iff (Nat.succ_pos m)]; norm_num
  have hμpow (l : Fin n) (hl : l ∉ J) : μ l ^ (2 ^ m) = 1 := by
    have hiter : ∀ t : ℕ,
        (g ^ t) (Pi.single l (1 : K) : Fin n → K) = Pi.single l (μ l ^ t) := by
      intro t
      induction t with
      | zero => simp
      | succ t ih =>
        rw [pow_succ', LinearEquiv.mul_apply, ih, hsingle l hl (μ l ^ t), pow_succ]
    have hfix : (Pi.single l (μ l ^ (2 ^ m)) : Fin n → K) =
        (Pi.single l (1 : K) : Fin n → K) := by
      have h := congrArg (fun e : (Fin n → K) ≃ₗ[F] (Fin n → K) =>
        e (Pi.single l (1 : K) : Fin n → K)) hm
      rw [hiter (2 ^ m)] at h
      simpa using h
    have := congrFun hfix l
    simpa using this
  have hμ3 (l : Fin n) (hl : l ∉ J) : μ l ^ 3 = 1 := by
    have h := hμnorm l hl
    rw [hσ2 (μ l), ← pow_succ] at h
    simpa using h
  have hμeq (l : Fin n) (hl : l ∉ J) : μ l = 1 :=
    (pow_eq_one_iff_of_coprime (a := μ l) (m := 2 ^ m) (n := 3) hcop).mp
      ⟨hμpow l hl, hμ3 l hl⟩
  let gK : (Fin n → K) →ₗ[K] (Fin n → K) :=
    { toFun := g, map_add' := g.map_add, map_smul' := hKlin }
  let A : Matrix (Fin n) (Fin n) K := LinearMap.toMatrix' gK
  have hA_apply : ∀ v : Fin n → K, A *ᵥ v = g v := fun v => LinearMap.toMatrix'_mulVec gK v
  have hAherm : ∀ v w : Fin n → K, herm σ (A *ᵥ v) (A *ᵥ w) = herm σ v w := by
    intro v w
    rw [hA_apply, hA_apply]
    exact herm_map_of_isKLinear E hgO hKlin v w
  have huni : conjTr σ A * A = 1 := conjTr_mul_self_of_isometry σ hAherm
  have hA_entry (i j : Fin n) : A i j = (g (Pi.single j 1)) i := by
    have h := congrFun (hA_apply (Pi.single j 1)) i
    rw [Matrix.mulVec_single_one, Matrix.col_apply] at h
    simpa using h
  have hA_out (l : Fin n) (hl : l ∉ J) (j : Fin n) :
      A l j = if j = l then μ l else 0 := by
    rw [hA_entry, hcoord l hl (Pi.single j 1)]
    by_cases hj : j = l
    · subst hj; simp
    · rw [Pi.single_eq_of_ne (Ne.symm hj), if_neg hj]; simp
  have hA_col (l : Fin n) (hl : l ∉ J) (i : Fin n) :
      A i l = if i = l then μ l else 0 := by
    rw [hA_entry, hsingle l hl 1, one_mul]
    by_cases hi : i = l
    · subst hi; simp
    · rw [Pi.single_eq_of_ne hi, if_neg hi]
  have hA_out1 (l : Fin n) (hl : l ∉ J) (j : Fin n) :
      A l j = if j = l then 1 else 0 := by rw [hA_out l hl j, hμeq l hl]
  have hA_col1 (l : Fin n) (hl : l ∉ J) (i : Fin n) :
      A i l = if i = l then 1 else 0 := by rw [hA_col l hl i, hμeq l hl]
  have hblock : ∀ i j : Fin n, (i ∉ J ∨ j ∉ J) → A i j = if i = j then 1 else 0 := by
    intro i j hij
    rcases hij with hi | hj
    · simpa [eq_comm] using hA_out1 i hi j
    · exact hA_col1 j hj i
  have hApow_mulVec : ∀ t : ℕ, ∀ v : Fin n → K, (A ^ t) *ᵥ v = (g ^ t) v := by
    intro t
    induction t with
    | zero => intro v; simp
    | succ t ih =>
      intro v
      have hg : g ^ (t + 1) = g ^ t * g := pow_succ g t
      rw [hg, LinearEquiv.mul_apply, pow_succ, ← Matrix.mulVec_mulVec, ih, hA_apply]
  have hApow : A ^ (2 ^ m) = 1 := by
    ext i j
    have h := hApow_mulVec (2 ^ m) (Pi.single j 1)
    rw [hm] at h
    simp only [LinearEquiv.coe_one, id_eq] at h
    have h2 := congrFun h i
    rw [Matrix.mulVec_single_one, Matrix.col_apply] at h2
    simpa [Pi.single_apply, Matrix.one_apply] using h2
  have hdetconj : (conjTr σ A).det = σ A.det := by
    rw [conjTr, Matrix.det_transpose]
    exact (RingHom.map_det (σ : K →+* K) A).symm
  have hσdet : σ A.det * A.det = 1 := by
    have h := congrArg Matrix.det huni
    rw [Matrix.det_mul, hdetconj, Matrix.det_one] at h
    exact h
  have hdetpow : A.det ^ (2 ^ m) = 1 := by
    have h := congrArg Matrix.det hApow
    rwa [Matrix.det_pow, Matrix.det_one] at h
  have hdet3 : A.det ^ 3 = 1 := by
    have h := hσdet
    rw [hσ2 A.det, ← pow_succ] at h
    simpa using h
  have hdet : A.det = 1 :=
    (pow_eq_one_iff_of_coprime (a := A.det) (m := 2 ^ m) (n := 3) hcop).mp
      ⟨hdetpow, hdet3⟩
  refine ⟨mkSU σ A hdet hAherm, ?_, ?_⟩
  · rw [mem_coordBlockSU_iff]
    intro i j hij
    change A i j = if i = j then 1 else 0
    exact hblock i j hij
  · apply LinearEquiv.ext
    intro v
    rw [suEndN_apply, mkSU_smul, hA_apply]

end CFSG.StandardType.QTwo

end
