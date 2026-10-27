module

public import CFSG.LocalAnalysis.StandardType.GGTPNI1TypeAHelp
public import CFSG.LocalAnalysis.StandardType.GGTPNI1TypeADvdBlock
public import CFSG.LocalAnalysis.StandardType.GGLabelRigid
public import CFSG.HardMathSupport.Solomon.Coordinator.LayerCentralFix
public import CFSG.LocalAnalysis.GLTheoremA.S12.CanonInnBridge
public import CFSG.Fischer.Classification.Recognition.Basic
public import CFSG.LocalAnalysis.StandardType.GGTableBTypeATransport
public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs
public import CFSG.LocalAnalysis.StandardType.Marking
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagOrder
public import CFSG.Quasithin.Background.B69Iso
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.LinearBlocks
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.LinearInner
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267GenPlaneClsLinBlock
public import CFSG.HardMathSupport.Solomon.LocalBalance.I1433.LinUnitLinear
public import CFSG.GroupTheory.Fitting.LayerProjection
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FSeitzB2
public import CFSG.GroupTheory.Fitting.LayerContainment
public import CFSG.LocalAnalysis.ComponentClassification.FittingNilpotence

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Matrix CFSG.RankThree.CALinearPlane CFSG.RankThree.CALinearPrimary
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple CFSG.RankThree.PartOne.KCPrimary

private theorem tptd_rawDatum_recipe {lab labL : LargeEvenLabel} {Q : LargeEvenRawCont}
    (hiso : GGLabelIso lab labL) (htag : labL.tag = .A) (hrank : 3 ≤ labL.rank)
    (hraw : LargeEvenRawDatum lab Q) :
    LargeEvenRecipeLinear (labL.rank + 1) (2 ^ labL.n) Q := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨tL, lL, nL⟩ := labL
  change tL = .A at htag
  change 3 ≤ lL at hrank
  subst tL
  rcases hiso with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8
  · rw [h1] at hraw
    simpa only [LargeEvenRawDatum] using hraw
  · exact absurd h2.2.1 (by simp)
  · obtain ⟨h3a, h3b⟩ := h3
    have hr3 : lL = 3 := congrArg LargeEvenLabel.rank h3b
    have hn : nL = n := congrArg LargeEvenLabel.n h3b
    rw [h3a] at hraw
    simp only [LargeEvenRawDatum] at hraw
    rw [hn, hr3]
    simpa using hraw
  · exact absurd (congrArg LargeEvenLabel.tag h4.2) (by simp)
  · exact absurd (congrArg LargeEvenLabel.tag h5.2) (by simp)
  · exact absurd (congrArg LargeEvenLabel.tag h6.2) (by simp)
  · have h1 : lL = 1 := by simpa using congrArg LargeEvenLabel.rank h7.2
    omega
  · exact absurd (congrArg LargeEvenLabel.tag h8.1) (by simp)

private theorem tptd_ggInducedAut_trans {X : Type} [Group X] {R R' : Type} [Group R] [Group R']
    (θ : X ⧸ Subgroup.center X ≃* R) (e : R ≃* R') (a : MulAut X) :
    ggInducedAut (θ.trans e) a = MulAut.congr e (ggInducedAut θ a) := by
  show MulAut.congr (θ.trans e) (centerQuotAut X a) =
    MulAut.congr e (MulAut.congr θ (centerQuotAut X a))
  rw [MulAut.congr_apply, MulAut.congr_apply, MulAut.congr_apply]
  ext x
  rfl

private theorem tptd_extract_model
    {L : Type} [Group L] [Finite L] {E : Subgroup (MulAut L)} {labL : LargeEvenLabel}
    (hlabL : LargeEvenInLambda2 labL) (htag : labL.tag = .A) (hrank : 3 ≤ labL.rank)
    (hhL : GGHasLabel labL (L ⧸ Subgroup.center L))
    (hmark : LargeEvenMarking L (fun _ _ _ I _ θ => GGInducedInn E θ I)) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K),
      Nat.card K = 2 ^ labL.n ∧
      ∃ θ : L ⧸ Subgroup.center L ≃* projectiveSL (labL.rank + 1) K,
        ∀ a ∈ E, ∃ B : GL (Fin (labL.rank + 1)) K,
          ∀ l : L, conjAut (labL.rank + 1) K B (θ (l : L ⧸ Subgroup.center L)) =
            θ ((a l : L) : L ⧸ Subgroup.center L) := by
  obtain ⟨-, lab, hlab, hraw⟩ := hmark
  have hhaslab : GGHasLabel lab (L ⧸ Subgroup.center L) :=
    largeEvenRawDatum_mono (fun R _ I F hq => by obtain ⟨-, -, θ, -⟩ := hq; exact ⟨θ⟩) hraw
  have hiso : GGLabelIso lab labL := ggLabelRigidInput_holds lab labL _ hlab hlabL hhaslab hhL
  have hrecipe : LargeEvenRecipeLinear (labL.rank + 1) (2 ^ labL.n)
      (fun R _ I F => IsSimpleGroup R ∧ (∃ a b : R, a * b ≠ b * a) ∧
        ∃ θ : L ⧸ Subgroup.center L ≃* R, GGInducedInn E θ I) :=
    tptd_rawDatum_recipe hiso htag hrank hraw
  simp only [LargeEvenRecipeLinear] at hrecipe
  obtain ⟨K, hFld, hFin, hK, hsimp, -, θ, hind⟩ := hrecipe
  refine ⟨K, hFld, hFin, hK, ?_⟩
  let e := TypeA.recipeEquiv (labL.rank + 1) K
  let θ' : L ⧸ Subgroup.center L ≃* projectiveSL (labL.rank + 1) K := θ.trans e
  refine ⟨θ', ?_⟩
  intro a ha
  have hmem : ggInducedAut θ a ∈
      LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin (labL.rank + 1)) K))
        Set.univ := hind a ha
  have hmem' : MulAut.congr e (ggInducedAut θ a) ∈
      Set.range (conjAut (labL.rank + 1) K) := TypeA.congr_recipeEquiv_mem hmem
  obtain ⟨B, hB⟩ := hmem'
  refine ⟨B, ?_⟩
  intro l
  have h1 := ggInducedAut_apply θ' a l
  rw [tptd_ggInducedAut_trans θ e a, ← hB] at h1
  exact h1

private theorem tptd_extract_model_lift
    {L : Type} [Group L] [Finite L] {E : Subgroup (MulAut L)} {labL : LargeEvenLabel}
    (hlabL : LargeEvenInLambda2 labL) (htag : labL.tag = .A) (hrank : 3 ≤ labL.rank)
    (hhL : GGHasLabel labL (L ⧸ Subgroup.center L))
    (hmark : LargeEvenMarking L (fun _ _ _ I _ θ => GGInducedInn E θ I))
    {p : ℕ} (hp : p.Prime) {y : MulAut L} (hy : y ∈ E) (hE : IsElemAbelian p E) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K),
      Nat.card K = 2 ^ labL.n ∧
      ∃ θ : L ⧸ Subgroup.center L ≃* projectiveSL (labL.rank + 1) K,
        (∀ a ∈ E, ∃ B : GL (Fin (labL.rank + 1)) K,
          ∀ l : L, conjAut (labL.rank + 1) K B (θ (l : L ⧸ Subgroup.center L)) =
            θ ((a l : L) : L ⧸ Subgroup.center L)) ∧
        ∃ g : GL (Fin (labL.rank + 1)) K,
          (∃ c : Kˣ, g ^ p = Matrix.GeneralLinearGroup.scalar (Fin (labL.rank + 1)) c) ∧
          ∀ l : L, conjAut (labL.rank + 1) K g (θ (l : L ⧸ Subgroup.center L)) =
            θ ((y l : L) : L ⧸ Subgroup.center L) := by
  obtain ⟨K, hFld, hFin, hK, θ, hθ⟩ :=
    tptd_extract_model (L := L) (E := E) (labL := labL) hlabL htag hrank hhL hmark
  refine ⟨K, hFld, hFin, hK, θ, hθ, ?_⟩
  obtain ⟨g, hg⟩ := hθ y hy
  refine ⟨g, ?_, hg⟩
  have hy_pow : y ^ p = 1 := hE.2 y hy
  have hconj : conjAut (labL.rank + 1) K g = ggInducedAut θ y := by
    ext x
    obtain ⟨z, rfl⟩ := θ.surjective x
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective z
    exact (hg l).trans (ggInducedAut_apply θ y l).symm
  have hconjpow : (conjAut (labL.rank + 1) K g) ^ p = 1 := by
    rw [hconj, ← map_pow, hy_pow, map_one]
  have hgpow : conjAut (labL.rank + 1) K (g ^ p) = 1 := by
    rw [map_pow, hconjpow]
  obtain ⟨c, hc⟩ :=
    (eq_one_of_conjAut_mul_fieldAut_eq_one (n := labL.rank + 1) (by omega) (g ^ p) 1
      (by rw [map_one, mul_one]; exact hgpow)).2
  exact ⟨c, hc.symm⟩

private theorem tptd_map_fixSubgroup_eq {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (α : MulAut G) (β : MulAut H) (h : MulAut.congr e α = β) :
    (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup α).map e.toMonoidHom =
      CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup β := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    change α x = x at hx
    change β (e x) = e x
    rw [← h]
    change e (α (e.symm (e x))) = e x
    rw [MulEquiv.symm_apply_apply, hx]
  · intro hy
    change β y = y at hy
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    change α (e.symm y) = e.symm y
    apply e.injective
    rw [MulEquiv.apply_symm_apply]
    change (MulAut.congr e α) y = y
    rw [h, hy]

private theorem tptd_component_transport {L : Type} [Group L] (hperf : commutator L = ⊤)
    {K : Type} [Field K] {d : ℕ} {θ : L ⧸ Subgroup.center L ≃* projectiveSL d K}
    {g : GL (Fin d) K} {y : MulAut L} {J : Subgroup L}
    (hcomp : IsComponentOf J (ggAutFixedSubgroup y))
    (hg : ∀ l : L, conjAut d K g (θ (l : L ⧸ Subgroup.center L)) =
      θ ((y l : L) : L ⧸ Subgroup.center L)) :
    IsComponentOf (J.map ((θ : L ⧸ Subgroup.center L →* projectiveSL d K).comp
        (QuotientGroup.mk' (Subgroup.center L))))
      (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup (conjAut d K g)) := by
  have hcomp' : CFSG.Open.IsComponentOf J
      (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup y) :=
    isComponentOf_iff_open.mp hcomp
  have hcomp₁ : CFSG.Open.IsComponentOf (J.map (QuotientGroup.mk' (Subgroup.center L)))
      (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup (centerQuotAut L y)) :=
    CFSG.LocalAnalysis.GLTheoremA.CanonInn.isComponentOf_map_centerQuot y hcomp'
  have hcomp₂ := CFSG.Fischer.Classification.Recognition.IsComponentOf.map_mulEquiv θ hcomp₁
  have hθ : ggInducedAut θ y = conjAut d K g := by
    ext x
    obtain ⟨z, rfl⟩ := θ.surjective x
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective z
    rw [ggInducedAut_apply]
    exact (hg l).symm
  have hfix : (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup (centerQuotAut L y)).map
      θ.toMonoidHom =
      CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup (conjAut d K g) := by
    rw [← hθ]
    exact tptd_map_fixSubgroup_eq θ (centerQuotAut L y) (ggInducedAut θ y) rfl
  rw [hfix] at hcomp₂
  rw [Subgroup.map_map] at hcomp₂
  exact isComponentOf_iff_open.mpr hcomp₂

private theorem tptd_block_numerics
    {K : Type} [Field K] [Finite K] [CharP K 2] {d p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hd : 4 ≤ d) (hf : Nat.card K = 2 ^ f)
    {g : GL (Fin d) K} {c : Kˣ}
    (hg : g ^ p = Matrix.GeneralLinearGroup.scalar (Fin d) c)
    {C : Subgroup (projectiveSL d K)}
    (hC : IsComponentOf C
      (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup (conjAut d K g)))
    {labJ : LargeEvenLabel} (hlabJ : LargeEvenInLambda2 labJ) (hlabJtag : labJ.tag = .A)
    (hlabJrank : labJ.rank = d - 2) (hlabJn : labJ.n = f)
    (hlabel : GGHasLabel labJ (↥C ⧸ Subgroup.center ↥C)) :
    ∃ h : Polynomial K, h.natDegree = 1 ∧
      h ∈ primaryFactors (glA g : Module.End K (Fin d → K)) ∧
      IsGoodFactor g h ∧
      primaryMultiplicity (glA g : Module.End K (Fin d → K)) h = d - 1 ∧
      C = (specialFactor g h).map (proj d K) :=
  tptdB_block_numerics hp hp2 hd hf hg hC hlabJ hlabJtag hlabJrank hlabJn hlabel

private theorem tptd_exists_specialFactor_not_fix
    {K : Type} [Field K] [Finite K] {d : ℕ} {g : GL (Fin d) K}
    (hsq : Squarefree (minpoly K (glA g : Module.End K (Fin d → K))))
    {h : Polynomial K} (hh : h ∈ primaryFactors (glA g : Module.End K (Fin d → K)))
    (hm : 2 ≤ primaryMultiplicity (glA g : Module.End K (Fin d → K)) h)
    {w : primaryComponent (glA g : Module.End K (Fin d → K)) h} (hw : w ≠ 0) :
    ∃ A ∈ specialFactor g h,
      (slGL d K A : Module.End K (Fin d → K)) (w : Fin d → K) ≠ (w : Fin d → K) := by
  classical
  haveI : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one (AdjoinRoot h) hw
  have hker_ne_bot : LinearMap.ker f ≠ ⊥ := by
    intro hbot
    have hinj : Function.Injective f := LinearMap.ker_eq_bot.mp hbot
    have hle : Module.finrank (AdjoinRoot h)
          (primaryComponent (glA g : Module.End K (Fin d → K)) h) ≤
        Module.finrank (AdjoinRoot h) (AdjoinRoot h) :=
      LinearMap.finrank_le_finrank_of_injective (R := AdjoinRoot h) hinj
    rw [Module.finrank_self] at hle
    have hm' : 2 ≤ Module.finrank (AdjoinRoot h)
        (primaryComponent (glA g : Module.End K (Fin d → K)) h) := hm
    omega
  obtain ⟨u, hu_mem, hu_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker_ne_bot
  have hfu : f u = 0 := LinearMap.mem_ker.mp hu_mem
  obtain ⟨g', hg'mem, hg'act⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.S267.Gen.exists_mem_linearSpecialBlock_transvection
      (k := K) (V := Fin d → K) (x := glA g) hsq hh hfu
  have hdet : LinearMap.det (g' : Module.End K (Fin d → K)) = 1 :=
    det_eq_one_of_mem_linearSpecialBlock hsq hh hg'mem
  obtain ⟨A, hA⟩ := mem_range_slGL hdet
  refine ⟨A, ?_, ?_⟩
  · rw [specialFactor, Subgroup.mem_comap, hA]; exact hg'mem
  · rw [hA, hg'act w, hf, one_smul]
    intro hcon
    have h3 : (w : Fin d → K) + (u : Fin d → K) = (w : Fin d → K) := by
      rw [← Submodule.coe_add]; exact hcon
    have h4 : (u : Fin d → K) = 0 := by
      have h3' : (w : Fin d → K) + (u : Fin d → K) = (w : Fin d → K) + 0 := by
        rw [add_zero]; exact h3
      exact add_left_cancel h3'
    exact hu_ne (Subtype.ext h4)

private theorem tptd_fixed_of_specialFactor_eq_zero
    {K : Type} [Field K] [Finite K] {d : ℕ} {g : GL (Fin d) K}
    (hsq : Squarefree (minpoly K (glA g : Module.End K (Fin d → K))))
    {h : Polynomial K} (hh : h ∈ primaryFactors (glA g : Module.End K (Fin d → K)))
    (hm : 2 ≤ primaryMultiplicity (glA g : Module.End K (Fin d → K)) h)
    {v : Fin d → K} (hv : v ∈ primaryComponent (glA g : Module.End K (Fin d → K)) h)
    (hfix : ∀ A ∈ specialFactor g h, (slGL d K A : Module.End K (Fin d → K)) v = v) :
    v = 0 := by
  by_contra hv0
  obtain ⟨A, hA, hAv⟩ := tptd_exists_specialFactor_not_fix hsq hh hm
    (w := ⟨v, hv⟩) (fun hc => hv0 (congrArg Subtype.val hc))
  exact hAv (hfix A hA)

private def tptd_IsBlockScalar {K : Type} [Field K] {d : ℕ} (g : GL (Fin d) K)
    (h : Polynomial K) (B : GL (Fin d) K) (c : AdjoinRoot h) : Prop :=
  ∀ w : primaryComponent (glA g : Module.End K (Fin d → K)) h,
    (glA B : Module.End K (Fin d → K)) (w : Fin d → K) =
      ((c • w : primaryComponent (glA g : Module.End K (Fin d → K)) h) : Fin d → K)

private def tptd_IsQuotientScalar {K : Type} [Field K] {d : ℕ} (g : GL (Fin d) K)
    (h : Polynomial K) (B : GL (Fin d) K) (δ : K) : Prop :=
  ∀ v : Fin d → K, (glA B : Module.End K (Fin d → K)) v - δ • v ∈
    primaryComponent (glA g : Module.End K (Fin d → K)) h

private theorem tptd_blockScalar_exists
    {K : Type} [Field K] [Finite K] {d : ℕ} {g : GL (Fin d) K} {h : Polynomial K}
    (hsq : Squarefree (minpoly K (glA g : Module.End K (Fin d → K))))
    (hh : h ∈ primaryFactors (glA g : Module.End K (Fin d → K)))
    (hm : 2 ≤ primaryMultiplicity (glA g : Module.End K (Fin d → K)) h)
    {B : GL (Fin d) K}
    (hcomm : ∀ g' ∈ linearSpecialBlock (glA g) h,
      (glA B : Module.End K (Fin d → K)) * g' = g' * (glA B : Module.End K (Fin d → K))) :
    ∃ c : AdjoinRoot h, tptd_IsBlockScalar g h B c := by
  have hm' : 2 ≤ Module.finrank (AdjoinRoot h)
      (primaryComponent (glA g : Module.End K (Fin d → K)) h) := hm
  obtain ⟨c, hc⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.S267.Gen.exists_smul_of_commute_linearSpecialBlock
      (x := glA g) hsq hh hm' ((glA B : Module.End K (Fin d → K)).toAddMonoidHom) (by
        intro g' hg' v
        exact congrArg (fun M : Module.End K (Fin d → K) => M v) (hcomm g' hg'))
  exact ⟨c, hc⟩

private theorem tptd_blockScalar_unique
    {K : Type} [Field K] {d : ℕ} {g : GL (Fin d) K} {h : Polynomial K} {B : GL (Fin d) K}
    [Fact (Irreducible h)]
    (hm : 2 ≤ primaryMultiplicity (glA g : Module.End K (Fin d → K)) h)
    {c c' : AdjoinRoot h} (hc : tptd_IsBlockScalar g h B c)
    (hc' : tptd_IsBlockScalar g h B c') : c = c' := by
  haveI : Nontrivial (primaryComponent (glA g : Module.End K (Fin d → K)) h) :=
    Module.nontrivial_of_finrank_pos (R := AdjoinRoot h)
      (show 0 < primaryMultiplicity (glA g : Module.End K (Fin d → K)) h from by omega)
  obtain ⟨w, hw⟩ := exists_ne (0 : primaryComponent (glA g : Module.End K (Fin d → K)) h)
  have h1 : c • w = c' • w := Subtype.ext ((hc w).symm.trans (hc' w))
  have h2 : (c - c') • w = 0 := by rw [sub_smul, h1, sub_self]
  by_contra hne
  have h3 : w = 0 := by
    calc w = (1 : AdjoinRoot h) • w := (one_smul _ w).symm
      _ = ((c - c')⁻¹ * (c - c')) • w := by rw [inv_mul_cancel₀ (sub_ne_zero.mpr hne)]
      _ = (c - c')⁻¹ • ((c - c') • w) := (smul_smul _ _ _).symm
      _ = 0 := by rw [h2, smul_zero]
  exact hw h3

private theorem tptd_blockScalar_mul
    {K : Type} [Field K] {d : ℕ} {g : GL (Fin d) K} {h : Polynomial K}
    {B₁ B₂ : GL (Fin d) K} {c₁ c₂ : AdjoinRoot h}
    (h₁ : tptd_IsBlockScalar g h B₁ c₁) (h₂ : tptd_IsBlockScalar g h B₂ c₂) :
    tptd_IsBlockScalar g h (B₁ * B₂) (c₁ * c₂) := by
  have hgl : (glA (B₁ * B₂) : Module.End K (Fin d → K)) =
      (glA B₁ : Module.End K (Fin d → K)) * (glA B₂ : Module.End K (Fin d → K)) :=
    congrArg (fun x : LinearMap.GeneralLinearGroup K (Fin d → K) =>
      (x : Module.End K (Fin d → K)))
      (map_mul (Matrix.GeneralLinearGroup.toLin : GL (Fin d) K ≃*
        LinearMap.GeneralLinearGroup K (Fin d → K)) B₁ B₂)
  intro w
  rw [hgl, Module.End.mul_apply, h₂ w, h₁ (c₂ • w)]
  exact congrArg Subtype.val (smul_smul c₁ c₂ w)

private theorem tptd_glA_scalar {K : Type} [Field K] {d : ℕ} (u : Kˣ) :
    (glA (Matrix.GeneralLinearGroup.scalar (Fin d) u) : Module.End K (Fin d → K)) =
      (u : K) • 1 := by
  ext v i
  simp [glA, Matrix.GeneralLinearGroup.toLin, Matrix.toLin'_apply,
    Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.mulVec_diagonal]

private theorem tptd_glA_mul {K : Type} [Field K] {d : ℕ} (B₁ B₂ : GL (Fin d) K) :
    (glA (B₁ * B₂) : Module.End K (Fin d → K)) =
      (glA B₁ : Module.End K (Fin d → K)) * (glA B₂ : Module.End K (Fin d → K)) :=
  congrArg (fun x : LinearMap.GeneralLinearGroup K (Fin d → K) =>
    (x : Module.End K (Fin d → K)))
    (map_mul (Matrix.GeneralLinearGroup.toLin : GL (Fin d) K ≃*
      LinearMap.GeneralLinearGroup K (Fin d → K)) B₁ B₂)

private theorem tptd_blockScalar_scalar_mul
    {K : Type} [Field K] {d : ℕ} {g : GL (Fin d) K} {h : Polynomial K}
    {B : GL (Fin d) K} {c : AdjoinRoot h} (u : Kˣ)
    (hb : tptd_IsBlockScalar g h B c) :
    tptd_IsBlockScalar g h (Matrix.GeneralLinearGroup.scalar (Fin d) u * B)
      (algebraMap K (AdjoinRoot h) (u : K) * c) := by
  intro w
  rw [tptd_glA_mul, Module.End.mul_apply, tptd_glA_scalar, LinearMap.smul_apply,
    Module.End.one_apply, hb w]
  have hcoe := CFSG.RankThree.PartOne.KCPrimary.coe_algebraMap_smul_primaryComponent
    (glA g : Module.End K (Fin d → K)) h (u : K) (c • w)
  rw [← hcoe, smul_smul]

private theorem tptd_quotientScalar_exists
    {K : Type} [Field K] [Finite K] {d : ℕ} {g : GL (Fin d) K} {h : Polynomial K}
    (hd : 1 ≤ d)
    (hsq : Squarefree (minpoly K (glA g : Module.End K (Fin d → K))))
    (hh : h ∈ primaryFactors (glA g : Module.End K (Fin d → K)))
    (hm : 2 ≤ primaryMultiplicity (glA g : Module.End K (Fin d → K)) h)
    (hfinVh : Module.finrank K (primaryComponent (glA g : Module.End K (Fin d → K)) h) = d - 1)
    {B : GL (Fin d) K}
    (hcomm : ∀ g' ∈ linearSpecialBlock (glA g) h,
      (glA B : Module.End K (Fin d → K)) * g' = g' * (glA B : Module.End K (Fin d → K))) :
    ∃ δ : K, tptd_IsQuotientScalar g h B δ := by
  let Vh : Submodule K (Fin d → K) := primaryComponent (glA g : Module.End K (Fin d → K)) h
  have hle : Vh ≤ Vh.comap (glA B : Module.End K (Fin d → K)) := by
    intro v hv
    exact CFSG.LocalAnalysis.GLTheoremA.S267.Gen.mem_primaryComponent_of_commute_linearSpecialBlock
      (x := glA g) hsq hh hm ((glA B : Module.End K (Fin d → K)).toAddMonoidHom)
      (fun g' hg' w => congrArg (fun M : Module.End K (Fin d → K) => M w) (hcomm g' hg')) hv
  let fB : (Fin d → K) ⧸ Vh →ₗ[K] (Fin d → K) ⧸ Vh :=
    Vh.mapQ Vh (glA B : Module.End K (Fin d → K)) hle
  have hfrQ : Module.finrank K ((Fin d → K) ⧸ Vh) = 1 := by
    have hfrV : Module.finrank K (Fin d → K) = d := Module.finrank_fin_fun (R := K) (n := d)
    have hfinVh' : Module.finrank K Vh = d - 1 := hfinVh
    have hsum := Submodule.finrank_quotient_add_finrank (R := K) (M := Fin d → K) Vh
    rw [hfinVh', hfrV] at hsum
    have hd' : d - 1 + 1 = d := Nat.sub_add_cancel hd
    have hsum' : (d - 1) + Module.finrank K ((Fin d → K) ⧸ Vh) = (d - 1) + 1 := by
      rw [add_comm (d - 1), hd']; exact hsum
    exact Nat.add_left_cancel hsum'
  have hne : Vh ≠ ⊤ := by
    intro htop
    have hfrV : Module.finrank K (Fin d → K) = d := Module.finrank_fin_fun (R := K) (n := d)
    have h1 : Module.finrank K Vh = d := by
      rw [htop]
      simpa using hfrV
    have hlt : d - 1 < d := Nat.sub_lt hd (by norm_num)
    have hfinVh' : Module.finrank K Vh = d - 1 := hfinVh
    omega
  obtain ⟨v0, -, hv0⟩ := SetLike.exists_of_lt (lt_top_iff_ne_top.mpr hne)
  let w0 : (Fin d → K) ⧸ Vh := Submodule.mkQ Vh v0
  have hw0 : w0 ≠ 0 := by
    intro hw
    have hker : v0 ∈ LinearMap.ker (Submodule.mkQ Vh) := LinearMap.mem_ker.mpr hw
    rw [Submodule.ker_mkQ] at hker
    exact hv0 hker
  obtain ⟨δ, hδ0⟩ := exists_smul_eq_of_finrank_eq_one hfrQ hw0 (fB w0)
  have hspan : Submodule.span K ({w0} : Set ((Fin d → K) ⧸ Vh)) = ⊤ :=
    (finrank_eq_one_iff_of_nonzero w0 hw0).mp hfrQ
  have hfB : ∀ y : (Fin d → K) ⧸ Vh, fB y = δ • y := by
    intro y
    have hy : y ∈ Submodule.span K ({w0} : Set ((Fin d → K) ⧸ Vh)) := by
      rw [hspan]; exact Submodule.mem_top
    rw [Submodule.mem_span_singleton] at hy
    obtain ⟨c, rfl⟩ := hy
    rw [map_smul, ← hδ0, smul_comm]
  refine ⟨δ, ?_⟩
  intro v
  have h1 : fB (Submodule.mkQ Vh v) =
      Submodule.mkQ Vh ((glA B : Module.End K (Fin d → K)) v) :=
    Submodule.mapQ_apply (p := Vh) (q := Vh)
      (f := (glA B : Module.End K (Fin d → K))) (h := hle) (x := v)
  have h2 : (Submodule.mkQ Vh) ((glA B : Module.End K (Fin d → K)) v - δ • v) = 0 := by
    rw [map_sub, map_smul, ← h1, hfB, sub_self]
  have hmem : (glA B : Module.End K (Fin d → K)) v - δ • v ∈ Vh := by
    rw [← Submodule.ker_mkQ (p := Vh), LinearMap.mem_ker]
    exact h2
  exact hmem

private theorem tptd_quotientScalar_unique
    {K : Type} [Field K] {d : ℕ} {g : GL (Fin d) K} {h : Polynomial K} {B : GL (Fin d) K}
    (hne : primaryComponent (glA g : Module.End K (Fin d → K)) h ≠ ⊤)
    {δ δ' : K} (hδ : tptd_IsQuotientScalar g h B δ)
    (hδ' : tptd_IsQuotientScalar g h B δ') : δ = δ' := by
  obtain ⟨v, -, hv⟩ := SetLike.exists_of_lt (lt_top_iff_ne_top.mpr hne)
  have h2 : (δ' - δ) • v ∈ primaryComponent (glA g : Module.End K (Fin d → K)) h := by
    have heq : (δ' - δ) • v = ((glA B : Module.End K (Fin d → K)) v - δ • v) -
        ((glA B : Module.End K (Fin d → K)) v - δ' • v) := by
      rw [sub_smul]; abel
    rw [heq]
    exact Submodule.sub_mem _ (hδ v) (hδ' v)
  by_contra hδne
  have h3 : v ∈ primaryComponent (glA g : Module.End K (Fin d → K)) h := by
    have hsub : (δ' - δ) ≠ 0 := sub_ne_zero.mpr (Ne.symm hδne)
    have h4 : v = (δ' - δ)⁻¹ • ((δ' - δ) • v) := by
      rw [smul_smul, inv_mul_cancel₀ hsub, one_smul]
    rw [h4]
    exact Submodule.smul_mem _ _ h2
  exact hv h3

private theorem tptd_quotientScalar_mul
    {K : Type} [Field K] {d : ℕ} {g : GL (Fin d) K} {h : Polynomial K}
    {B₁ B₂ : GL (Fin d) K} {δ₁ δ₂ : K}
    (h₁ : tptd_IsQuotientScalar g h B₁ δ₁) (h₂ : tptd_IsQuotientScalar g h B₂ δ₂) :
    tptd_IsQuotientScalar g h (B₁ * B₂) (δ₁ * δ₂) := by
  have hle₁ : ∀ v ∈ primaryComponent (glA g : Module.End K (Fin d → K)) h,
      (glA B₁ : Module.End K (Fin d → K)) v ∈
        primaryComponent (glA g : Module.End K (Fin d → K)) h := by
    intro v hv
    have hsum : (glA B₁ : Module.End K (Fin d → K)) v =
        δ₁ • v + ((glA B₁ : Module.End K (Fin d → K)) v - δ₁ • v) := by abel
    rw [hsum]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ hv) (h₁ v)
  intro v
  have hgoal : (glA (B₁ * B₂) : Module.End K (Fin d → K)) v - (δ₁ * δ₂) • v =
      δ₂ • ((glA B₁ : Module.End K (Fin d → K)) v - δ₁ • v) +
        (glA B₁ : Module.End K (Fin d → K)) ((glA B₂ : Module.End K (Fin d → K)) v - δ₂ • v) := by
    rw [tptd_glA_mul, Module.End.mul_apply]
    simp only [map_sub, map_smul, smul_sub, smul_smul]
    module
  rw [hgoal]
  exact Submodule.add_mem _ (Submodule.smul_mem _ δ₂ (h₁ v)) (hle₁ _ (h₂ v))

private theorem tptd_quotientScalar_scalar_mul
    {K : Type} [Field K] {d : ℕ} {g : GL (Fin d) K} {h : Polynomial K}
    {B : GL (Fin d) K} {δ : K} (u : Kˣ)
    (hb : tptd_IsQuotientScalar g h B δ) :
    tptd_IsQuotientScalar g h (Matrix.GeneralLinearGroup.scalar (Fin d) u * B)
      ((u : K) * δ) := by
  intro v
  have hgoal : (glA (Matrix.GeneralLinearGroup.scalar (Fin d) u * B) :
        Module.End K (Fin d → K)) v - ((u : K) * δ) • v =
      (u : K) • ((glA B : Module.End K (Fin d → K)) v - δ • v) := by
    rw [tptd_glA_mul, Module.End.mul_apply, tptd_glA_scalar]
    simp only [LinearMap.smul_apply, Module.End.one_apply]
    module
  rw [hgoal]
  exact Submodule.smul_mem _ _ (hb v)

private theorem tptd_eq_scalar_of_scalars_eq
    {K : Type} [Field K] [Finite K] {d : ℕ} {g : GL (Fin d) K} {h : Polynomial K}
    (hsq : Squarefree (minpoly K (glA g : Module.End K (Fin d → K))))
    (hh : h ∈ primaryFactors (glA g : Module.End K (Fin d → K)))
    (hm : 2 ≤ primaryMultiplicity (glA g : Module.End K (Fin d → K)) h)
    {B : GL (Fin d) K}
    (hcommF : ∀ A ∈ specialFactor g h,
      B * Matrix.SpecialLinearGroup.toGL A = Matrix.SpecialLinearGroup.toGL A * B)
    {c : AdjoinRoot h} (hc : tptd_IsBlockScalar g h B c)
    {δ : K} (hδ : tptd_IsQuotientScalar g h B δ)
    (hcd : c = algebraMap K (AdjoinRoot h) δ) :
    (glA B : Module.End K (Fin d → K)) = δ • 1 := by
  let N : Module.End K (Fin d → K) := (glA B : Module.End K (Fin d → K)) - δ • 1
  have hNapply : ∀ v : Fin d → K,
      N v = (glA B : Module.End K (Fin d → K)) v - δ • v := fun v => rfl
  have hNmem : ∀ v : Fin d → K,
      N v ∈ primaryComponent (glA g : Module.End K (Fin d → K)) h := by
    intro v
    rw [hNapply v]
    exact hδ v
  have hNzero : ∀ w ∈ primaryComponent (glA g : Module.End K (Fin d → K)) h, N w = 0 := by
    intro w hw
    have h1 := hc ⟨w, hw⟩
    rw [hcd] at h1
    rw [hNapply w, h1,
      CFSG.RankThree.PartOne.KCPrimary.coe_algebraMap_smul_primaryComponent
        (glA g : Module.End K (Fin d → K)) h δ ⟨w, hw⟩, sub_self]
  have hNcomm : ∀ A ∈ specialFactor g h,
      N * (slGL d K A : Module.End K (Fin d → K)) =
        (slGL d K A : Module.End K (Fin d → K)) * N := by
    intro A hA
    have hcommA : (glA B : Module.End K (Fin d → K)) *
        (slGL d K A : Module.End K (Fin d → K)) =
        (slGL d K A : Module.End K (Fin d → K)) *
          (glA B : Module.End K (Fin d → K)) := by
      have h := congrArg (fun X : GL (Fin d) K => (glA X : Module.End K (Fin d → K)))
        (hcommF A hA)
      rwa [tptd_glA_mul, tptd_glA_mul] at h
    have hscalar_comm : (δ • (1 : Module.End K (Fin d → K))) *
        (slGL d K A : Module.End K (Fin d → K)) =
        (slGL d K A : Module.End K (Fin d → K)) *
          (δ • (1 : Module.End K (Fin d → K))) := by
      rw [smul_mul_assoc, one_mul, mul_smul_comm, mul_one]
    show ((glA B : Module.End K (Fin d → K)) - δ • 1) *
        (slGL d K A : Module.End K (Fin d → K)) =
        (slGL d K A : Module.End K (Fin d → K)) *
          ((glA B : Module.End K (Fin d → K)) - δ • 1)
    rw [sub_mul, mul_sub, hcommA, hscalar_comm]
  have hfixed : ∀ v : Fin d → K, N v = 0 := by
    intro v
    refine tptd_fixed_of_specialFactor_eq_zero (K := K) (d := d) (g := g) hsq hh hm
      (hNmem v) ?_
    intro A hA
    have hsub : (slGL d K A : Module.End K (Fin d → K)) v - v ∈
        primaryComponent (glA g : Module.End K (Fin d → K)) h := by
      refine CFSG.LocalAnalysis.GLTheoremA.S267.Gen.sub_mem_primaryComponent_of_mem_linearSpecialBlock
        (x := glA g) hsq hh ?_ v
      rw [specialFactor, Subgroup.mem_comap] at hA
      exact hA
    have h1 : N ((slGL d K A : Module.End K (Fin d → K)) v) =
        (slGL d K A : Module.End K (Fin d → K)) (N v) := by
      have := congrArg (fun M : Module.End K (Fin d → K) => M v) (hNcomm A hA)
      simpa only [Module.End.mul_apply] using this
    calc (slGL d K A : Module.End K (Fin d → K)) (N v)
        = N ((slGL d K A : Module.End K (Fin d → K)) v) := h1.symm
      _ = N (((slGL d K A : Module.End K (Fin d → K)) v - v) + v) := by
            rw [sub_add_cancel]
      _ = N ((slGL d K A : Module.End K (Fin d → K)) v - v) + N v := by rw [map_add]
      _ = 0 + N v := by rw [hNzero _ hsub]
      _ = N v := by rw [zero_add]
  have hN0 : N = 0 := LinearMap.ext hfixed
  have : (glA B : Module.End K (Fin d → K)) - δ • 1 = 0 := hN0
  exact sub_eq_zero.mp this

private theorem tptd_cyclic_centralizer
    {K : Type} [Field K] [Finite K] {d p : ℕ} (hp : p.Prime) (hd : 4 ≤ d)
    {g : GL (Fin d) K}
    (hsq : Squarefree (minpoly K (glA g : Module.End K (Fin d → K))))
    {h : Polynomial K} (hh : h ∈ primaryFactors (glA g : Module.End K (Fin d → K)))
    (hdeg : h.natDegree = 1)
    (hmult : primaryMultiplicity (glA g : Module.End K (Fin d → K)) h = d - 1)
    {C : Subgroup (projectiveSL d K)}
    (hC : C = (specialFactor g h).map (proj d K))
    {H : Subgroup (MulAut (projectiveSL d K))} (hH : IsElemAbelian p H)
    (hfix : ∀ a ∈ H, ∀ x ∈ C, a x = x)
    (hinner : ∀ a ∈ H, ∃ B : GL (Fin d) K, a = conjAut d K B) :
    Nat.card H ≤ p := by
  classical
  haveI : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
  have hm : 2 ≤ primaryMultiplicity (glA g : Module.End K (Fin d → K)) h := by
    rw [hmult]; omega
  have hgood : IsGoodFactor g h := Or.inl (by rw [hmult]; omega)
  have hperf : ⁅specialFactor g h, specialFactor g h⁆ = specialFactor g h := by
    haveI := (isQuasisimple_specialFactor (A := g) hsq hh hgood).1
    exact CFSG.GroupTheory.commutator_eq_self_of_isPerfect_subgroup
  have hfin : Module.finrank K (primaryComponent (glA g : Module.End K (Fin d → K)) h) = d - 1 := by
    rw [CFSG.RankThree.PartOne.KCPrimary.finrank_primaryComponent, hdeg]
    change 1 * primaryMultiplicity (glA g : Module.End K (Fin d → K)) h = d - 1
    rw [hmult]; ring
  have hVh_ne_top : primaryComponent (glA g : Module.End K (Fin d → K)) h ≠ ⊤ := by
    intro htop
    have h1 : Module.finrank K (primaryComponent (glA g : Module.End K (Fin d → K)) h) = d := by
      rw [htop, finrank_top]
      exact Module.finrank_fin_fun (R := K) (n := d)
    omega
  haveI : Nontrivial (primaryComponent (glA g : Module.End K (Fin d → K)) h) :=
    Module.nontrivial_of_finrank_pos (R := AdjoinRoot h)
      (show 0 < primaryMultiplicity (glA g : Module.End K (Fin d → K)) h from by omega)
  haveI : Finite (AdjoinRoot h) := by
    haveI : Module.Finite K (AdjoinRoot h) :=
      (AdjoinRoot.powerBasis (monic_of_mem_primaryFactors hh).ne_zero).finite
    exact Module.finite_of_finite K
  have hAlgNe : ∀ x : K, x ≠ 0 → algebraMap K (AdjoinRoot h) x ≠ 0 := by
    intro x hx
    simpa using (algebraMap K (AdjoinRoot h)).injective.ne hx
  let H' : Subgroup (GL (Fin d) K) := Subgroup.comap (conjAut d K) H
  have hcommF_of_mem : ∀ B ∈ H', ∀ A ∈ specialFactor g h,
      B * Matrix.SpecialLinearGroup.toGL A = Matrix.SpecialLinearGroup.toGL A * B := by
    intro B hB A hA
    have hBH : conjAut d K B ∈ H := Subgroup.mem_comap.mp hB
    refine (CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433.LinearCore.commute_of_fixes_proj
      (specialFactor g h) hperf B ?_) A hA
    intro f hf
    have hCf : proj d K f ∈ C := by
      rw [hC]; exact Subgroup.mem_map_of_mem (proj d K) hf
    exact hfix (conjAut d K B) hBH (proj d K f) hCf
  have hcommBlock_of_mem : ∀ B ∈ H', ∀ A ∈ linearSpecialBlock (glA g) h,
      (glA B : Module.End K (Fin d → K)) * A = A * (glA B : Module.End K (Fin d → K)) := by
    intro B hB A hA
    have h := (CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433.LinearCore.commute_specialBlock_of_specialFactor
      hsq hh (hcommF_of_mem B hB)) A hA
    exact congrArg (fun X : LinearMap.GeneralLinearGroup K (Fin d → K) =>
      (X : Module.End K (Fin d → K))) h
  have hlifts : ∀ a : H, ∃ B : GL (Fin d) K, a.1 = conjAut d K B := fun a => hinner a.1 a.2
  let lift : H → GL (Fin d) K := fun a => Classical.choose (hlifts a)
  have lift_spec : ∀ a : H, a.1 = conjAut d K (lift a) :=
    fun a => Classical.choose_spec (hlifts a)
  have lift_mem : ∀ a : H, lift a ∈ H' := by
    intro a
    change conjAut d K (lift a) ∈ H
    rw [← lift_spec a]; exact a.2
  have hblock_exists : ∀ a : H, ∃ c : AdjoinRoot h, tptd_IsBlockScalar g h (lift a) c :=
    fun a => tptd_blockScalar_exists (K := K) (d := d) (g := g) (h := h) hsq hh hm
      (hcommBlock_of_mem (lift a) (lift_mem a))
  let ca : H → AdjoinRoot h := fun a => Classical.choose (hblock_exists a)
  have ca_spec : ∀ a : H, tptd_IsBlockScalar g h (lift a) (ca a) :=
    fun a => Classical.choose_spec (hblock_exists a)
  have hquot_exists : ∀ a : H, ∃ δ : K, tptd_IsQuotientScalar g h (lift a) δ :=
    fun a => tptd_quotientScalar_exists (K := K) (d := d) (g := g) (h := h) (by omega) hsq hh hm
      hfin (hcommBlock_of_mem (lift a) (lift_mem a))
  let da : H → K := fun a => Classical.choose (hquot_exists a)
  have da_spec : ∀ a : H, tptd_IsQuotientScalar g h (lift a) (da a) :=
    fun a => Classical.choose_spec (hquot_exists a)
  have hblock_one : tptd_IsBlockScalar g h (1 : GL (Fin d) K) 1 := by
    intro w
    show (glA (1 : GL (Fin d) K) : Module.End K (Fin d → K)) (w : Fin d → K) =
      ((1 : AdjoinRoot h) • w : primaryComponent (glA g : Module.End K (Fin d → K)) h)
    rw [one_smul]
    simp
  have hquot_one : tptd_IsQuotientScalar g h (1 : GL (Fin d) K) 1 := by
    intro v
    simp [tptd_IsQuotientScalar]
  have ca_ne_zero : ∀ a : H, ca a ≠ 0 := by
    intro a h0
    obtain ⟨w, hw⟩ := exists_ne (0 : primaryComponent (glA g : Module.End K (Fin d → K)) h)
    have hwco : (w : Fin d → K) ≠ 0 := fun h => hw (Subtype.ext h)
    have h1 : (glA (lift a) : Module.End K (Fin d → K)) (w : Fin d → K) = 0 := by
      rw [ca_spec a w, h0, zero_smul]
      rfl
    have hinv : (glA ((lift a)⁻¹) : Module.End K (Fin d → K))
        ((glA (lift a) : Module.End K (Fin d → K)) (w : Fin d → K)) = (w : Fin d → K) := by
      rw [← Module.End.mul_apply, ← tptd_glA_mul]
      simp
    rw [h1, map_zero] at hinv
    exact hwco hinv.symm
  have da_ne_zero : ∀ a : H, da a ≠ 0 := by
    intro a h0
    apply hVh_ne_top
    rw [Submodule.eq_top_iff']
    intro v
    have h1 : (glA (lift a) : Module.End K (Fin d → K))
        ((glA ((lift a)⁻¹) : Module.End K (Fin d → K)) v) ∈
        primaryComponent (glA g : Module.End K (Fin d → K)) h := by
      have h := da_spec a ((glA ((lift a)⁻¹) : Module.End K (Fin d → K)) v)
      rwa [h0, zero_smul, sub_zero] at h
    have h2 : (glA (lift a) : Module.End K (Fin d → K))
        ((glA ((lift a)⁻¹) : Module.End K (Fin d → K)) v) = v := by
      rw [← Module.End.mul_apply, ← tptd_glA_mul]
      simp
    rwa [h2] at h1
  have scalar_rel : ∀ a b : H, ∃ u : Kˣ,
      lift (a * b) = Matrix.GeneralLinearGroup.scalar (Fin d) u * (lift a * lift b) ∧
      ca (a * b) = algebraMap K (AdjoinRoot h) (u : K) * (ca a * ca b) ∧
      da (a * b) = (u : K) * (da a * da b) := by
    intro a b
    have hker : conjAut d K ((lift a * lift b)⁻¹ * lift (a * b)) = 1 := by
      rw [map_mul, map_inv, map_mul,
        show conjAut d K (lift (a * b)) = (a * b).1 from (lift_spec (a * b)).symm,
        show conjAut d K (lift a) = a.1 from (lift_spec a).symm,
        show conjAut d K (lift b) = b.1 from (lift_spec b).symm,
        Subgroup.coe_mul, inv_mul_cancel]
    obtain ⟨-, u, hu⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one (K := K) (n := d) (by omega)
      ((lift a * lift b)⁻¹ * lift (a * b)) 1 (by rw [map_one, mul_one]; exact hker)
    have hlift : lift (a * b) =
        Matrix.GeneralLinearGroup.scalar (Fin d) u * (lift a * lift b) := by
      have h1 : (lift a * lift b) * Matrix.GeneralLinearGroup.scalar (Fin d) u = lift (a * b) := by
        rw [hu]; group
      rw [Matrix.GeneralLinearGroup.scalar_commute u (lift a * lift b)]
      exact h1.symm
    have hca : ca (a * b) = algebraMap K (AdjoinRoot h) (u : K) * (ca a * ca b) := by
      have hscalar : tptd_IsBlockScalar g h
          (Matrix.GeneralLinearGroup.scalar (Fin d) u * (lift a * lift b))
          (algebraMap K (AdjoinRoot h) (u : K) * (ca a * ca b)) :=
        tptd_blockScalar_scalar_mul (g := g) (h := h) u
          (tptd_blockScalar_mul (g := g) (h := h) (ca_spec a) (ca_spec b))
      rw [← hlift] at hscalar
      exact tptd_blockScalar_unique (B := lift (a * b)) hm (ca_spec (a * b)) hscalar
    have hda : da (a * b) = (u : K) * (da a * da b) := by
      have hscalar : tptd_IsQuotientScalar g h
          (Matrix.GeneralLinearGroup.scalar (Fin d) u * (lift a * lift b))
          ((u : K) * (da a * da b)) :=
        tptd_quotientScalar_scalar_mul (g := g) (h := h) u
          (tptd_quotientScalar_mul (g := g) (h := h) (da_spec a) (da_spec b))
      rw [← hlift] at hscalar
      exact tptd_quotientScalar_unique (B := lift (a * b)) hVh_ne_top (da_spec (a * b)) hscalar
    exact ⟨u, hlift, hca, hda⟩
  let Uc : H → (AdjoinRoot h)ˣ := fun a => Units.mk0 (ca a) (ca_ne_zero a)
  let Ud : H → (AdjoinRoot h)ˣ := fun a =>
    Units.mk0 (algebraMap K (AdjoinRoot h) (da a)) (hAlgNe (da a) (da_ne_zero a))
  let Ψfun : H → (AdjoinRoot h)ˣ := fun a => Uc a * (Ud a)⁻¹
  have Ψ_mul : ∀ a b : H, Ψfun (a * b) = Ψfun a * Ψfun b := by
    intro a b
    obtain ⟨u, hlift, hca, hda⟩ := scalar_rel a b
    apply Units.ext
    show ca (a * b) * (algebraMap K (AdjoinRoot h) (da (a * b)))⁻¹ =
      (ca a * (algebraMap K (AdjoinRoot h) (da a))⁻¹) *
        (ca b * (algebraMap K (AdjoinRoot h) (da b))⁻¹)
    rw [hca, hda]
    simp only [map_mul]
    have hA_ne : algebraMap K (AdjoinRoot h) (u : K) ≠ 0 := hAlgNe (u : K) (Units.ne_zero u)
    have hDa_ne : algebraMap K (AdjoinRoot h) (da a) ≠ 0 := hAlgNe (da a) (da_ne_zero a)
    have hDb_ne : algebraMap K (AdjoinRoot h) (da b) ≠ 0 := hAlgNe (da b) (da_ne_zero b)
    field_simp [hA_ne, hDa_ne, hDb_ne]
  have Ψ_one : Ψfun 1 = 1 := by
    obtain ⟨μ, hμ⟩ : ∃ μ : Kˣ, lift 1 = Matrix.GeneralLinearGroup.scalar (Fin d) μ := by
      have h : conjAut d K (lift 1) = 1 := by
        rw [← lift_spec (1 : H)]; rfl
      obtain ⟨-, μ, hμ⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one (K := K) (n := d) (by omega)
        (lift 1) 1 (by rw [map_one, mul_one]; exact h)
      exact ⟨μ, hμ.symm⟩
    have hca1 : ca 1 = algebraMap K (AdjoinRoot h) (μ : K) := by
      have h1 : tptd_IsBlockScalar g h (lift 1) (algebraMap K (AdjoinRoot h) (μ : K)) := by
        rw [hμ]
        simpa using tptd_blockScalar_scalar_mul (g := g) (h := h) μ hblock_one
      exact tptd_blockScalar_unique (B := lift 1) hm (ca_spec 1) h1
    have hda1 : da 1 = (μ : K) := by
      have h1 : tptd_IsQuotientScalar g h (lift 1) ((μ : K) * 1) := by
        rw [hμ]
        simpa using tptd_quotientScalar_scalar_mul (g := g) (h := h) μ hquot_one
      exact tptd_quotientScalar_unique (B := lift 1) hVh_ne_top (da_spec 1) (by simpa using h1)
    apply Units.ext
    rw [Units.val_mul, Units.val_inv_eq_inv_val]
    change ca 1 * (algebraMap K (AdjoinRoot h) (da 1))⁻¹ = 1
    rw [hca1, hda1]
    exact mul_inv_cancel₀ (hAlgNe (μ : K) (Units.ne_zero μ))
  let Ψ : H →* (AdjoinRoot h)ˣ :=
    { toFun := Ψfun
      map_one' := Ψ_one
      map_mul' := Ψ_mul }
  have Ψ_eq_one : ∀ a : H, Ψ a = 1 → a = 1 := by
    intro a ha
    have hca_eq : ca a = algebraMap K (AdjoinRoot h) (da a) := by
      have hco : Ψfun a = 1 := ha
      have h2 := congrArg (fun u : (AdjoinRoot h)ˣ => (u : AdjoinRoot h)) hco
      have h' : ca a * (algebraMap K (AdjoinRoot h) (da a))⁻¹ = 1 := by
        simpa only [Ψfun, Uc, Ud, Units.val_mul, Units.val_inv_eq_inv_val,
          Units.val_mk0, Units.val_one] using h2
      exact (eq_inv_of_mul_eq_one_left h').trans (inv_inv _)
    have hscal := tptd_eq_scalar_of_scalars_eq (K := K) (d := d) (g := g) (h := h)
      hsq hh hm (hcommF_of_mem (lift a) (lift_mem a)) (ca_spec a) (da_spec a) hca_eq
    have hlift : lift a =
        Matrix.GeneralLinearGroup.scalar (Fin d) (Units.mk0 (da a) (da_ne_zero a)) := by
      apply Matrix.GeneralLinearGroup.toLin.injective
      apply (LinearMap.GeneralLinearGroup.generalLinearEquiv K (Fin d → K)).injective
      apply LinearEquiv.toLinearMap_injective
      show (glA (lift a) : Module.End K (Fin d → K)) =
        (glA (Matrix.GeneralLinearGroup.scalar (Fin d) (Units.mk0 (da a) (da_ne_zero a))) :
          Module.End K (Fin d → K))
      rw [hscal, tptd_glA_scalar]
      simp
    apply Subtype.ext
    rw [lift_spec a, hlift]
    exact conjAut_scalar (Units.mk0 (da a) (da_ne_zero a))
  have Ψ_inj : Function.Injective Ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, Subgroup.eq_bot_iff_forall]
    intro a ha
    exact Ψ_eq_one a (MonoidHom.mem_ker.mp ha)
  haveI : IsCyclic (AdjoinRoot h)ˣ := instIsCyclicUnitsOfFinite
  have hcyc : IsCyclic H := isCyclic_of_injective Ψ Ψ_inj
  exact TableB.card_le_of_isCyclic hp.pos hcyc hH.2

theorem ggI1PairRankOn_TypeA_dvd
    : GGI1PairRankOn fun p labL labJ => GGPairTypeA p labL labJ ∧ p ∣ labL.rank + 1 := by
  intro p hp hp2 L _ _ J y E labL labJ hlabL hlabJ hP hhL hhJ hy1 hyE hE hcomp hfix hmark
  obtain ⟨hAtag, hrank, hn, hpdiv, hlabJeq⟩ := hP.1
  obtain ⟨K, hFld, hFin, hK, θ, hModel, g, hgscalar, hgy⟩ :=
    tptd_extract_model_lift (L := L) (E := E) (labL := labL) hlabL hAtag hrank hhL hmark
      hp hyE hE
  let ψ : L →* projectiveSL (labL.rank + 1) K :=
    (θ : L ⧸ Subgroup.center L →* projectiveSL (labL.rank + 1) K).comp
      (QuotientGroup.mk' (Subgroup.center L))
  let C : Subgroup (projectiveSL (labL.rank + 1) K) := J.map ψ
  have hCcomp : IsComponentOf C
      (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup (conjAut (labL.rank + 1) K g)) :=
    tptd_component_transport hmark.1 (J := J) (θ := θ) (g := g) (y := y) hcomp hgy
  have hlabelC : GGHasLabel labJ (↥C ⧸ Subgroup.center ↥C) := by
    have hperfJ : Group.IsPerfect ↥J := ⟨hcomp.2.2.1⟩
    have hkerψ : ψ.ker = Subgroup.center L := by
      ext l
      rw [MonoidHom.mem_ker]
      show θ (QuotientGroup.mk' (Subgroup.center L) l) = 1 ↔ l ∈ Subgroup.center L
      rw [← map_one θ, θ.injective.eq_iff]
      exact QuotientGroup.eq_one_iff l
    have hker : (ψ.subgroupMap J).ker ≤ Subgroup.center ↥J := by
      intro j hj
      have hj' : ψ (j : L) = 1 := by
        have h1 := congrArg Subtype.val hj
        rw [MonoidHom.subgroupMap_apply_coe] at h1
        simpa using h1
      have hjZ : (j : L) ∈ Subgroup.center L := by
        rw [← hkerψ]; exact hj'
      rw [Subgroup.mem_center_iff]
      intro k
      apply Subtype.ext
      exact Subgroup.mem_center_iff.mp hjZ (k : L)
    obtain ⟨e⟩ := CFSG.LocalAnalysis.GLTheoremA.Y10F.quotEquiv_of_perfect_central
      (ψ.subgroupMap J) (ψ.subgroupMap_surjective J) hperfJ hker
    exact ggHasLabel_of_mulEquiv e hhJ
  haveI hcharK : CharP K 2 := by
    haveI : Fintype K := Fintype.ofFinite K
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact charP_of_card_eq_prime_pow (p := 2) (f := labL.n) (by
      rw [← Nat.card_eq_fintype_card]; exact hK)
  have hd4 : 4 ≤ labL.rank + 1 := by omega
  obtain ⟨c, hc⟩ := hgscalar
  obtain ⟨h, hdeg, hh, hgood, hmult, hCeq⟩ :=
    tptd_block_numerics (K := K) (d := labL.rank + 1) (p := p) (f := labL.n)
      hp hp2 hd4 hK hc hCcomp hlabJ (by rw [hlabJeq])
        (by rw [hlabJeq]; show labL.rank - 1 = labL.rank + 1 - 2; omega)
        (by rw [hlabJeq]) hlabelC
  have hpk : (p : K) ≠ 0 := by
    intro h0
    have h2dvd : 2 ∣ p := (CharP.cast_eq_zero_iff K 2 p).mp h0
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h2dvd).symm
  have hsq : Squarefree (minpoly K (glA g : Module.End K (Fin (labL.rank + 1) → K))) :=
    squarefree_minpoly_glA (k := K) (n := labL.rank + 1) (p := p) hpk hc
  have hH : IsElemAbelian p (E.map (ggInducedAut θ)) :=
    tpta_isElemAbelian_map_ggInducedAut θ hE
  have hfixH : ∀ a ∈ E.map (ggInducedAut θ), ∀ x ∈ C, a x = x := by
    intro a ha x hx
    obtain ⟨e', he', rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨j, hj, hxj⟩ := Subgroup.mem_map.mp hx
    rw [← hxj]
    show ggInducedAut θ e' (θ (QuotientGroup.mk' (Subgroup.center L) j)) =
      θ (QuotientGroup.mk' (Subgroup.center L) j)
    rw [QuotientGroup.mk'_apply, ggInducedAut_apply, hfix e' he' j hj]
  have hinnerH : ∀ a ∈ E.map (ggInducedAut θ), ∃ B : GL (Fin (labL.rank + 1)) K,
      a = conjAut (labL.rank + 1) K B := by
    intro a ha
    obtain ⟨e', he', rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨B, hB⟩ := hModel e' he'
    refine ⟨B, ?_⟩
    ext x
    obtain ⟨z, rfl⟩ := θ.surjective x
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective z
    rw [ggInducedAut_apply, hB l]
  have hcardH : Nat.card (E.map (ggInducedAut θ)) ≤ p :=
    tptd_cyclic_centralizer (K := K) (d := labL.rank + 1) (p := p) hp hd4 hsq hh hdeg hmult
      hCeq hH hfixH hinnerH
  have hcardE : Nat.card E ≤ p := by
    have hinj : Function.Injective
        (ggInducedAut θ : MulAut L → MulAut (projectiveSL (labL.rank + 1) K)) :=
      ggInducedAut_injective_of_perfect hmark.1 θ
    have hmap := Subgroup.card_map_of_injective
      (K := E) (f := (ggInducedAut θ : MulAut L →* MulAut (projectiveSL (labL.rank + 1) K))) hinj
    rw [← hmap]
    exact hcardH
  exact le_of_eq (tpta_eq_zpowers_of_card_le hp hyE hy1 hE hcardE)

end CFSG.StandardType

end
