module

public import CFSG.LocalAnalysis.StandardType.GGTwE6SCFourModel
public import CFSG.LocalAnalysis.StandardType.GGLieM6cDescent
public import CFSG.LocalAnalysis.StandardType.GGTwE6SCFourCover
public import CFSG.LieType.AlgebraicGroups.ConnectedCentralizerReflection
public import CFSG.LieType.AlgebraicGroups.AdjointCentralizerComponentsThree
public import CFSG.LocalAnalysis.StandardType.GGForkJrPumpDefs
public import CFSG.LocalAnalysis.StandardType.GGReflectionBasic
public import CFSG.LocalAnalysis.StandardType.GGE6NonToralCentralizerTorus
public import CFSG.LocalAnalysis.StandardType.GGE6NegativeCyclic
public import CFSG.LieType.AlgebraicGroups.TorusCentralizerMaximal
public import CFSG.LieType.AlgebraicGroups.ReductiveFixedComponentsThree
public import CFSG.LieType.AlgebraicGroups.FixedComponentCentralIsogeny
public import CFSG.LieType.AlgebraicGroups.FixedComponentProduct
public import CFSG.LieType.AlgebraicGroups.FixedComponentSmooth
public import CFSG.LieType.AlgebraicGroups.CoordinateConjugation
public import CFSG.LieType.AlgebraicGroups.MatrixFixedComponentsThree
public import CFSG.LieType.AlgebraicGroups.InnerCoordinateConjugation
public import CFSG.LieType.AlgebraicGroups.MatrixFixedIdentityComponent
public import CFSG.LieType.AlgebraicGroups.ReductiveFixedCoverData
public import CFSG.LieType.AlgebraicGroups.FixedTorusReductive
public import CFSG.LieType.AlgebraicGroups.ReductiveDescent
public import TauCeti.Algebra.AlgebraicGroup.Reductive.Product
public import TauCeti.Algebra.AlgebraicGroup.Reductive.Basic
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LieType.AlgebraicGroups.ClosedIdentityComponentFunctorial
public import CFSG.LieType.AlgebraicGroups.FiniteNormalizerComponentAction
public import CFSG.LieType.AlgebraicGroups.ConnectedMatrixCentralizer
import CFSG.GroupTheory.OddKernelImage

public noncomputable section
namespace CFSG.StandardType.SCFourCover
open Subgroup CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.StandardType.NoOffTwE6Three CFSG.RankThree.Classical2
  CFSG.RankThree.PartOne.KE
  CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Lang.E6Descent
  CFSG.LieType.AlgebraicGroups

section Matrix

variable
  {n : ℕ} {K : Type} [Field K] (σ : K ≃+* K) {Ω : Type} [Field Ω] [Algebra K Ω]
  (ε : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) ≃* TwE6Delta.RecipeR K n)
  {L' : Type} [Group L'] {ψ : L' →* TwE6Delta.RecipeR K n}

@[expose] noncomputable def recipeMatrixHom : L' →* ModGL Tag.E6 Ω :=
  (baseChangeGL (τ := Tag.E6) (algebraMap K Ω)).comp
    ((graphFixedRootGroup TwistTag.E6 K σ.toRingHom).subtype.comp
      (ε.symm.toMonoidHom.comp ψ))

theorem recipeMatrixHom_apply (x : L') :
    recipeMatrixHom σ ε (ψ := ψ) x =
      baseChangeGL (τ := Tag.E6) (algebraMap K Ω) (ε.symm (ψ x)).1 := rfl

end Matrix


variable {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ n) ^ 2)
  (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n) {Ω : Type} [Field Ω] [Algebra K Ω]
  [IsAlgClosure K Ω] (Fr : Ω →+* Ω) (hFr : ∀ c, Fr c = c ^ 2 ^ n)
  (ε : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) ≃* TwE6Delta.RecipeR K n)
  (hε : ∀ x : MulAut ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom),
    MulAut.congr ε x ∈ TwE6Delta.RecipeI K n ↔ x ∈ (RecipeExcLang.twConj K σ).range)

variable {L' : Type} [Group L'] {ψ : L' →* TwE6Delta.RecipeR K n}
  (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ center L') (hperf : commutator L' = ⊤)
  {A : Subgroup (MulAut L')}
  (hAI : ∀ a ∈ A, ∃ φ ∈ TwE6Delta.RecipeI K n, ∀ l, φ (ψ l) = ψ (a l))

noncomputable def recipeActorModelEquiv :
    A ≃* rgrpModel hn hK σ hσ Fr hFr ε (TypeA.inducedSub ψ A) :=
  Classical.choose (exists_equiv_rgrpModel_of_cover hn hK σ hσ Fr hFr ε hε hψ hker hperf hAI)

theorem recipeActorModelEquiv_apply (a : A) (l : L') :
    rgrpRecipeAut hn hK σ hσ Fr hFr ε
      ⟨(recipeActorModelEquiv hn hK σ hσ Fr hFr ε hε hψ hker hperf hAI a : ModGL Tag.E6 Ω),
        rgrpModel_le_Rgrp hn hK σ hσ Fr hFr ε _
          (recipeActorModelEquiv hn hK σ hσ Fr hFr ε hε hψ hker hperf hAI a).2⟩
        (ψ l) = ψ (a.1 l) := by
  let γ := recipeActorModelEquiv hn hK σ hσ Fr hFr ε hε hψ hker hperf hAI
  let r : TwistedDiag.Rgrp Ω Fr :=
    ⟨γ a, rgrpModel_le_Rgrp hn hK σ hσ Fr hFr ε _ (γ a).2⟩
  have hact : r.1 * baseChangeGL (τ := Tag.E6) (algebraMap K Ω) (ε.symm (ψ l)).1 * r.1⁻¹ =
      baseChangeGL (τ := Tag.E6) (algebraMap K Ω) (ε.symm (ψ (a.1 l))).1 :=
    (Classical.choose_spec
      (exists_equiv_rgrpModel_of_cover hn hK σ hσ Fr hFr ε hε hψ hker hperf hAI)).1 a l
  have hc : rgrpConjAut hn hK σ hσ Fr hFr r (ε.symm (ψ l)) = ε.symm (ψ (a.1 l)) := by
    apply Subtype.ext
    apply baseChangeGL_injective (τ := Tag.E6) (algebraMap K Ω)
    rw [baseChange_rgrpConjAut]
    exact hact
  have h := rgrpRecipeAut_apply hn hK σ hσ Fr hFr ε r (ε.symm (ψ l))
  rwa [hc, ε.apply_symm_apply, ε.apply_symm_apply] at h

theorem recipeActorModelEquiv_conj {g : L'}
    (hg : MulAut.conj g ∈ normalizer (A : Set (MulAut L'))) (a : A) :
    (recipeActorModelEquiv hn hK σ hσ Fr hFr ε hε hψ hker hperf hAI
      (ggConjAut A hg a) : ModGL Tag.E6 Ω) =
        recipeMatrixHom σ ε (ψ := ψ) g *
          (recipeActorModelEquiv hn hK σ hσ Fr hFr ε hε hψ hker hperf hAI a : ModGL Tag.E6 Ω) *
            (recipeMatrixHom σ ε (ψ := ψ) g)⁻¹ :=
  (Classical.choose_spec
    (exists_equiv_rgrpModel_of_cover hn hK σ hσ Fr hFr ε hε hψ hker hperf hAI)).2 g hg a

theorem rgrpModel_fixedHyperplane_eq {φ : MulAut A} :
    rgrpModel hn hK σ hσ Fr hFr ε
      (TypeA.inducedSub ψ ((φ.toMonoidHom.eqLocus (MonoidHom.id A)).map A.subtype)) =
        (φ.toMonoidHom.eqLocus (MonoidHom.id A)).map
          ((rgrpModel hn hK σ hσ Fr hFr ε (TypeA.inducedSub ψ A)).subtype.comp
            (recipeActorModelEquiv hn hK σ hσ Fr hFr ε hε hψ hker hperf hAI).toMonoidHom) := by
  let γ := recipeActorModelEquiv hn hK σ hσ Fr hFr ε hε hψ hker hperf hAI
  ext x
  constructor
  · intro hx
    obtain ⟨hxR, a, ha, hax⟩ := (mem_rgrpModel hn hK σ hσ Fr hFr ε).mp hx
    obtain ⟨b, hb, rfl⟩ := ha
    have hbx : (γ b : ModGL Tag.E6 Ω) = x := by
      have h := rgrpRecipeAut_injective hn hK σ hσ Fr hFr ε
        (TypeA.induced_unique ψ hψ
          (recipeActorModelEquiv_apply hn hK σ hσ Fr hFr ε hε hψ hker hperf hAI b) hax)
      exact congrArg Subtype.val h
    exact ⟨b, hb, hbx⟩
  · rintro ⟨a, ha, rfl⟩
    exact (mem_rgrpModel hn hK σ hσ Fr hFr ε).mpr
      ⟨rgrpModel_le_Rgrp hn hK σ hσ Fr hFr ε _ (γ a).2,
        TypeA.mem_inducedSub.mpr
          ⟨a, mem_map_of_mem A.subtype ha,
            recipeActorModelEquiv_apply hn hK σ hσ Fr hFr ε hε hψ hker hperf hAI a⟩⟩

include hn hK hσ hFr in
theorem recipeMatrixHom_mem_Rgrp (g : L') :
    recipeMatrixHom σ ε (ψ := ψ) g ∈ TwistedDiag.Rgrp Ω Fr := by
  let r : TwistedDiag.Rgrp Ω Fr := twInndiagEquivRgrp hn hK σ hσ Fr hFr
    ⟨ε.symm (ψ g), RecipeExcLang.graphFixedRootGroup_le_twInndiag σ (ε.symm (ψ g)).2⟩
  have hr : r.1 = recipeMatrixHom σ ε (ψ := ψ) g :=
    (twInndiagEquivRgrp_apply hn hK σ hσ Fr hFr _).trans
      (recipeMatrixHom_apply σ ε (ψ := ψ) g).symm
  exact hr ▸ r.2

section CentralizerGeometry
open scoped CFSG.ConvolutionPoints

theorem rgrpModel_eq_fixedHyperplane_sup_negative
    [Finite A] (hA : CFSG.Open.IsElemAbelian 3 A)
    {φ : MulAut A} (hφ : GGIsReflection 3 φ) {e : A} (he : e ≠ 1) (hφe : φ e = e⁻¹) :
    rgrpModel hn hK σ hσ Fr hFr ε (TypeA.inducedSub ψ A) =
      rgrpModel hn hK σ hσ Fr hFr ε
        (TypeA.inducedSub ψ ((φ.toMonoidHom.eqLocus (MonoidHom.id A)).map A.subtype)) ⊔
      zpowers (recipeActorModelEquiv hn hK σ hσ Fr hFr ε hε hψ hker hperf hAI e : ModGL .E6 Ω) := by
  let γ := recipeActorModelEquiv hn hK σ hσ Fr hFr ε hε hψ hker hperf hAI
  let X := rgrpModel hn hK σ hσ Fr hFr ε (TypeA.inducedSub ψ A)
  let f := X.subtype.comp γ.toMonoidHom
  have hfull : (⊤ : Subgroup A).map f = X := by
    rw [Subgroup.map_top]
    ext x
    constructor
    · rintro ⟨a, rfl⟩; exact (γ a).2
    · intro hx
      obtain ⟨a, ha⟩ := γ.surjective ⟨x,hx⟩
      exact ⟨a, congrArg Subtype.val ha⟩
  have hsplit := hφ.eqLocus_sup_zpowers_of_inverted_three hA he hφe
  have hmap := congrArg (Subgroup.map f) hsplit
  rw [Subgroup.map_sup, MonoidHom.map_zpowers, hfull] at hmap
  rw [rgrpModel_fixedHyperplane_eq hn hK σ hσ Fr hFr ε hε hψ hker hperf hAI]
  exact hmap.symm

include hε in
theorem orderOf_recipeMatrixHom_of_two_element_reflection
    [Finite L']
    (hTB : GGTorusTBGroup 3 4 (TwE6Delta.RecipeR K n) (TwE6Delta.RecipeI K n) L' ψ A)
    (hnt : ¬ E6AdToral (rgrpModel hn hK σ hσ Fr hFr ε (TypeA.inducedSub ψ A)))
    {g : L'} (hg : MulAut.conj g ∈ normalizer (A : Set (MulAut L')))
    (hφ : GGIsReflection 3 (ggConjAut A hg)) {m : ℕ} (hgm : g ^ (2 ^ m) = 1) :
    orderOf (recipeMatrixHom (Ω := Ω) σ ε (ψ := ψ) g) = 2 := by
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  have : CharP K 2 := CFSG.StandardType.charP_two_of_card (m := n * 2) (by rw [hK,pow_mul])
  have : CharP Ω 2 := charP_of_injective_algebraMap (algebraMap K Ω).injective 2
  let E := rgrpModel hn hK σ hσ Fr hFr ε (TypeA.inducedSub ψ A)
  let γ := recipeActorModelEquiv hn hK σ hσ Fr hFr ε hε
    hTB.1 hTB.2.1 hTB.2.2.1 hTB.2.2.2.2.1
  have : Finite A := inferInstance
  have : Finite E := Finite.of_equiv A γ
  have hcardA : Nat.card A = 3 ^ 4 := le_antisymm
    (card_le_four_of_not_e6AdToral_rgrpModel_of_cover hn hK σ hσ Fr hFr ε hε
      hTB.1 hTB.2.1 hTB.2.2.1 hTB.2.2.2.1 hTB.2.2.2.2.1 hnt) hTB.2.2.2.2.2.1
  have hcardE : Nat.card E = 3 ^ 4 := (Nat.card_congr γ.toEquiv).symm.trans hcardA
  have hEG : E ≤ adjointGroup .E6 Ω := fun x hx => ((TwistedDiag.mem_Rgrp _).mp
    (rgrpModel_le_Rgrp hn hK σ hσ Fr hFr ε _ hx)).1
  have hE : CFSG.Open.IsElemAbelian 3 E := isElemAbelian_rgrpModel hn hK σ hσ Fr hFr ε
    (TypeA.isElemAbelian_inducedSub hTB.1 hTB.2.2.2.1)
  let t : ModGL .E6 Ω := recipeMatrixHom σ ε (ψ := ψ) g
  have htG : t ∈ adjointGroup .E6 Ω := by
    let r := twInndiagEquivRgrp hn hK σ hσ Fr hFr
      ⟨ε.symm (ψ g), RecipeExcLang.graphFixedRootGroup_le_twInndiag σ (ε.symm (ψ g)).2⟩
    have hr : r.1 = t := (twInndiagEquivRgrp_apply hn hK σ hσ Fr hFr _).trans
      (recipeMatrixHom_apply σ ε (ψ := ψ) g).symm
    exact hr ▸ ((TwistedDiag.mem_Rgrp _).mp r.2).1
  have hact (a : A) : t * (γ a : ModGL .E6 Ω) * t⁻¹ = γ (ggConjAut A hg a) :=
    (recipeActorModelEquiv_conj hn hK σ hσ Fr hFr ε hε
      hTB.1 hTB.2.1 hTB.2.2.1 hTB.2.2.2.2.1 hg a).symm
  have ht2C : t ^ 2 ∈ centralizer (E : Set (ModGL .E6 Ω)) := by
    rw [mem_centralizer_iff]
    intro x hx
    obtain ⟨a,ha⟩ := γ.surjective ⟨x,hx⟩
    have hφφ : ggConjAut A hg (ggConjAut A hg a) = a := by
      have h := congrArg (fun f : MulAut A => f a) hφ.1
      simpa only [pow_two,MulAut.mul_apply,MulAut.one_apply] using h
    have hc : t^2*(γ a : ModGL .E6 Ω)*(t^2)⁻¹=(γ a : ModGL .E6 Ω) := by
      calc t^2*(γ a : ModGL .E6 Ω)*(t^2)⁻¹=
          t*(t*(γ a : ModGL .E6 Ω)*t⁻¹)*t⁻¹ := by rw [pow_two]; group
        _=(γ a : ModGL .E6 Ω) := by rw [hact,hact,hφφ]
    have hax : (γ a : ModGL .E6 Ω)=x := congrArg Subtype.val ha
    rw [hax] at hc
    exact ((mul_inv_eq_iff_eq_mul).mp hc).symm
  have ht2pow : (t ^ 2) ^ (2 ^ m) = 1 := by
    have ht : t ^ (2 ^ m) = 1 := by change recipeMatrixHom σ ε g ^ (2 ^ m) = 1;rw [← map_pow,hgm,map_one]
    rw [← pow_mul,Nat.mul_comm,pow_mul,ht,one_pow]
  have ht2 : t ^ 2 = 1 := eq_one_of_mem_original_centralizer_of_pow_two_pow_eq_one
    (CFSG.RankThree.PartOne.KE.isAlgebraic_zmod_of_isAlgClosure (k := K)) hEG hE hcardE hnt
    ⟨pow_mem htG 2,ht2C⟩ ht2pow
  have ht1 : t ≠ 1 := by
    intro h
    apply hφ.ne_one Nat.prime_three
    apply MulEquiv.ext
    intro a
    apply γ.injective
    apply Subtype.ext
    simpa [h] using (hact a).symm
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime_iff.mpr ⟨ht2,ht1⟩


theorem negative_mem_full_connected_centralizer_of_actual_reflection
    [Finite L']
    (hε : ∀ x : MulAut ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom),
      MulAut.congr ε x ∈ TwE6Delta.RecipeI K n ↔ x ∈ (RecipeExcLang.twConj K σ).range)
    (hTB : GGTorusTBGroup 3 4 (TwE6Delta.RecipeR K n) (TwE6Delta.RecipeI K n) L' ψ A)
    (hnt : ¬ E6AdToral (rgrpModel hn hK σ hσ Fr hFr ε (TypeA.inducedSub ψ A)))
    {g : L'} (hg : MulAut.conj g ∈ normalizer (A : Set (MulAut L')))
    {φ : MulAut A} (hgφ : ggConjAut A hg = φ) (hφ : GGIsReflection 3 φ)
    {e : A} (he : e ≠ 1) (hφe : φ e = e⁻¹)
    (heK : (recipeActorModelEquiv hn hK σ hσ Fr hFr ε hε
        hTB.1 hTB.2.1 hTB.2.2.1 hTB.2.2.2.2.1 e : ModGL .E6 Ω) ∈
      closedIdentityComponent (adjointGroup .E6 Ω ⊓ centralizer
        (rgrpModel hn hK σ hσ Fr hFr ε
          (TypeA.inducedSub ψ ((φ.toMonoidHom.eqLocus (MonoidHom.id A)).map A.subtype)) : Set (ModGL .E6 Ω)))) :
    (recipeActorModelEquiv hn hK σ hσ Fr hFr ε hε
        hTB.1 hTB.2.1 hTB.2.2.1 hTB.2.2.2.2.1 e : ModGL .E6 Ω) ∈
      closedIdentityComponent (adjointGroup .E6 Ω ⊓ centralizer
        (rgrpModel hn hK σ hσ Fr hFr ε (TypeA.inducedSub ψ A) : Set (ModGL .E6 Ω))) := by
  classical
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  have : CharP K 2 := CFSG.StandardType.charP_two_of_card (m := n * 2) (by rw [hK,pow_mul])
  have : CharP Ω 2 := charP_of_injective_algebraMap (algebraMap K Ω).injective 2
  let E := rgrpModel hn hK σ hσ Fr hFr ε (TypeA.inducedSub ψ A)
  let γ := recipeActorModelEquiv hn hK σ hσ Fr hFr ε hε
    hTB.1 hTB.2.1 hTB.2.2.1 hTB.2.2.2.2.1
  have : Finite E := Finite.of_equiv A γ
  have hEG : E ≤ adjointGroup .E6 Ω := fun x hx => ((TwistedDiag.mem_Rgrp _).mp
    (rgrpModel_le_Rgrp hn hK σ hσ Fr hFr ε _ hx)).1
  have hE : CFSG.Open.IsElemAbelian 3 E := isElemAbelian_rgrpModel hn hK σ hσ Fr hFr ε
    (TypeA.isElemAbelian_inducedSub hTB.1 hTB.2.2.2.1)
  have hcardA : Nat.card A = 3 ^ 4 := le_antisymm
    (card_le_four_of_not_e6AdToral_rgrpModel_of_cover hn hK σ hσ Fr hFr ε hε
      hTB.1 hTB.2.1 hTB.2.2.1 hTB.2.2.2.1 hTB.2.2.2.2.1 hnt) hTB.2.2.2.2.2.1
  have hcardE : Nat.card E = 3 ^ 4 := (Nat.card_congr γ.toEquiv).symm.trans hcardA
  let φE := MulAut.congr γ φ
  have hφE : GGIsReflection 3 φE := (F4AutRefl.ggIsReflection_congr_iff γ φ).mpr hφ
  let t := recipeMatrixHom (Ω := Ω) σ ε (ψ := ψ) g
  have htG : t ∈ adjointGroup .E6 Ω := ((TwistedDiag.mem_Rgrp _).mp
    (recipeMatrixHom_mem_Rgrp hn hK σ hσ Fr hFr ε g)).1
  have hact (x : E) : t * (x : ModGL .E6 Ω) * t⁻¹ = φE x := by
    obtain ⟨a,rfl⟩ := γ.surjective x
    have hγφ : φE (γ a) = γ (φ a) := by
      change γ (φ (γ.symm (γ a))) = γ (φ a)
      rw [γ.symm_apply_apply]
    rw [hγφ]
    have h := recipeActorModelEquiv_conj hn hK σ hσ Fr hFr ε hε
      hTB.1 hTB.2.1 hTB.2.2.1 hTB.2.2.2.2.1 hg a
    rw [hgφ] at h
    exact h.symm
  have heE : φE (γ e) = (γ e)⁻¹ := by
    change γ (φ (γ.symm (γ e))) = (γ e)⁻¹
    rw [γ.symm_apply_apply, hφe, map_inv]
  rcases E6NegativeCyclic.exists_conj_cE6_or_centralizer_eq_self K hEG hE hcardE hnt with hc | hself
  · obtain ⟨a,ha,hN,hAS,hAg,hA⟩ := hc
    have hET : ¬ E.map (MulAut.conj a).toMonoidHom ≤ torusGroup .E6 Ω := by
      intro h
      exact hnt ((e6AdToral_map_conj ha E).mp
        ⟨1,one_mem _,fun x hx => by simpa using h hx⟩)
    exact E6NegativeCyclic.negative_mem_connected_of_conj_weyl_cE6 K hEG hE hcardE
      φE hφE htG hact heE a ha hN hET hAS hAg hA
  ·
    exfalso
    let H : Subgroup (ModGL .E6 Ω) := rgrpModel hn hK σ hσ Fr hFr ε
      (TypeA.inducedSub ψ ((φ.toMonoidHom.eqLocus (MonoidHom.id A)).map A.subtype))
    let em : ModGL .E6 Ω := γ e
    have hGad : IsPointClosed Ω (transportPoints (modGLPoint .E6 Ω)
        (adjointGroup .E6 Ω : Set (ModGL .E6 Ω))) := by
      rw [transportPoints_modGLPoint]
      exact (exceptional_Lang_exact_affine_group_realization Ω .E6).1.1
    have hZ : IsPointClosed Ω (transportPoints (modGLPoint .E6 Ω)
        ((adjointGroup .E6 Ω ⊓ centralizer (H : Set (ModGL .E6 Ω))) :
          Set (ModGL .E6 Ω))) :=
      isPointClosed_inf hGad (isPointClosed_centralizer (H : Set (ModGL .E6 Ω)))
    have hK0 : IsConnectedAlgebraicSubgroup Ω
        ((closedIdentityComponent (adjointGroup .E6 Ω ⊓
          centralizer (H : Set (ModGL .E6 Ω)))).map
            (modGLPoint .E6 Ω).toMonoidHom) :=
      isConnectedAlgebraicSubgroup_closedIdentityComponent hZ
    have hemK : em ∈ closedIdentityComponent
        (adjointGroup .E6 Ω ⊓ centralizer (H : Set (ModGL .E6 Ω))) := heK
    have hem3 : em ^ 3 = 1 := by
      have h := congrArg (fun x : A => (γ x : ModGL .E6 Ω))
        (Subtype.ext (hTB.2.2.2.1.2 e e.2) : e ^ 3 = 1)
      simpa only [map_pow, map_one, coe_pow, coe_one] using h
    have hem1 : em ≠ 1 := by
      intro h
      have h' : (γ e : E) = 1 := Subtype.ext (by simpa [em] using h)
      exact he (γ.injective (by rw [h']; exact (map_one γ).symm))
    have hsplit : E = H ⊔ zpowers em :=
      rgrpModel_eq_fixedHyperplane_sup_negative hn hK σ hσ Fr hFr ε hε
        hTB.1 hTB.2.1 hTB.2.2.1 hTB.2.2.2.2.1 hTB.2.2.2.1 hφ he hφe
    exact (ne_centralizer_of_isConnected_of_eq_sup_zpowers (G := adjointGroup .E6 Ω)
      (H := H) em hK0 hsplit (closedIdentityComponent_le _) hemK hem3 hem1
      (CharP.cast_ne_zero_of_ne_of_prime Ω Nat.prime_three (by decide))) hself

end CentralizerGeometry

end CFSG.StandardType.SCFourCover

namespace CFSG.StandardType.SCFourCover

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.StandardType.GGFinModel
  CFSG.HardMathSupport.Lang.E6Descent
open CFSG.StandardType

@[expose] noncomputable def actualRecipeActorGroup {G : Type} [Group G] {J Bs : Subgroup G}
    (hN : Bs ≤ Subgroup.normalizer (J : Set G)) : Subgroup (MulAut ↥J) :=
  (ggGamma J hN).range

@[expose] noncomputable def actualRecipeActorNormalizer {G : Type} [Group G] {J Bs : Subgroup G}
    (hN : Bs ≤ Subgroup.normalizer (J : Set G)) : Subgroup ↥J :=
  (Subgroup.normalizer (actualRecipeActorGroup hN : Set (MulAut ↥J))).comap
    (MulAut.conj : ↥J →* MulAut ↥J)

@[expose] noncomputable def actualRecipeActorNormalizerAction {G : Type} [Group G] {J Bs : Subgroup G}
    (hN : Bs ≤ Subgroup.normalizer (J : Set G)) :
    actualRecipeActorNormalizer hN →* MulAut (actualRecipeActorGroup hN) :=
  (actualRecipeActorGroup hN).normalizerMonoidHom.comp
    (((MulAut.conj : ↥J →* MulAut ↥J).comp (actualRecipeActorNormalizer hN).subtype).codRestrict
      (Subgroup.normalizer (actualRecipeActorGroup hN : Set (MulAut ↥J)))
      (fun n => n.2))


theorem exists_actual_recipe_action_finite_descent
    {G : Type} [Group G] [Finite G] {J Bs : Subgroup G}
    (hN : Bs ≤ Subgroup.normalizer (J : Set G))
    {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n)
    [Algebra K GGL] [IsAlgClosure K GGL]
    (Fr : GGL →+* GGL) (hFr : ∀ c, Fr c = c ^ 2 ^ n)
    (ε : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) ≃* TwE6Delta.RecipeR K n)
    (hε : ∀ x : MulAut ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom),
      MulAut.congr ε x ∈ TwE6Delta.RecipeI K n ↔ x ∈ (RecipeExcLang.twConj K σ).range)
    {ψ : ↥J →* TwE6Delta.RecipeR K n}
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center ↥J)
    (hperf : commutator ↥J = ⊤)
    (hAI : ∀ a ∈ actualRecipeActorGroup hN,
      ∃ φ ∈ TwE6Delta.RecipeI K n, ∀ l : ↥J, φ (ψ l) = ψ (a l))
    (k₀ : Type) [Field k₀] [Finite k₀] (ι₀ : k₀ →+* GGL) :
    ∃ (k : Type) (_ : Field k) (_ : Finite k) (_ : CharP k 2)
      (κ : k₀ →+* k) (ι : k →+* GGL),
      ι.comp κ = ι₀ ∧
      ∃ e_k : actualRecipeActorGroup hN →* adjointGroup Tag.E6 k,
      ∃ j_k : actualRecipeActorNormalizer hN →* adjointGroup Tag.E6 k,
        (∀ a, baseChangeGL ι (e_k a).val =
          (rgrpModel hn hK σ hσ Fr hFr ε
            (TypeA.inducedSub ψ (actualRecipeActorGroup hN))).subtype
            (recipeActorModelEquiv hn hK σ hσ Fr hFr ε hε hψ hker hperf hAI a)) ∧
        (∀ n, baseChangeGL ι (j_k n).val =
          recipeMatrixHom σ ε (ψ := ψ) (n : ↥J)) ∧
        (∀ n a, e_k (actualRecipeActorNormalizerAction hN n a) =
          j_k n * e_k a * (j_k n)⁻¹) ∧
        Function.Injective e_k := by
  classical
  let A := actualRecipeActorGroup hN
  let Nj := actualRecipeActorNormalizer hN
  let e : A →* ModGL Tag.E6 GGL :=
    (rgrpModel hn hK σ hσ Fr hFr ε (TypeA.inducedSub ψ A)).subtype.comp
      (recipeActorModelEquiv hn hK σ hσ Fr hFr ε hε hψ hker hperf hAI).toMonoidHom
  let j : Nj →* ModGL Tag.E6 GGL :=
    (recipeMatrixHom σ ε (ψ := ψ)).comp Nj.subtype
  have he_adj : ∀ a, e a ∈ adjointGroup Tag.E6 GGL := by
    intro a
    exact ((TwistedDiag.mem_Rgrp Fr).mp
      (rgrpModel_le_Rgrp hn hK σ hσ Fr hFr ε (TypeA.inducedSub ψ A)
        (recipeActorModelEquiv hn hK σ hσ Fr hFr ε hε hψ hker hperf hAI a).2)).1
  have hj_adj : ∀ n, j n ∈ adjointGroup Tag.E6 GGL := by
    intro n
    exact ((TwistedDiag.mem_Rgrp Fr).mp
      (recipeMatrixHom_mem_Rgrp hn hK σ hσ Fr hFr ε (ψ := ψ) (n : ↥J))).1
  have hα_apply (n : Nj) (a : A) :
      actualRecipeActorNormalizerAction hN n a = ggConjAut A n.2 a := by
    apply Subtype.ext
    change ((A.normalizerMonoidHom
      (⟨(MulAut.conj : ↥J →* MulAut ↥J) (n : ↥J), n.2⟩ : Subgroup.normalizer (A : Set (MulAut ↥J))))
        a : MulAut ↥J) =
      ((ggConjAut A n.2 a : A) : MulAut ↥J)
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
    rfl
  have hα : ∀ n a, e (actualRecipeActorNormalizerAction hN n a) = j n * e a * (j n)⁻¹ := by
    intro n a
    rw [hα_apply n a]
    simpa [e, j] using
      (recipeActorModelEquiv_conj hn hK σ hσ Fr hFr ε hε hψ hker hperf hAI (g := (n : ↥J)) n.2 a)
  obtain ⟨k, hk, hkfin, hchar, κ, ι, hcomp, e_k, j_k, hek, hjk, hconj, hinj⟩ :=
    CFSG.StandardType.LieCore.exists_finite_adjoint_action_descent
      e j he_adj hj_adj (actualRecipeActorNormalizerAction hN) hα k₀ ι₀
  refine ⟨k, hk, hkfin, hchar, κ, ι, hcomp, e_k, j_k, ?_, ?_, ?_, ?_⟩
  · intro a
    exact hek a
  · intro n
    exact hjk n
  · intro n a
    exact hconj n a
  · apply hinj
    intro a b hab
    exact (recipeActorModelEquiv hn hK σ hσ Fr hFr ε hε hψ hker hperf hAI).injective
      (Subtype.ext (by simpa [e] using hab))

end CFSG.StandardType.SCFourCover
