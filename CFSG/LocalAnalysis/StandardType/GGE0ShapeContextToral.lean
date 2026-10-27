module

public import CFSG.LocalAnalysis.StandardType.GGE0ShapeDefs
public import CFSG.LocalAnalysis.StandardType.GGE0ModelFrame
public import CFSG.LocalAnalysis.StandardType.GGOTwoStarFrame
public import CFSG.LocalAnalysis.StandardType.GGSixLSixSevenA3BstarCentralizer
public import CFSG.LocalAnalysis.StandardType.GGE0ShapeContextToralAux
public import CFSG.LocalAnalysis.StandardType.GGE0ShapeContextToralAux2
public import CFSG.LocalAnalysis.StandardType.GGE0ShapeWeylGoodDefs
public import CFSG.LocalAnalysis.StandardType.GGE0ShapeWeylGood
public import CFSG.LocalAnalysis.StandardType.GGE0ShapeRankFive
public import CFSG.LocalAnalysis.StandardType.GGOuterInvAtE6DiagLang
public import CFSG.LocalAnalysis.StandardType.GGE0ExcTwE6NonShape
public import CFSG.LocalAnalysis.StandardType.GGE0ShapeSetupSplitPlus
public import CFSG.LocalAnalysis.StandardType.GGE0ShapeSetupTwPlus

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.Minuscule
  CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Steinberg.TwistedE6
  CFSG.LieType.Steinberg.Exceptional

private theorem mem_contextImage {G : Type} [Group G] {G0 H : Subgroup G} {φ : MulAut G0} :
    φ ∈ contextImage G0 H ↔
      ∃ n : Subgroup.normalizer (G0 : Set G), (n : G) ∈ H ∧
        Subgroup.normalizerMonoidHom G0 n = φ := by
  rw [contextImage, Subgroup.mem_map]
  simp only [Subgroup.mem_comap]
  exact Iff.rfl

private theorem contextImage_card_of_le_normalizer {G : Type} [Group G]
    {G0 H : Subgroup G} (hH : H ≤ Subgroup.normalizer (G0 : Set G))
    (hC : Subgroup.centralizer (G0 : Set G) = ⊥) :
    Nat.card (contextImage G0 H) = Nat.card H := by
  have hker : (Subgroup.normalizerMonoidHom G0).ker = ⊥ := by
    rw [Subgroup.normalizerMonoidHom_ker, hC, Subgroup.bot_subgroupOf]
  have hinj : Function.Injective (Subgroup.normalizerMonoidHom G0) :=
    (MonoidHom.ker_eq_bot_iff _).mp hker
  change Nat.card ((H.comap (Subgroup.normalizer (G0 : Set G)).subtype).map
    (Subgroup.normalizerMonoidHom G0)) = Nat.card H
  rw [Subgroup.card_map_of_injective hinj]
  have hmap : (H.comap (Subgroup.normalizer (G0 : Set G)).subtype).map
      (Subgroup.normalizer (G0 : Set G)).subtype = H := by
    rw [Subgroup.map_comap_eq, Subgroup.range_subtype]
    exact inf_eq_right.mpr hH
  have hcard : Nat.card (H.comap (Subgroup.normalizer (G0 : Set G)).subtype) =
      Nat.card H := by
    conv_rhs => rw [← hmap]
    exact (Subgroup.card_map_of_injective
      (f := (Subgroup.normalizer (G0 : Set G)).subtype)
      (K := H.comap (Subgroup.normalizer (G0 : Set G)).subtype)
      (Subgroup.subtype_injective (Subgroup.normalizer (G0 : Set G)))).symm
  rw [hcard]

private theorem realizedSubgroup_le_model {C : Type} [Group C] {I : Subgroup (MulAut C)}
    {L : Type} [Field L] [IsAlgClosed L]
    (R : ShapeRealization C I L) (E : Subgroup (MulAut C)) :
    realizedSubgroup R E ≤ R.setup.D.model := by
  intro x hx
  rw [realizedSubgroup, Subgroup.mem_map] at hx
  obtain ⟨φ, -, rfl⟩ := hx
  exact R.action_mem φ

private theorem realizedSubgroup_card_of_le {C : Type} [Group C]
    {I : Subgroup (MulAut C)} {L : Type} [Field L] [IsAlgClosed L]
    (R : ShapeRealization C I L) {E : Subgroup (MulAut C)} (hE : E ≤ I) :
    Nat.card (realizedSubgroup R E) = Nat.card E := by
  change Nat.card ((E.comap I.subtype).map R.action) = Nat.card E
  rw [Subgroup.card_map_of_injective R.action_injective]
  have hmap : (E.comap I.subtype).map I.subtype = E := by
    rw [Subgroup.map_comap_eq, Subgroup.range_subtype]
    exact inf_eq_right.mpr hE
  have hcard : Nat.card (E.comap I.subtype) = Nat.card E := by
    conv_rhs => rw [← hmap]
    exact (Subgroup.card_map_of_injective
      (f := I.subtype) (K := E.comap I.subtype) I.subtype_injective).symm
  rw [hcard]

private theorem exists_lang_realization
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {t : StatedLieTag} {n f : ℕ}
    {ψ : (ggU t n f).K →* G}
    (hctx : GGSixCtxV2 3 B Bs x L D J (ggU t n f).D t n f ψ)
    (s1 : GGSixStepOne 3 B Bs x L D J) (hshape : Shape t f) :
    ∃ (Ω : Type) (_ : Field Ω) (_ : IsAlgClosed Ω) (_ : CharP Ω 2)
      (I : Subgroup (MulAut (ggG0 3 B x L D J)))
      (R : ShapeRealization (ggG0 3 B x L D J) I Ω),
      (letI := ZMod.algebra Ω 2; Algebra.IsAlgebraic (ZMod 2) Ω) ∧
      contextImage (ggG0 3 B x L D J) (ggG1 ψ) ≤ I ∧
      contextImage (ggG0 3 B x L D J) Bs ≤ I ∧
      realizedSubgroup R (contextImage (ggG0 3 B x L D J) Bs) ≤ torusGroup .E6 Ω ∧
      (t = .E6 → ∀ α, R.setup.ρ α = α) ∧
      (t = .twistedE6 → ∀ α, R.setup.ρ α = -α) ∧
      contextImage (ggG0 3 B x L D J) D ≤ I := by
  classical
  rcases hshape with ⟨rfl, h3⟩ | ⟨rfl, h3⟩
  · have hf : 1 ≤ f := hctx.2.2.2.1.1.2.1
    obtain ⟨S, e, hdesc, hρ, hT3, hdict, hfaith⟩ := split_setup_plus (f := f) hf h3
    let C := CFSG.Blueprint.Chevalley.adjointGroup .E6 (GaloisField 2 f)
    let I_C : Subgroup (MulAut C) :=
      (MulAut.conj : C →* MulAut C).range ⊔ (AutSt.e6DiagHom (GaloisField 2 f)).range
    let π : (ggU .E6 n f).K →* C :=
      CFSG.LieType.Steinberg.Isogeny.e6Isogeny (GaloisField 2 f)
    have hπ : Function.Surjective π :=
      CFSG.LieType.Steinberg.Isogeny.e6Isogeny_surjective _
    have hπker : π.ker = Subgroup.center (ggU .E6 n f).K :=
      CFSG.LieType.Steinberg.CentralExt.FieldFour.e6Isogeny_ker_eq_center
    have hC' : Subgroup.centralizer (ψ.range : Set G) = ⊥ := by
      rw [hctx.range_eq]; exact s1.1
    have hψ : ψ.ker = Subgroup.center (ggU .E6 n f).K :=
      ggOuterInv_ker_eq_center_of_centralizer ψ hctx.2.2.2.2.1.2 hC'
    obtain ⟨Θ, Φ, hΘ, hΦinj, hΦ⟩ :=
      ggOuterInv_exists_modelHom ψ hctx.range_eq π hπ (hπker.trans hψ.symm) s1.1
    have hΦI : ∀ c : Subgroup.normalizer (ggG0 3 B x L D J : Set G),
        (c : G) ∈ ggG1 ψ → Φ c ∈ I_C :=
      modelHom_mem_innerDiag_e6 hctx s1 Θ Φ hΘ hΦ
    have hΓle : S.Γ ≤ S.D.model :=
      CFSG.HardMathSupport.Timmesfeld.LangTorus.LangSetup.Γ_le_model S
    have hInn : (MulAut.conj : C →* MulAut C).range ≤ I_C := le_sup_left
    have hreal : ∀ φ : I_C, ∃ d ∈ S.D.model,
        ∀ y : C, e (φ.1 y) = d * e y * d⁻¹ := fun φ => hdict φ.1 φ.2
    obtain ⟨act, hact_inner, hact_mem, hact_rel⟩ :=
      exists_shape_model_action S e hΓle hInn hreal hfaith
    have hact_inj : Function.Injective act := by
      intro φ1 φ2 h12
      apply Subtype.ext
      exact MulEquiv.ext fun y => e.injective (Subtype.ext (by
        rw [hact_rel φ1 y, hact_rel φ2 y, h12]))
    obtain ⟨I₀, R₀, hR₀setup, -, hR₀action⟩ :=
      realization_of_model e Θ act hact_mem hact_inj hInn hact_inner (fun φ y => hact_rel φ y)
    have hG1I : contextImage (ggG0 3 B x L D J) (ggG1 ψ) ≤ I₀ :=
      contextImage_le_of_conj Θ Φ hΦ hΦI R₀ act hR₀action
    have hBsN : Bs ≤ Subgroup.normalizer (ggG0 3 B x L D J : Set G) :=
      (ggBs_le_ggG1 hctx).trans (ggG1_le_ggM hctx.range_eq)
    have hBsI : contextImage (ggG0 3 B x L D J) Bs ≤ I₀ :=
      contextImage_le_of_conj Θ Φ hΦ
        (fun c hc => hΦI c (ggBs_le_ggG1 hctx hc)) R₀ act hR₀action
    have hA_model : realizedSubgroup R₀ (contextImage (ggG0 3 B x L D J) Bs) ≤ S.D.model := by
      rw [← hR₀setup]
      exact realizedSubgroup_le_model R₀ _
    have hA_el : IsElemAbelian 3
        (realizedSubgroup R₀ (contextImage (ggG0 3 B x L D J) Bs)) :=
      realizedSubgroup_isElemAbelian R₀ hctx.2.1.2.1
    have hA_card : 3 ^ 5 ≤ Nat.card
        (realizedSubgroup R₀ (contextImage (ggG0 3 B x L D J) Bs)) := by
      rw [realizedSubgroup_card_of_le R₀ hBsI, contextImage_card_of_le_normalizer hBsN s1.1]
      exact pow_five_le_card_bstar (G := G) hctx s1 (Or.inl ⟨rfl, h3⟩)
    obtain ⟨h, hh_model, hh_torus⟩ :=
      toral_conj_in_model (weylGoodRankFive (AlgebraicClosure (GaloisField 2 f)))
        S hT3 hA_model hA_el hA_card
    obtain ⟨R, hRsetup, hRreal⟩ :=
      realization_conj_same R₀ (show h ∈ R₀.setup.D.model by rw [hR₀setup]; exact hh_model)
    have hDI : contextImage (ggG0 3 B x L D J) D ≤ I₀ :=
      (contextImage_mono (hctx.stdSub.1.1.trans hctx.bstar.1)).trans hBsI
    have hBT : realizedSubgroup R (contextImage (ggG0 3 B x L D J) Bs) ≤
        torusGroup .E6 (AlgebraicClosure (GaloisField 2 f)) := by
      rw [hRreal]
      exact hh_torus.trans fun y hy =>
        (CFSG.RankThree.PartOne.KE.mem_twistedTorusOf.1 hy).1
    refine ⟨AlgebraicClosure (GaloisField 2 f), inferInstance, inferInstance, inferInstance,
      I₀, R, ?_, hG1I, hBsI, hBT, ?_, ?_, hDI⟩
    · exact algebraicClosure_isAlgebraic_zmod 2 (GaloisField 2 f)
    · intro _
      rw [hRsetup, hR₀setup]
      exact hρ
    · intro ht
      cases ht
  · have hf : 1 ≤ f := hctx.2.2.2.1.1.2.1
    let K := GaloisField 2 (2 * f)
    have hK : Nat.card K = (2 ^ f) ^ 2 := by
      rw [GaloisField.card 2 (2 * f) (by omega), ← pow_mul, mul_comm]
    let σ : K ≃+* K := iterateFrobeniusEquiv K 2 f
    have hσ : ∀ c, σ c = c ^ (2 ^ f) := fun c => iterateFrobeniusEquiv_def _ 2 f c
    obtain ⟨S, e, hdesc, hρ, hT3, hdict, hfaith⟩ :=
      twisted_setup_plus (f := f) hf hK σ hσ h3
    let C := CFSG.LieType.Chevalley.twistedE6RootGroup K σ
    let I_C : Subgroup (MulAut C) :=
      CFSG.LieType.Chevalley.twistedE6Inn K σ ⊔ CFSG.LieType.Chevalley.twistedE6Diag K σ
    have hσθ : σ.toRingHom = frobQ 2 f :=
      RingHom.ext fun c => by
        change σ c = frobQ 2 f c
        rw [hσ, frobQ_apply]
    obtain ⟨-, -, -, -, -, -, -, -, ⟨-, -, -, -, -, -, -⟩, -, hder, hZ, -⟩ :=
      twisted_E6_all_characteristic_exact_automorphism_normal_form Nat.prime_two hf K hK σ hσ
    have hH : ⁅twistedFixedGroup .E6 K (frobQ 2 f), twistedFixedGroup .E6 K (frobQ 2 f)⁆ =
        twistedE6RootGroup K σ := by
      rw [← hσθ]; exact hder
    let π := (MulEquiv.subgroupCongr hH).toMonoidHom.comp (twistedE6Isogeny 2 f hf)
    have hπ : Function.Surjective π :=
      (MulEquiv.subgroupCongr hH).surjective.comp (twistedE6Isogeny_surjective 2 f hf)
    have hπvalT : ∀ z, ((π z : C) : ModGL TwistTag.E6.tag K) =
        ((e6IsogenyT K (z : e6Data_valid.minGroup K) : adjointGroup TwistTag.E6.tag K) :
          ModGL TwistTag.E6.tag K) := fun _ => rfl
    have hπker : π.ker = Subgroup.center (twistedE6Group 2 f) :=
      AutSt.ker_eq_center_of_surjective π hπ hZ (RootDetectTwE6.ker_le_center f π hπvalT)
    have hC' : Subgroup.centralizer (ψ.range : Set G) = ⊥ := by
      rw [hctx.range_eq]; exact s1.1
    have hψ : ψ.ker = Subgroup.center (ggU .twistedE6 n f).K :=
      ggOuterInv_ker_eq_center_of_centralizer ψ hctx.2.2.2.2.1.2 hC'
    obtain ⟨Θ, Φ, hΘ, hΦinj, hΦ⟩ :=
      ggOuterInv_exists_modelHom ψ hctx.range_eq π hπ (hπker.trans hψ.symm) s1.1
    have hΦI : ∀ c : Subgroup.normalizer (ggG0 3 B x L D J : Set G),
        (c : G) ∈ ggG1 ψ → Φ c ∈ I_C :=
      modelHom_mem_innerDiag_twE6 hctx s1 hf hσθ π hπ hπker hπvalT Θ Φ hΘ hΦ
    have hΓle : S.Γ ≤ S.D.model :=
      CFSG.HardMathSupport.Timmesfeld.LangTorus.LangSetup.Γ_le_model S
    have hInn : (MulAut.conj : C →* MulAut C).range ≤ I_C := le_sup_left
    have hreal : ∀ φ : I_C, ∃ d ∈ S.D.model,
        ∀ y : C, e (φ.1 y) = d * e y * d⁻¹ := fun φ => hdict φ.1 φ.2
    obtain ⟨act, hact_inner, hact_mem, hact_rel⟩ :=
      exists_shape_model_action S e hΓle hInn hreal hfaith
    have hact_inj : Function.Injective act := by
      intro φ1 φ2 h12
      apply Subtype.ext
      exact MulEquiv.ext fun y => e.injective (Subtype.ext (by
        rw [hact_rel φ1 y, hact_rel φ2 y, h12]))
    obtain ⟨I₀, R₀, hR₀setup, -, hR₀action⟩ :=
      realization_of_model e Θ act hact_mem hact_inj hInn hact_inner (fun φ y => hact_rel φ y)
    have hG1I : contextImage (ggG0 3 B x L D J) (ggG1 ψ) ≤ I₀ :=
      contextImage_le_of_conj Θ Φ hΦ hΦI R₀ act hR₀action
    have hBsN : Bs ≤ Subgroup.normalizer (ggG0 3 B x L D J : Set G) :=
      (ggBs_le_ggG1 hctx).trans (ggG1_le_ggM hctx.range_eq)
    have hBsI : contextImage (ggG0 3 B x L D J) Bs ≤ I₀ :=
      contextImage_le_of_conj Θ Φ hΦ
        (fun c hc => hΦI c (ggBs_le_ggG1 hctx hc)) R₀ act hR₀action
    have hA_model : realizedSubgroup R₀ (contextImage (ggG0 3 B x L D J) Bs) ≤ S.D.model := by
      rw [← hR₀setup]
      exact realizedSubgroup_le_model R₀ _
    have hA_el : IsElemAbelian 3
        (realizedSubgroup R₀ (contextImage (ggG0 3 B x L D J) Bs)) :=
      realizedSubgroup_isElemAbelian R₀ hctx.2.1.2.1
    have hA_card : 3 ^ 5 ≤ Nat.card
        (realizedSubgroup R₀ (contextImage (ggG0 3 B x L D J) Bs)) := by
      rw [realizedSubgroup_card_of_le R₀ hBsI, contextImage_card_of_le_normalizer hBsN s1.1]
      exact pow_five_le_card_bstar (G := G) hctx s1 (Or.inr ⟨rfl, h3⟩)
    obtain ⟨h, hh_model, hh_torus⟩ :=
      toral_conj_in_model (weylGoodRankFive (AlgebraicClosure K))
        S hT3 hA_model hA_el hA_card
    obtain ⟨R, hRsetup, hRreal⟩ :=
      realization_conj_same R₀ (show h ∈ R₀.setup.D.model by rw [hR₀setup]; exact hh_model)
    have hDI : contextImage (ggG0 3 B x L D J) D ≤ I₀ :=
      (contextImage_mono (hctx.stdSub.1.1.trans hctx.bstar.1)).trans hBsI
    have hBT : realizedSubgroup R (contextImage (ggG0 3 B x L D J) Bs) ≤
        torusGroup .E6 (AlgebraicClosure K) := by
      rw [hRreal]
      exact hh_torus.trans fun y hy =>
        (CFSG.RankThree.PartOne.KE.mem_twistedTorusOf.1 hy).1
    refine ⟨AlgebraicClosure K, inferInstance, inferInstance, inferInstance,
      I₀, R, ?_, hG1I, hBsI, hBT, ?_, ?_, hDI⟩
    · exact algebraicClosure_isAlgebraic_zmod 2 K
    · intro ht
      cases ht
    · intro _
      rw [hRsetup, hR₀setup]
      exact hρ

private theorem toralKernelContext_of_data
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {Ω : Type} [Field Ω] [IsAlgClosed Ω]
    {I : Subgroup (MulAut (ggG0 3 B x L D J))}
    (R : ShapeRealization (ggG0 3 B x L D J) I Ω)
    (hBI : contextImage (ggG0 3 B x L D J) B ≤ I)
    (hDI : contextImage (ggG0 3 B x L D J) D ≤ I)
    (hJI : contextImage (ggG0 3 B x L D J) J ≤ I)
    (hBT : realizedSubgroup R (contextImage (ggG0 3 B x L D J) Bs) ≤ torusGroup .E6 Ω)
    {a : Fin 2 → Fin Tag.E6.rank → Ωˣ}
    (hplane : planeGroup a =
      realizedSubgroup R (contextImage (ggG0 3 B x L D J) D))
    (ha3 : ∀ i j, a i j ^ 3 = 1)
    (hBN : B ≤ Subgroup.normalizer (ggG0 3 B x L D J : Set G))
    (hBBs : B ≤ Bs)
    (hBexp : ∀ b ∈ B, b ^ 3 = 1)
    (hBcard : 3 ^ 4 ≤ Nat.card B)
    (hDB : D ≤ B)
    (hcardD : Nat.card D = 9)
    (hDj : D = B ⊓ Subgroup.centralizer (J : Set G))
    (hJcomp : IsComponentOf J
      (ggG0 3 B x L D J ⊓ Subgroup.centralizer (D : Set G)))
    (hC : Subgroup.centralizer (ggG0 3 B x L D J : Set G) = ⊥)
    (hsign : (∀ α, R.setup.ρ α = α) ∨ (∀ α, R.setup.ρ α = -α)) :
    ToralKernelContext R.setup
      (realizedSubgroup R (contextImage (ggG0 3 B x L D J) B))
      (realizedSubgroup R (contextImage (ggG0 3 B x L D J) J)) a := by
  refine ⟨?_, ?_, ?_, ?_, ha3, ?_, ?_, ?_, ?_, hsign⟩
  · exact realizedSubgroup_le_model R _
  · exact (realizedSubgroup_mono R (contextImage_mono hBBs)).trans hBT
  · intro x hx
    rw [realizedSubgroup, Subgroup.mem_map] at hx
    obtain ⟨φ, hφ, rfl⟩ := hx
    have hφ' : φ.1 ∈ contextImage (ggG0 3 B x L D J) B := Subgroup.mem_comap.mp hφ
    rw [mem_contextImage] at hφ'
    obtain ⟨n, hnB, hnφ⟩ := hφ'
    have hφ3' : (φ.1 : MulAut (ggG0 3 B x L D J)) ^ 3 = 1 := by
      rw [← hnφ]
      have hn3 : n ^ 3 = 1 := by
        apply Subtype.ext
        simpa using hBexp (n : G) hnB
      rw [← map_pow, hn3, map_one]
    have hφ3 : φ ^ 3 = 1 := by
      apply Subtype.ext
      simpa using hφ3'
    rw [← map_pow, hφ3, map_one]
  · have hcard : Nat.card (realizedSubgroup R (contextImage (ggG0 3 B x L D J) B)) =
        Nat.card B := by
      rw [realizedSubgroup_card_of_le R hBI, contextImage_card_of_le_normalizer hBN hC]
    rw [hcard]
    exact hBcard
  · rw [hplane]
    exact realizedSubgroup_mono R (contextImage_mono hDB)
  · rw [hplane, realizedSubgroup_card_of_le R hDI,
      contextImage_card_of_le_normalizer (hDB.trans hBN) hC, hcardD]
  · rw [hplane]
    exact isComponentOf_realized I R hDI (hDB.trans hBN) hJcomp
  · rw [hplane]
    exact inf_centralizer_realized I R hJI (hJcomp.1.trans inf_le_left) hDj

theorem context_toral_data
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {t : StatedLieTag} {n f : ℕ}
    {ψ : (ggU t n f).K →* G}
    (hctx : GGSixCtxV2 3 B Bs x L D J (ggU t n f).D t n f ψ)
    (s1 : GGSixStepOne 3 B Bs x L D J) (hshape : Shape t f) :
    ∃ (Ω : Type) (_ : Field Ω) (_ : IsAlgClosed Ω) (_ : CharP Ω 2)
      (I : Subgroup (MulAut (ggG0 3 B x L D J)))
      (R : ShapeRealization (ggG0 3 B x L D J) I Ω)
      (a : Fin 2 → Fin Tag.E6.rank → Ωˣ),
      (letI := ZMod.algebra Ω 2; Algebra.IsAlgebraic (ZMod 2) Ω) ∧
      contextImage (ggG0 3 B x L D J) (ggG1 ψ) ≤ I ∧
      contextImage (ggG0 3 B x L D J) Bs ≤ I ∧
      realizedSubgroup R (contextImage (ggG0 3 B x L D J) Bs) ≤ torusGroup .E6 Ω ∧
      (t = .E6 → ∀ α, R.setup.ρ α = α) ∧
      (t = .twistedE6 → ∀ α, R.setup.ρ α = -α) ∧
      contextImage (ggG0 3 B x L D J) D ≤ I ∧
      planeGroup a = realizedSubgroup R (contextImage (ggG0 3 B x L D J) D) ∧
      ToralKernelContext R.setup
        (realizedSubgroup R (contextImage (ggG0 3 B x L D J) B))
        (realizedSubgroup R (contextImage (ggG0 3 B x L D J) J)) a := by
  obtain ⟨Ω, hField, hClosed, hChar, I, R, hAlg, hG1I, hBsI, hBT, hsignE, hsignT, hDI⟩ :=
    exists_lang_realization hctx s1 hshape
  obtain ⟨a, hplane, ha3⟩ := exists_plane_of_realization hctx s1 R hDI hBT
  have hBI : contextImage (ggG0 3 B x L D J) B ≤ I :=
    (contextImage_mono hctx.bstar.1).trans hBsI
  have hJleG0 : J ≤ ggG0 3 B x L D J :=
    hctx.j_isComponentOf_inf.1.trans inf_le_left
  have hJleG1 : J ≤ ggG1 ψ := hJleG0.trans (ggG0_le_ggG1 hctx.range_eq)
  have hJI : contextImage (ggG0 3 B x L D J) J ≤ I :=
    (contextImage_mono hJleG1).trans hG1I
  have hBexp : ∀ b ∈ B, b ^ 3 = 1 :=
    fun b hb => hctx.bstar.2.1.2 b (hctx.bstar.1 hb)
  have hBN : B ≤ Subgroup.normalizer (ggG0 3 B x L D J : Set G) :=
    hctx.bstar.1.trans hctx.bstar_le_normalizer
  have hDB : D ≤ B := hctx.stdSub.1.1
  have hcardD : Nat.card D = 9 := by rw [hctx.card_d]; norm_num
  have hDj : D = B ⊓ Subgroup.centralizer (J : Set G) := hctx.stdSub.1.2.2.2.2.2.2
  have hsign : (∀ α, R.setup.ρ α = α) ∨ (∀ α, R.setup.ρ α = -α) := by
    rcases hshape with ⟨ht, -⟩ | ⟨ht, -⟩
    · exact Or.inl (hsignE ht)
    · exact Or.inr (hsignT ht)
  refine ⟨Ω, hField, hClosed, hChar, I, R, a, hAlg,
    hG1I, hBsI, hBT, hsignE, hsignT, hDI, hplane, ?_⟩
  exact toralKernelContext_of_data R hBI hDI hJI hBT hplane ha3
    hBN hctx.bstar.1 hBexp hctx.pow_four_le_card_b hDB hcardD hDj
    hctx.j_isComponentOf_inf s1.1 hsign

end CFSG.StandardType
