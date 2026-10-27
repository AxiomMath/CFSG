module

public import CFSG.Quasithin.EmptyFaithful.R3c17G
public import CFSG.Quasithin.EmptyFaithful.R3c17E
public import CFSG.Quasithin.EmptyFaithful.R3c17F
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B113LieG2
public import CFSG.LieType.Chevalley.AdjointCenter
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDescentEndpoint
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFixedTransfer
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelModel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixComponentsCover
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixModelGeometry
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalTraceZeroCoordinates
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBLinear
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticRepresentationOdd
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpSuzukiCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpWedge
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115EvenLie
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bPairs
public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassical
public import CFSG.LocalAnalysis.QuasithinUnique.K1.ExceptionalCat
public import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.LowRank

public section

namespace CFSG.Quasithin.R3c17

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.Chevalley CFSG.Blueprint
  CFSG.Blueprint.Chevalley CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique.Setup.X6
  CFSG.Quasithin.R3c16 CFSG.Quasithin.R3c14 CFSG.Quasithin.R3c10 CFSG.Quasithin.R3c15
  CFSG.QuasithinUnique.K1 CFSG.QuasithinUnique.B113Lie CFSG.ComponentClassification.UnbalancedCatalog
open scoped commutatorElement Pointwise

section Main

theorem centralScalar_g2
    {X : Type} [Group X] [Finite X] {f : ℕ} (hf : 2 ≤ f)
    (hX : ChevalleyExceptionalModel X .G2 2 f) : CentralScalar X := by
  intro T V hT hVT hV4 hTV y hyV k hk hyn
  classical
  obtain ⟨K, hF, hFin, hcp, φ, hK, hφ, -, -⟩ := even_rank_two_residual_G2 hX hT
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfm : Finite (ModGL Tag.G2 K) := finite_modGL
  obtain ⟨hT2, -⟩ := K1.isSylowTwoOf_top_iff.mp hT
  let ψ : X →* ModGL Tag.G2 K := (adjointGroup Tag.G2 K).subtype.comp φ.toMonoidHom
  have hψ : Function.Injective ψ := Subtype.val_injective.comp φ.injective
  have hUC : posUnipotent Tag.G2 K ≤ adjointGroup Tag.G2 K := posUnipotent_le_adjointGroup
  have hTU : T.map ψ = posUnipotent Tag.G2 K := by
    have : T.map ψ = (T.map φ.toMonoidHom).map (adjointGroup Tag.G2 K).subtype :=
      (Subgroup.map_map _ _ _).symm
    rw [this, hφ]
    exact Subgroup.map_subgroupOf_eq_of_le hUC
  have hψC : ∀ x : X, ψ x ∈ adjointGroup Tag.G2 K := fun x => (φ x).2
  have hV'U : V.map ψ ≤ posUnipotent Tag.G2 K := hTU ▸ Subgroup.map_mono hVT
  have hV'4 : Nat.card (V.map ψ) = 4 := by
    rw [← hV4]
    exact (Nat.card_congr (V.equivMapOfInjective ψ hψ).toEquiv).symm
  have hUN : posUnipotent Tag.G2 K ≤
      Subgroup.normalizer ((V.map ψ : Subgroup (ModGL Tag.G2 K)) : Set (ModGL Tag.G2 K)) := by
    rw [← hTU]
    rintro _ ⟨t, ht, rfl⟩
    exact mem_normalizer_map_of_mem ψ (hTV ht)
  have hMne : adjointGroup Tag.G2 K ⊓
      Subgroup.normalizer ((V.map ψ : Subgroup (ModGL Tag.G2 K)) : Set (ModGL Tag.G2 K)) ≠
      adjointGroup Tag.G2 K := by
    intro hMC'
    have hCN : adjointGroup Tag.G2 K ≤
        Subgroup.normalizer ((V.map ψ : Subgroup (ModGL Tag.G2 K)) : Set (ModGL Tag.G2 K)) :=
      fun g hg => (show g ∈ adjointGroup Tag.G2 K ⊓ Subgroup.normalizer
        ((V.map ψ : Subgroup (ModGL Tag.G2 K)) : Set (ModGL Tag.G2 K)) from hMC'.symm ▸ hg).2
    have hV'C : V.map ψ ≤ adjointGroup Tag.G2 K := hV'U.trans hUC
    have hnorm : ((V.map ψ).subgroupOf (adjointGroup Tag.G2 K)).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hV'C).2 hCN
    obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem Tag.G2).length
    obtain ⟨-, ⟨PV, hPV⟩, hUV, -⟩ := exceptional_ordinary_Sylow_opposition Tag.G2 K 2 w₀ hw₀
    have hU₁2 : IsPGroup 2 ↥((posUnipotent Tag.G2 K).subgroupOf (adjointGroup Tag.G2 K)) :=
      hφ ▸ hT2.map φ.toMonoidHom
    have hV₁U : (V.map ψ).subgroupOf (adjointGroup Tag.G2 K) ≤
        (posUnipotent Tag.G2 K).subgroupOf (adjointGroup Tag.G2 K) := fun x hx => hV'U hx
    have hV₁2 : IsPGroup 2 ↥((V.map ψ).subgroupOf (adjointGroup Tag.G2 K)) := hU₁2.to_le hV₁U
    have hle := hV₁2.le_sylow_of_normal PV
    rw [hPV] at hle
    have hbot : V.map ψ ≤ ⊥ := by
      intro x hx
      have hxU : x ∈ posUnipotent Tag.G2 K := hV'U hx
      have hxV : x ∈ negUnipotent Tag.G2 K :=
        hle (show (⟨x, hV'C hx⟩ : adjointGroup Tag.G2 K) ∈
          (V.map ψ).subgroupOf (adjointGroup Tag.G2 K) from hx)
      have : x ∈ posUnipotent Tag.G2 K ⊓ negUnipotent Tag.G2 K := ⟨hxU, hxV⟩
      rwa [hUV] at this
    have h1 : Nat.card (V.map ψ) = 1 := by
      have : V.map ψ = ⊥ := le_bot_iff.1 hbot
      rw [this]
      exact Subgroup.card_bot
    omega
  have hyM : ψ y ∈ adjointGroup Tag.G2 K ⊓
      Subgroup.normalizer ((V.map ψ : Subgroup (ModGL Tag.G2 K)) : Set (ModGL Tag.G2 K)) :=
    ⟨hψC y, mem_normalizer_map_of_mem ψ hyV⟩
  have hk' : (ψ y) ^ (3 ^ k) = 1 := by rw [← map_pow, hk, map_one]
  have hyn' : ¬ ∀ v ∈ V.map ψ, ψ y * v = v * ψ y := by
    intro h
    apply hyn
    intro v hv
    apply hψ
    rw [map_mul, map_mul]
    exact h (ψ v) (Subgroup.mem_map_of_mem ψ hv)
  obtain ⟨ha, hb⟩ := g2_core hK4 hV'U hV'4 inf_le_left (le_inf hUC hUN) hMne inf_le_right hyM hk'
    hyn'
  have hcentral : ∀ v ∈ V, ∀ q ∈ posUnipotent Tag.G2 K, q * ψ v = ψ v * q :=
    fun v hv q hq => ha q hq (ψ v) (Subgroup.mem_map_of_mem ψ hv)
  constructor
  · intro v hv t ht
    apply hψ
    rw [map_mul, map_mul]
    exact ha (ψ t) (hTU ▸ Subgroup.mem_map_of_mem ψ ht) (ψ v) (Subgroup.mem_map_of_mem ψ hv)
  · intro g hg z hzT hzc hz1 hgz v hv
    obtain ⟨l, hl⟩ := hb (ψ g) ⟨hψC g, mem_normalizer_map_of_mem ψ hg⟩
    have hzU : ψ z ∈ posUnipotent Tag.G2 K := hTU ▸ Subgroup.mem_map_of_mem ψ hzT
    obtain ⟨c, hc⟩ := g2_center_xc hK4 hzU (fun q hq => by
      rw [← hTU] at hq
      obtain ⟨t, ht, rfl⟩ := hq
      rw [← map_mul, ← map_mul, hzc t ht])
    have hc0 : c ≠ 0 := by
      intro h0
      apply hz1
      apply hψ
      rw [hc, h0, map_one]
      exact pinnedX_zero _ _ _
    have hl1 : l = 1 := by
      have h1 := hl c
      rw [← hc] at h1
      have h2 : ψ g * ψ z * (ψ g)⁻¹ = ψ z := by
        rw [← map_mul, ← map_inv, ← map_mul, hgz]
        group
      rw [h2, hc] at h1
      have h3 := pinnedX_injective (τ := Tag.G2) (R := K) g2c h1
      exact (mul_eq_right₀ hc0).1 h3.symm
    obtain ⟨d, hd⟩ := g2_center_xc hK4 (hV'U (Subgroup.mem_map_of_mem ψ hv))
      (fun q hq => hcentral v hv q hq)
    apply hψ
    rw [map_mul, map_mul]
    have h5 : ψ g * ψ v * (ψ g)⁻¹ = ψ v := by
      rw [hd, hl d, hl1, one_mul]
    calc ψ g * ψ v = (ψ g * ψ v * (ψ g)⁻¹) * ψ g := by group
      _ = ψ v * ψ g := by rw [h5]

end Main

section Elim

theorem zeta_facts_g2
    {X : Type} [Group X] [Finite X] {f : ℕ} (hf : 2 ≤ f)
    (hX : ChevalleyExceptionalModel X .G2 2 f) {T : Subgroup X} (hT : IsSylowTwoOf T ⊤) :
    (∀ β : X ≃* X, (∀ q ∈ T, β q = q) → ∃ x : X, ∀ y : X, β y = x⁻¹ * y * x) ∧
    (∀ φ : MulAut X, (∀ u ∈ T, φ u = u) → Odd (orderOf φ) → φ = 1) ∧
    (∀ g : X, (∀ y : X, g * y = y * g) → g = 1) := by
  obtain ⟨K, hF, hFin, hcp, φ, hK, hφ, -, -⟩ := even_rank_two_residual_G2 hX hT
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  refine ⟨(SylowCentralizingAutInner.of_mulEquiv φ (sylowCentralizingAutInner_g2 hK4)) T hT,
    (g2_sylowFacts hX hT).2.2, ?_⟩
  intro g hg
  have hgc : φ g ∈ Subgroup.center ↥(adjointGroup Tag.G2 K) :=
    Subgroup.mem_center_iff.2 fun z => by
      obtain ⟨x, rfl⟩ := φ.surjective z
      rw [← map_mul, ← map_mul, hg x]
  rw [center_adjointGroup_eq_bot] at hgc
  exact φ.injective (by rw [map_one]; exact Subgroup.mem_bot.1 hgc)

theorem not_elConfig_of_g2_scalar
    {X : Type} [Group X] [Finite X] {f : ℕ} (hf : 2 ≤ f)
    (hX : ChevalleyExceptionalModel X .G2 2 f) : ¬ ElConfig X := by
  rintro ⟨T, V, H, ζ, hT, hd⟩
  obtain ⟨hA, hOdd, hZ⟩ := zeta_facts_g2 hf hX hT
  exact not_elData_of_centralScalar hT hA hOdd hZ (centralScalar_g2 hf hX) hd

variable {G : Type} [Group G] [Finite G]

theorem elim15343_of_g2_scalar
    {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}
    (c : CtxComp1 T Mc M V₁ V₂ Yp I L t) (o : Concl15343Open T M V₁ V₂ Yp I L)
    (hN : I ≤ Subgroup.normalizer (L : Set G)) (hYL : Yp ≤ L) {f : ℕ} (hf : 2 ≤ f)
    (h : ChevalleyExceptionalModel (↥L ⧸ Subgroup.center ↥L) .G2 2 f) : False :=
  not_elConfig_of_g2_scalar hf h (elConfig_of_ctx1 c o hN hYL)

theorem cl15335_of_g2_scalar
    {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G} (h113 : StageLemma14113)
    (c : CtxComp2 T Mc M V₁ V₂ Yp I L t) (hN : I ≤ Subgroup.normalizer (L : Set G))
    (hYL : Yp ≤ L) {f : ℕ} (hf : 2 ≤ f)
    (h : ChevalleyExceptionalModel (↥L ⧸ Subgroup.center ↥L) .G2 2 f) : False := by
  rcases c.hyp.cases with hY | hU
  · exact cl_case1_of_centralScalar h113 c hN hYL hY (centralScalar_g2 hf h)
  · exact not_elConfig_of_g2_scalar hf h (elConfig_of_ctx2 h113 c hN hYL hU)

end Elim

section Final

theorem input15343ElimLieRest10_proved :
    Input15343ElimLieRest10 := by
  intro G _ _ T Mc M V₁ V₂ Yp I L t c o hmin hN hIeq hYL hRest
  obtain ⟨f, hf, h⟩ := hRest
  exact elim15343_of_g2_scalar c o hN hYL hf h

theorem input15343ElimLieRest_proved :
    R3c10.Input15343ElimLieRest :=
  input15343ElimLieRest_of_rest10 input15343ElimLieRest10_proved

@[expose] def Lemma115LieHighRest9 (X : Type) [Group X] : Prop :=
  ∃ f : ℕ, 2 ≤ f ∧ CFSG.Assembly.LowTwoRank.StatedClassicalModel X .PSp 2 2 f

theorem lemma115LieHighRest8_cases_rest9 {X : Type} [Group X] (h : Lemma115LieHighRest8 X) :
    Lemma115LieHighRest9 X ∨ ∃ f : ℕ, 2 ≤ f ∧ ChevalleyExceptionalModel X .G2 2 f := by
  obtain ⟨f, ⟨hf, h1⟩ | ⟨hf, h2⟩⟩ := h
  · exact Or.inl ⟨f, hf, h1⟩
  · exact Or.inr ⟨f, hf, h2⟩

@[expose] def Input15335CloseLieRest9 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G),
    CtxComp2 T Mc M V₁ V₂ Yp I L t →
      (∀ K : Subgroup G, IsHPlus Yp (Sgp153 T V₁) M K → K ≤ I → K = I) →
        I ≤ Subgroup.normalizer (L : Set G) → I = L ⊔ Sgp153 T V₁ → Yp ≤ L →
          Lemma115LieHighRest9 (↥L ⧸ Subgroup.center ↥L) → False

theorem input15335CloseLieRest8_of_rest9
    (h113 : StageLemma14113) (kR : Input15335CloseLieRest9) : Input15335CloseLieRest8 := by
  intro G _ _ T Mc M V₁ V₂ Yp I L t c hmin hN hIeq hYL hRest
  rcases lemma115LieHighRest8_cases_rest9 hRest with h9 | ⟨f, hf, hg2⟩
  · exact kR G T Mc M V₁ V₂ Yp I L t c hmin hN hIeq hYL h9
  · exact cl15335_of_g2_scalar h113 c hN hYL hf hg2

theorem input15335CloseLieRest_of_rest9
    (h113 : StageLemma14113) (kR : Input15335CloseLieRest9) : Input15335CloseLieRest :=
  input15335CloseLieRest_of_rest8 h113 (input15335CloseLieRest8_of_rest9 h113 kR)

end Final

end CFSG.Quasithin.R3c17
