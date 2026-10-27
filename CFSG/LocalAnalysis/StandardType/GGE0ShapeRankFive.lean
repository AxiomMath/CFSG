module

public import CFSG.LocalAnalysis.StandardType.GGE0ShapeDefs
public import CFSG.LocalAnalysis.StandardType.GGSixBstarE6ThreeFrameOn
public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsExcSixETwisted
public import CFSG.LocalAnalysis.StandardType.GGSixBstarNormalizerAut
public import CFSG.LocalAnalysis.StandardType.GGSixBstarNormalizerAutTwoLocal
public import CFSG.LocalAnalysis.StandardType.GGSixBstarNormalizerAutInduces
public import CFSG.LocalAnalysis.StandardType.GGSixBstarNoOffenderExcRestProof
public import CFSG.LocalAnalysis.StandardType.GGSixBstarModelFrameTransfer
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LocalAnalysis.StandardType.GGTableBThreeTBTwE6RankFive
public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordContrary
public import CFSG.LocalAnalysis.StandardType.GGExcKGSFCoreAux
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylTwE6SplitEmbed
import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.TwE6Aux.Field

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.LieType.Chevalley CFSG.Assembly.LowTwoRank
  CFSG.HardMathSupport.Timmesfeld.Torality CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

private theorem card_le_of_le_sylow_unique {p : ℕ} (hp : p.Prime) {G : Type} [Group G] [Finite G]
    {Bs P : Subgroup G} (hBs : IsElemAbelian p Bs) (hbs_ge : p ^ 1 ≤ Nat.card Bs)
    (huniq : ∀ E : Subgroup G, E ≤ P → IsElemAbelian p E → Nat.card E = Nat.card Bs → E = Bs)
    {E : Subgroup G} (hEP : E ≤ P) (hE : IsElemAbelian p E) :
    Nat.card E ≤ Nat.card Bs := by
  haveI : Fact p.Prime := ⟨hp⟩
  by_contra hle
  rw [not_le] at hle
  obtain ⟨s, hs⟩ := GGSFCore.exists_card_eq_pow (A := G) hBs
  obtain ⟨r, hr⟩ := GGSFCore.exists_card_eq_pow (A := G) hE
  have hsr : s < r := by
    rw [hs, hr] at hle
    exact (Nat.pow_lt_pow_iff_right hp.one_lt).mp hle
  have hs1 : 1 ≤ s := by
    rw [hs] at hbs_ge
    exact (Nat.pow_le_pow_iff_right hp.one_lt).mp hbs_ge
  obtain ⟨X, Y, hXE, hYE, hXcard, hYcard, hXY⟩ :=
    GGSFCore.exists_two_subgroups (A := G) hE hr hs1 hsr
  have hXel : IsElemAbelian p X := GGSFCore.isElemAbelian_of_le hE hXE
  have hYel : IsElemAbelian p Y := GGSFCore.isElemAbelian_of_le hE hYE
  have hXeq : X = Bs := huniq X (hXE.trans hEP) hXel (by rw [hXcard, hs])
  have hYeq : Y = Bs := huniq Y (hYE.trans hEP) hYel (by rw [hYcard, hs])
  exact hXY (hXeq.trans hYeq.symm)

private theorem card_le_card_of_sylow_unique {p : ℕ} (hp : p.Prime) {G : Type} [Group G] [Finite G]
    {M Bs : Subgroup G} (hBs : IsElemAbelian p Bs) (hbs_ge : p ^ 1 ≤ Nat.card Bs)
    (P : Sylow p M)
    (huniq : ∀ E : Subgroup G, E ≤ (P : Subgroup M).map M.subtype → IsElemAbelian p E →
      Nat.card E = Nat.card Bs → E = Bs)
    {E : Subgroup G} (hEM : E ≤ M) (hE : IsElemAbelian p E) :
    Nat.card E ≤ Nat.card Bs := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hEp : IsPGroup p E := GGSFCore.isElemAbelian_isPGroup hE
  have hE'p : IsPGroup p (E.subgroupOf M) := hEp.comap_subtype (K := M)
  obtain ⟨S, hE'S⟩ := hE'p.exists_le_sylow
  obtain ⟨m, hm⟩ := MulAction.exists_smul_eq M P S
  have hEle : E.map (MulAut.conj (m : G)⁻¹).toMonoidHom ≤
      (P : Subgroup M).map M.subtype := by
    rintro _ ⟨e, he, rfl⟩
    have he' : (⟨e, hEM he⟩ : M) ∈ ((m • P : Sylow p M) : Subgroup M) := by
      rw [hm]
      exact hE'S (Subgroup.mem_subgroupOf.mpr he)
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at he'
    obtain ⟨y, hy, hye⟩ := he'
    have hyG : (y : G) ∈ (P : Subgroup M).map M.subtype := ⟨y, hy, rfl⟩
    have hyeG : (((MulAut.conj m) • y : M) : G) = e := congrArg (fun z : M => (z : G)) hye
    rw [← hyeG]
    simpa [MulAut.smul_def, mul_assoc] using hyG
  have hbound := card_le_of_le_sylow_unique hp hBs hbs_ge huniq hEle
    (GGSFCore.isElemAbelian_map_conj hE (m : G)⁻¹)
  rwa [GGSFCore.card_map_conj] at hbound

private theorem card_le_card_bstar
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {t : StatedLieTag} {n f : ℕ}
    {ψ : (ggU t n f).K →* G}
    (hctx : GGSixCtxV2 3 B Bs x L D J (ggU t n f).D t n f ψ)
    (s1 : GGSixStepOne 3 B Bs x L D J) :
    ∀ {E : Subgroup G}, E ≤ ggM 3 B x L D J → IsElemAbelian 3 E → Nat.card E ≤ Nat.card Bs := by
  obtain ⟨P, -, huniq⟩ := s1.2.2.2.1
  intro E hEM hE
  exact card_le_card_of_sylow_unique Nat.prime_three hctx.2.1.2.1
    (le_trans (by norm_num : 3 ^ 1 ≤ 3 ^ 4) hctx.pow_four_le_card_bstar) P huniq hEM hE

private theorem pow_five_le_card_bstar_E6
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {n f : ℕ}
    {ψ : (ggU .E6 n f).K →* G}
    (hctx : GGSixCtxV2 3 B Bs x L D J (ggU .E6 n f).D .E6 n f ψ)
    (s1 : GGSixStepOne 3 B Bs x L D J) (hshape : 3 ∣ 2 ^ f - 1) :
    3 ^ 5 ≤ Nat.card Bs := by
  have hf : 1 ≤ f := hctx.2.2.2.1.1.2.1
  obtain ⟨hrange, hker⟩ := hctx.2.2.2.2.1
  have hperf : commutator ↥(ggG0 3 B x L D J) = ⊤ := hctx.2.2.2.2.2.1.1
  have hC : Subgroup.centralizer (ggG0 3 B x L D J : Set G) = ⊥ := s1.1
  have hCψ : Subgroup.centralizer (ψ.range : Set G) = ⊥ := by rw [hrange]; exact hC
  obtain ⟨χ, hχinj, hχrange, -⟩ :=
    NoOffE6Three.exists_injective_factor_E6_comp ψ hker hCψ
  have hχG0 : χ.range = ggG0 3 B x L D J := hχrange.trans hrange
  have hZ : Subgroup.center (adjointGroup .E6 (GaloisField 2 f)) = ⊥ :=
    center_adjointGroup_eq_bot (τ := .E6) (K := GaloisField 2 f)
  obtain ⟨θ⟩ := NormalizerAut.nonempty_quotient_center_mulEquiv χ hχinj hZ hχG0
  have hK : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have h3 : 3 ∣ Nat.card (GaloisField 2 f) - 1 := by rw [hK]; exact hshape
  have hlift : GGTorusLift 3 5 (adjointGroup .E6 (GaloisField 2 f)) :=
    TableBExc.ggTorusLift_adjoint_E6_three h3
  have h5rank : 5 ≤ LargeEvenTwoLocalRank 3 G :=
    le_twoLocalRank_of_torusLift Nat.prime_three hperf θ hlift
  have hBc : Nat.card B = 3 ^ LargeEvenTwoLocalRank 3 G := hctx.1.2.2.2.2.2.2.1.1.2.1
  have hB5 : 3 ^ 5 ≤ Nat.card B := by
    rw [hBc]
    exact Nat.pow_le_pow_right (by norm_num) h5rank
  exact hB5.trans (Subgroup.card_le_of_le hctx.2.1.1)

private theorem pow_five_le_card_bstar_twE6
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {n f : ℕ}
    {ψ : (ggU .twistedE6 n f).K →* G}
    (hctx : GGSixCtxV2 3 B Bs x L D J (ggU .twistedE6 n f).D .twistedE6 n f ψ)
    (s1 : GGSixStepOne 3 B Bs x L D J) (hshape : 3 ∣ 2 ^ f + 1) :
    3 ^ 5 ≤ Nat.card Bs := by
  have hf : 1 ≤ f := hctx.2.2.2.1.1.2.1
  have hE : ChevalleyExceptionalModel (↥(ggG0 3 B x L D J) ⧸
      Subgroup.center ↥(ggG0 3 B x L D J)) .twistedE6 2 f :=
    (hctx.2.2.2.2.2.1.2).chevalleyExceptionalModel (by decide)
  obtain ⟨K, hF, hfin, σ, hK, hσ, ⟨e1⟩⟩ :=
    CFSG.HardMathSupport.Dickson.Sec6.I923.exists_twistedE6RootGroup_equiv
      Nat.prime_two hf hE.2
  obtain ⟨σ', hσ', ⟨e2⟩⟩ := exists_mulEquiv_recipeR_twistedE6RootGroup (K := K) hf hK
  have hσσ : σ = σ' := RingEquiv.ext fun c => (hσ c).trans (hσ' c).symm
  subst hσσ
  let θ : ↥(ggG0 3 B x L D J) ⧸ Subgroup.center ↥(ggG0 3 B x L D J) ≃*
      TwE6Delta.RecipeR K f := e1.symm.trans e2.symm
  have hcov : GGTwE6CoverRank (TwE6Delta.RecipeR K f) :=
    ggTwE6CoverRank_recipe hf hK hshape
  have hperf : commutator ↥(ggG0 3 B x L D J) = ⊤ := hctx.2.2.2.2.2.1.1
  obtain ⟨⟨E, hEel, hEcard⟩, -⟩ := hcov ↥(ggG0 3 B x L D J) (ggQuotHom θ)
    (ggQuotHom_surjective θ) (by rw [ker_ggQuotHom]) hperf
  have hEM : E.map (Subgroup.subtype (ggG0 3 B x L D J)) ≤ ggM 3 B x L D J :=
    (Subgroup.map_subtype_le E).trans Subgroup.le_normalizer
  have hEel' : IsElemAbelian 3 (E.map (Subgroup.subtype (ggG0 3 B x L D J))) :=
    CFSG.Open.IsElemAbelian.map hEel _
  have hcard : Nat.card (E.map (Subgroup.subtype (ggG0 3 B x L D J))) = Nat.card E :=
    Subgroup.card_map_of_injective (Subgroup.subtype_injective (ggG0 3 B x L D J))
  have hle := card_le_card_bstar hctx s1 hEM hEel'
  rw [hcard] at hle
  exact hEcard.trans hle

theorem pow_five_le_card_bstar
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {t : StatedLieTag} {n f : ℕ}
    {ψ : (ggU t n f).K →* G}
    (hctx : GGSixCtxV2 3 B Bs x L D J (ggU t n f).D t n f ψ)
    (s1 : GGSixStepOne 3 B Bs x L D J) (hshape : Shape t f) :
    3 ^ 5 ≤ Nat.card Bs := by
  rcases hshape with ⟨rfl, h3⟩ | ⟨rfl, h3⟩
  · exact pow_five_le_card_bstar_E6 hctx s1 h3
  · exact pow_five_le_card_bstar_twE6 hctx s1 h3

end CFSG.StandardType
