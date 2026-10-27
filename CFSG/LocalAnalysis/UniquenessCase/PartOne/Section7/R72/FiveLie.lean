module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.R72.Fstar
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.SEFive.LinTwo
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.SEFive.Unitary
import CFSG.Adapters.TauCetiLieModels
import CFSG.Models.Blueprint

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.R72

open CFSG.LocalAnalysis.UniquenessCase.UC22 (R72Shape)
open CFSG.LocalAnalysis.UniquenessCase.UC22.F07 (QuotK7 LKQuot7)

variable {G : Type} [Group G] [Finite G]

theorem r72Shape_of_isLinTwoIndex (k : Sec7Core4 G) {H : Subgroup G} (hH : k.Config H) {n : ℕ}
    {d : TauCeti.ValidLieTypeIndex} (hd : CFSG.AGLEmbedding.IsLinTwoIndex k.p n d)
    (e : ↥(CFSG.generalizedFitting (QuotK7 k.p H)) ≃* CFSG.AGLEmbedding.CatGroup d) :
    R72Shape k.p (LKQuot7 k.p H) := by
  haveI : Fact k.p.Prime := ⟨k.prime⟩
  have hn : 1 ≤ n := by
    obtain ⟨q, -, -, rfl⟩ := hd
    exact q.exponent_pos
  obtain ⟨e'⟩ := CFSG.AGLEmbedding.nonempty_mulEquiv_psl2GF_of_isLinTwoIndex hd
  have hF := (SEFive.pElements_psl2GF (X := QuotK7 k.p H) k.odd hn
    (CFSG.pPrimeCore_quotient_eq_bot k.prime) (k.isStronglyPEmbedded_map_quotient_pPrimeCore hH)
    (e.trans e')).2
  refine r72Shape_lkQuot7_of_eq
    (imageModK_opp_eq_generalizedFitting k hH (forall_pow_mem_of_forall_mem_N k hH hF))
    (Or.inl ⟨n, ?_⟩)
  obtain ⟨⟨d₀, hv⟩, rfl⟩ : ∃ d' : TauCeti.ValidLieTypeIndex, d' = d := ⟨d, rfl⟩
  obtain ⟨q, hq, hqp, hqn⟩ := hd
  obtain rfl : d₀ = .A 1 q := hq
  have h := (CFSG.Models.lieModel_A 1 q hv e).toBlueprint (by decide)
  rw [hqp, hqn] at h
  exact h

theorem r72Shape_of_isUnitaryIndex (k : Sec7Core4 G) {H : Subgroup G} (hH : k.Config H)
    {d : TauCeti.ValidLieTypeIndex} (hd : CFSG.AGLEmbedding.IsUnitaryIndex k.p d)
    (e : ↥(CFSG.generalizedFitting (QuotK7 k.p H)) ≃* CFSG.AGLEmbedding.CatGroup d) :
    R72Shape k.p (LKQuot7 k.p H) := by
  haveI : Fact k.p.Prime := ⟨k.prime⟩
  have hF := (SEFive.pElements_unitary (X := QuotK7 k.p H) hd
    (CFSG.pPrimeCore_quotient_eq_bot k.prime) (k.isStronglyPEmbedded_map_quotient_pPrimeCore hH)
    e).2
  refine r72Shape_lkQuot7_of_eq
    (imageModK_opp_eq_generalizedFitting k hH (forall_pow_mem_of_forall_mem_N k hH hF))
    (Or.inr (Or.inl ?_))
  obtain ⟨⟨d₀, hv⟩, rfl⟩ : ∃ d' : TauCeti.ValidLieTypeIndex, d' = d := ⟨d, rfl⟩
  obtain ⟨q, hqp, hq⟩ := hd
  obtain rfl : d₀ = .twistedA 2 q := hq
  have h := (CFSG.Models.lieModel_twistedA 2 q hv e).toBlueprint (by decide)
  have hc : TauCeti.ValidLieTypeIndex.characteristic ⟨.twistedA 2 q, hv⟩ = q.p :=
    TauCeti.LieTypeIndex.characteristic_twistedA 2 q
  rw [hc, hqp] at h
  exact ⟨_, h⟩

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.R72
