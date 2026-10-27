module

public import CFSG.Quasithin.Recognition.St84.Gen.BigL2Slice
public import CFSG.Quasithin.Recognition.St84.Gen.PerfectGen
public import CFSG.Quasithin.Recognition.GoldschmidtF112RSp44
public import CFSG.Quasithin.Background.GoldschmidtRankOneFacts
public import CFSG.Quasithin.Recognition.GoldschmidtF112TitsBorel
public import CFSG.RankThree.S4Free.Statement

public section

namespace CFSG.Quasithin.F112R

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.H13.F431
  CFSG.Quasithin.H13.F431.SpModel CFSG.ComponentClassification.UnbalancedCatalog.SpChain
  CFSG.Quasithin.H13.Ch9.F112Pf CFSG.LieType.BorelTits

theorem y9Sp4q : Y9Sp4q := by
  intro G _ _ L1 L2 S f hF hf3 h1 h2 hA
  have hf2 : 2 ≤ f := by omega
  have hPO := perfectOver_of_hasModelFacts_of_isL2Quot hF.1 hf2 h1 hf2 h2
    (hasModelFacts_sp4 f hf2) hA
  obtain ⟨hB, -, -⟩ := vFact_of_hasModelFacts_of_isL2Quot hf2 h1 hf2 h2
    (hasModelFacts_sp4 f hf2) hA
  obtain ⟨hB1, hB2⟩ := bigB_le_normalizer hF.1
  have hc1 := perfectCore_vertex hB1 hB hPO.1
  have hc2 := perfectCore_vertex hB2 hB hPO.2.1
  obtain ⟨Y, _, hY, T, M₁, M₂, hp, ⟨iso0⟩⟩ := hA
  have hL : CFSG.Blueprint.LieModel Y .PSp 2 2 f := by
    rcases hY with ⟨h, -⟩ | ⟨-, hL⟩
    · exact absurd h (by omega)
    · exact hL
  obtain ⟨hf, F, _, _, _, hFcard, ⟨e1⟩⟩ := exists_equiv_antiSp hL
  have hy1 := hp.map e1
  obtain ⟨h, -, hh⟩ := IsSylowTwoOf.exists_conj hy1.1 (borel_antiSp (F := F) hf hFcard).sylow
  let E : Y ≃* antiSp F := e1.trans (MulAut.conj h)
  have hy2 : IsYAmalgamPair (antiUnipotent F) (M₁.map E.toMonoidHom) (M₂.map E.toMonoidHom) := by
    have := hp.map E
    have hTD : T.map E.toMonoidHom = antiUnipotent F := by
      rw [hh, Subgroup.map_map]
      rfl
    rwa [hTD] at this
  have ψ1 : ↥(L1 ⊔ bigB L1 L2 S) ≃* ↥(M₁.map E.toMonoidHom) :=
    iso0.φ1.trans (M₁.equivMapOfInjective E.toMonoidHom E.injective)
  have ψ2 : ↥(L2 ⊔ bigB L1 L2 S) ≃* ↥(M₂.map E.toMonoidHom) :=
    iso0.φ2.trans (M₂.equivMapOfInjective E.toMonoidHom E.injective)
  have hv : (IsShort2 (perfectCore (M₁.map E.toMonoidHom)) ∧
        IsLin2Type (perfectCore (M₁.map E.toMonoidHom)) f) ∧
      (IsShort2 (perfectCore (M₂.map E.toMonoidHom)) ∧
        IsLin2Type (perfectCore (M₂.map E.toMonoidHom)) f) := by
    rcases yam_antiSp hf hFcard hy2 with ⟨e₁, e₂⟩ | ⟨e₁, e₂⟩
    · rw [e₁, e₂]
      exact ⟨sp_vertex hf hFcard 0, sp_vertex hf hFcard 1⟩
    · rw [e₁, e₂]
      exact ⟨sp_vertex hf hFcard 1, sp_vertex hf hFcard 0⟩
  obtain ⟨hs1, hl1⟩ := short_lin2_of_perfectCore hc1 ψ1 hv.1
  obtain ⟨hs2, hl2⟩ := short_lin2_of_perfectCore hc2 ψ2 hv.2
  exact ⟨⟨Gold14610.isBlock2_of_short hs1 le_rfl Subgroup.le_normalizer, hl1⟩,
    ⟨Gold14610.isBlock2_of_short hs2 le_rfl Subgroup.le_normalizer, hl2⟩, hPO⟩

end CFSG.Quasithin.F112R
