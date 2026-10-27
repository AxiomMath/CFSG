module

public import CFSG.Quasithin.Recognition.St84.Gen.BigL2Slice
import CFSG.Quasithin.Recognition.St84.Gen.PerfectGen
import CFSG.Quasithin.Recognition.GoldschmidtF112RSp44
import CFSG.Quasithin.Recognition.St84.Gen.L3qVertex
import CFSG.Quasithin.Vol2.GoldschmidtF431L3LieModel
import CFSG.Quasithin.Vol2.Ch9Sec3FactsF112PfC
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.ClassicalGroups
public import CFSG.GH74.GLS.Classes
public import CFSG.GH74.Statements
public import CFSG.LieType.Simplicity.Classical
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Reduce
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesBasic
public import CFSG.Quasithin.Background.A3StructureFacts
public import CFSG.Quasithin.Background.F9FiveStruct
public import CFSG.Quasithin.Background.F9G2
public import CFSG.Quasithin.Background.F9Geometry
public import CFSG.Quasithin.Background.GoldschmidtRankOneFacts
public import CFSG.Quasithin.EmptyFaithful.S1421Defs
public import CFSG.Quasithin.EmptyFaithful.S142Statements
public import CFSG.Quasithin.H13.A5S1326
public import CFSG.Quasithin.H13.A5Top
public import CFSG.Quasithin.H13.StatementsL3
public import CFSG.Quasithin.Recognition.GoldschmidtF112TitsBorel
public import CFSG.RankThree.S4Free.Statement

public section

namespace CFSG.Quasithin.F112R

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.H13.F431
  CFSG.Quasithin.H13.Ch9.F112Pf CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.LocalAnalysis.ComponentInitial.LinearFieldFour

theorem y9L3q : Y9L3q := by
  intro G _ _ L1 L2 S f hF hf3 h1 h2 hA
  have hf2 : 2 ≤ f := by omega
  have hPO := perfectOver_of_hasModelFacts_of_isL2Quot hF.1 hf2 h1 hf2 h2
    (hasModelFacts_l3 f hf2) hA
  obtain ⟨hB, -, -⟩ := vFact_of_hasModelFacts_of_isL2Quot hf2 h1 hf2 h2
    (hasModelFacts_l3 f hf2) hA
  obtain ⟨hB1, hB2⟩ := bigB_le_normalizer hF.1
  have hc1 := perfectCore_vertex hB1 hB hPO.1
  have hc2 := perfectCore_vertex hB2 hB hPO.2.1
  obtain ⟨Y, _, hY, T, N₁, N₂, hp, ⟨iso0⟩⟩ := hA
  have hL : CFSG.Blueprint.LieModel Y .PSL 3 2 f := hY
  obtain ⟨-, F, _, _, _, hFcard, ⟨e1⟩⟩ := CFSG.Quasithin.H13.F431.L3.exists_equiv_projSL3 hL
  have hy1 := hp.map e1
  obtain ⟨h, -, hh⟩ := IsSylowTwoOf.exists_conj hy1.1
    (CFSG.QuasithinUnique.Fin257.L3.isSylowTwoOf_U (F := F))
  let E : Y ≃* projectiveSL 3 F := e1.trans (MulAut.conj h)
  have hy2 : IsYAmalgamPair (projUnitriangular 3 F) (N₁.map E.toMonoidHom)
      (N₂.map E.toMonoidHom) := by
    have := hp.map E
    have hTD : T.map E.toMonoidHom = projUnitriangular 3 F := by
      rw [hh, Subgroup.map_map]
      rfl
    rwa [hTD] at this
  have hv : (IsShort2 (perfectCore (N₁.map E.toMonoidHom)) ∧
        IsLin2Type (perfectCore (N₁.map E.toMonoidHom)) f) ∧
      (IsShort2 (perfectCore (N₂.map E.toMonoidHom)) ∧
        IsLin2Type (perfectCore (N₂.map E.toMonoidHom)) f) := by
    rcases Borel252.BorelData.yam_cases Borel252.L3.borelData_L3
      CFSG.Quasithin.H13.F431.L3.no_normal_two_subgroup hy2 with ⟨e₁, e₂⟩ | ⟨e₁, e₂⟩
    · rw [e₁, e₂]
      exact ⟨PointVertex.l3_vertex_V1 (F := F) hf2 hFcard,
        LineVertex.l3_vertex_V2 (F := F) hf2 hFcard⟩
    · rw [e₁, e₂]
      exact ⟨LineVertex.l3_vertex_V2 (F := F) hf2 hFcard,
        PointVertex.l3_vertex_V1 (F := F) hf2 hFcard⟩
  have ψ1 : ↥(L1 ⊔ bigB L1 L2 S) ≃* ↥(N₁.map E.toMonoidHom) :=
    iso0.φ1.trans (N₁.equivMapOfInjective E.toMonoidHom E.injective)
  have ψ2 : ↥(L2 ⊔ bigB L1 L2 S) ≃* ↥(N₂.map E.toMonoidHom) :=
    iso0.φ2.trans (N₂.equivMapOfInjective E.toMonoidHom E.injective)
  obtain ⟨hs1, hl1⟩ := short_lin2_of_perfectCore hc1 ψ1 hv.1
  obtain ⟨hs2, hl2⟩ := short_lin2_of_perfectCore hc2 ψ2 hv.2
  exact ⟨⟨Gold14610.isBlock2_of_short hs1 le_rfl Subgroup.le_normalizer, hl1⟩,
    ⟨Gold14610.isBlock2_of_short hs2 le_rfl Subgroup.le_normalizer, hl2⟩, hPO⟩

end CFSG.Quasithin.F112R
