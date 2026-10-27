module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS143W2Ctx
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS143W2Weak
public import CFSG.Quasithin.EmptyFaithful.R3c19B

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1
  CFSG.QuasithinUnique.Tight CFSG.QuasithinUnique.BenderBranch
  CFSG.ComponentClassification.AschbacherTightEmbedding

namespace S143

namespace InspW2

@[expose] def LocalFactsHold : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G) (g : G) (A : Subgroup G) (t d x : G),
    Ctx T M g A t d x → LocalFacts T d x

@[expose] def ComponentAnalysis : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G) (g : G) (A : Subgroup G) (t d x : G),
    Ctx T M g A t d x → LocalFacts T d x →
      ∃ L : Subgroup G, IsComponentIn L (Gw d x) ∧ InspData ↥L

theorem inspW_apply (hWo : InspWo) (hWi : InspWiw) {L : Type} [Group L] [Finite L]
    (h : InspData L) : CFSG.Assembly.LowTwoRank.StatedClassicalModel L .PSU 3 3 1 := by
  obtain ⟨hq, Gc, _, _, ρ, ž, Ŝ, Kh, hin, hcase⟩ := h
  rcases hcase with hcd | ⟨hl, hz⟩
  · exact (hWo L hq hcd Gc ρ ž Ŝ Kh hin).elim
  · exact hWi L hq hl Gc ρ ž Ŝ Kh hin hz

theorem lemma14322InspectW3_of_parts (hloc : LocalFactsHold) (hcomp : ComponentAnalysis)
    (hWo : InspWo) (hWi : InspWiw) (h4 : Clause4) : Lemma14322InspectW3 := by
  intro G _ _ T M g A t c c18 c19 hΓ c21 d hD hd4 x hxL hx3 hSyl hN1 hN2 hR hO
  have h : Ctx T M g A t d x :=
    ⟨c, c18, c19, hΓ, c21, hD, hd4, hxL, hx3, hSyl, hN1, hN2, hR, hO⟩
  obtain ⟨L, hL, hdata⟩ := hcomp G T M g A t d x h (hloc G T M g A t d x h)
  have hU33 := inspW_apply hWo hWi hdata
  exact ⟨L, hL.1, hU33, h4 G T M g A t d x h L hL hU33⟩

theorem lemma14322InspectW2_of_parts (hloc : LocalFactsHold) (hcomp : ComponentAnalysis)
    (hWo : InspWo) (hWi : InspWiw) (h4 : Clause4) : Lemma14322InspectW2 :=
  lemma14322InspectW2_of_inspectW3 (lemma14322InspectW3_of_parts hloc hcomp hWo hWi h4)

end InspW2

end S143

end CFSG.Quasithin
