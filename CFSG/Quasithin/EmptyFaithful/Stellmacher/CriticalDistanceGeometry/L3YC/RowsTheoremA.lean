module

public import CFSG.Quasithin.Vol2.Ch1List

public section

open CFSG.QuasithinUnique (quasithinIsQTKECat)

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace Stellmacher.CD.L3YC

variable {G : Type} [Group G] [Finite G]

theorem exists_component_row (hQ : quasithinIsQTKECat G) (hs : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) (h37 : A37ForSQTK) (h39 : A39ForSQTK) (h312 : A312ForSQTK)
    {H S L : Subgroup G} (hH : pCoreOf 2 H ≠ ⊥) (hS : IsSylowTwoOf S H) (hLH : L ≤ H)
    (hL : L ∈ lFamily S) :
    ∃ L₁ ∈ cComp H, L ≤ L₁ ∧
      (modO2Image H L = modO2Image H L₁ ∨ A312Case (modO2Image H L) (modO2Image H L₁) ∨
        A312Nonquasi (modO2Image H L) (modO2Image H L₁)) := by
  obtain ⟨L₁, h1, h2⟩ := lemma_1_2_4_exists hQ hs hnab h37 h39 hH hS hLH hL
  exact ⟨L₁, h1, h2, lemma_1_2_4_list hQ hs hnab h312 hH hS hLH hL h1 h2⟩

end Stellmacher.CD.L3YC

end CFSG.Quasithin
