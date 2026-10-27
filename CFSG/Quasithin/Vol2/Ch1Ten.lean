module

public import CFSG.Quasithin.Vol2.Ch1Chief
public import CFSG.Quasithin.Vol2.Ch1Unique

public section

open CFSG.QuasithinUnique (quasithinIsQTKECat)

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G]

theorem lemma_1_2_10_of_maximal (hK : quasithinIsQTKECat G) (hs : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) (h36 : A36ForSQTK) (h37 : A37ForSQTK)
    (h39 : A39ForSQTK) {T L H : Subgroup G} (hT : quasithinIsSylowTwo T)
    (hL : quasithinIsMaximalLocal T L) (hH : InH (L ⊔ T) H) :
    List.TFAE [quasithinIsFaithfulLocal T L, ∃ V, IsTwoReducedIn H V ∧ ⁅V, L⁆ ≠ ⊥,
      ⁅twoReducedJoin H, L⁆ ≠ ⊥] := by
  obtain ⟨S, rfl⟩ := exists_sylow_of_quasithinIsSylowTwo hT
  have hLc := lemma_1_2_7_one hK hs hnab h37 h39 hT hL hH
  have hH' : InH (S : Subgroup G) H := ⟨le_sup_right.trans hH.1, hH.2⟩
  exact lemma_1_2_10_of_a36 hK hs hnab h36 S hH' hLc

end CFSG.Quasithin
