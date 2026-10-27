module

public import CFSG.Quasithin.EmptyFaithful.T1521SJ
public import CFSG.Quasithin.EmptyFaithful.S153WJOff

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

variable {G : Type} [Group G]

theorem thompsonJ_le_innerPart_of_offender {S L V : Subgroup G} (hVS : V ≤ S)
    (hV : IsElemAbelian 2 V)
    (hC : S ⊓ Subgroup.centralizer (V : Set G) ≤ innerPart1521 S L)
    (hOff : ∀ A : Subgroup G, IsElemAbelian 2 A → A ≤ S →
      Nat.card V * Nat.card ↥(A ⊓ Subgroup.centralizer (V : Set G)) ≤
        Nat.card A * Nat.card ↥(A ⊓ V) → A ≤ Subgroup.centralizer (V : Set G)) :
    thompsonJ S ≤ innerPart1521 S L := by
  refine iSup₂_le fun A hA => ?_
  have hineq := W153.card_mul_le_of_isMaxElemAbelian hA hV hVS
  exact (le_inf hA.1 (hOff A hA.2.1 hA.1 hineq)).trans hC

end CFSG.Quasithin
