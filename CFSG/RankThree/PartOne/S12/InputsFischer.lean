module

public import CFSG.RankThree.PartTwo.Sec7.ThreeTranspositions

public section

namespace CFSG.RankThree.PartOne

open CFSG.LocalAnalysis.GorensteinLyons (IsThreeTranspositions)
open CFSG.RankThree.PartTwo.Sec7 (Item72 Item73 localSet)

@[expose] def InFischer44 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (D : Set G), IsThreeTranspositions D →
    (∀ d ∈ D, ∀ e ∈ D, ∃ g : G, g * d * g⁻¹ = e) → ∀ d ∈ D, ∀ n : ℕ, 3 ≤ n → n ≤ 5 →
      Nonempty (Subgroup.closure (localSet D d) ≃* Equiv.Perm (Fin n)) →
        Nonempty (G ≃* Equiv.Perm (Fin (n + 2))) ∨
          n = 3 ∧ ¬ CFSG.pCore 3 G ≤ Subgroup.center G

theorem item73_of_inFischer44 (h : InFischer44) : Item73 :=
  fun G _ _ D hD ht d hd n hn hiso => h G D hD ht d hd n (by omega) (by omega) hiso

end CFSG.RankThree.PartOne
