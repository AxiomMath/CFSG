module

public import CFSG.Quasithin.EmptyFaithful.S146Main
public import CFSG.Quasithin.EmptyFaithful.S145Odd

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

theorem Setting146.theorem_14_6_11 (hedge : GoldschmidtEdgeBoundSubgroups.{0}) (h9 : Stage1469)
    (h105 : Stage14610Five) (h1 : Stage1463One) (h2 : Stage1463Two) (h3 : Stage1463Three)
    (h4 : Stage1463Four) (hA : Stage146BranchACore) (S : Setting146 G T M) :
    ∀ H : Subgroup G, IsHTM T M H → OddCoreModTwoTrivial H := by
  by_contra hcon
  push Not at hcon
  obtain ⟨H, hH, hn⟩ := hcon
  exact stepBCore hedge h9 h105 h1 h2 h3 h4 S (hA G T M S ⟨H, hH, hn⟩)

theorem Setting146.theorem_14_6_18 (S : Setting146 G T M)
    (h1611 : ∀ H : Subgroup G, IsHTM T M H → OddCoreModTwoTrivial H) {H : Subgroup G}
    (hH : InH T H) (hsolv : Group.IsSolvable ↥H) : H ≤ M := by
  by_contra hnle
  have hHM : IsHTM T M H := ⟨hH, hnle⟩
  have hTM : T ≤ M := S.hyp.m_max.1.2
  have hTsyl : IsSylowTwoOf T H := isSylowTwoOf_of_quasithinIsSylowTwo S.hyp.sylow hH.1
  have hlt : pCoreOf 2 H < H :=
    lt_of_le_of_ne (pCoreOf_le 2 H) fun heq =>
      hnle (heq ▸ (pCoreOf_two_le_of_isSylowTwoOf hTsyl).trans hTM)
  obtain ⟨P, hPH, hQP, hHP, hodd⟩ := exists_odd_normal_above_pCoreOf hsolv hlt
  exact hQP.not_ge (h1611 H hHM P hPH
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hPH).mpr hHP) hQP.le hodd)

end CFSG.Quasithin
