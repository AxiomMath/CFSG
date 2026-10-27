module

public import CFSG.RankThree.GF2n.Stroth80.Sec11Stmt
public import CFSG.RankThree.GF2n.Stroth80.Sec111Order

public section

namespace CFSG.RankThree.GF2n.Stroth80

theorem stroth111a_holds :
    ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ),
      Width Q Z n → 2 < n → ∀ m ∈ M,
        m ∈ Subgroup.normalizer ((B ⊔ Z : Subgroup G) : Set G) ↔
          m ∈ Subgroup.normalizer (LB M Q B : Set G) := by
  intro G _ _ M Q Z B hc n hw hn m hm
  exact stroth_11_1a hc hw hn hm

theorem stroth111b_holds : Stroth111bStatement := by
  intro G _ _ M Q Z B _ hc n hw hn
  exact ⟨stroth_11_1b_i hc hw hn, fun h hH hL hB => stroth_11_1b_ii hc hw hH hL hB⟩

end CFSG.RankThree.GF2n.Stroth80
