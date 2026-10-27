module

public import CFSG.Quasithin.EmptyFaithful.S152Y18
public import CFSG.Quasithin.EmptyFaithful.S152Y15

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

namespace S152Y

variable {G : Type} [Group G] [Finite G] {T Mc M : Subgroup G}

theorem concl_of_dihedral (h : Data T Mc M) (h113 : StageLemma14113) (hOm : Om4IsoStatement)
    {n : ℕ} [NeZero n] [Fact n.Prime] (hn : Odd n) (hn36 : 2 * n ≠ 36)
    (e : ↥(mBar0 T Mc M) ≃* DihedralGroup n)
    (hinv : ∀ x ∈ autOn T (V154 T Mc M), x ^ 2 = 1 → x ≠ 1 → x ∈ mBar0 T Mc M) :
    autOn (yOf152 T Mc M) (V154 T Mc M) ≠ ⊥ ∧
      autOn (yOf152 T Mc M) (V154 T Mc M) =
        ⁅autOn (yOf152 T Mc M) (V154 T Mc M), autOn (rcOf Mc M) (V154 T Mc M)⁆ ∧
      Case15203i T Mc M := by
  obtain ⟨hcard, hYb, hce, hK, hcent⟩ := nonThree_main h h113 hn e hinv
  refine ⟨?_, hce, hYb, hcent, fun hThree => ?_⟩
  · rw [hYb]
    intro hbot
    have h1 : Nat.card (oTwoUpper (mBar0 T Mc M)) = 1 := by rw [hbot]; exact Subgroup.card_bot
    rw [hcard] at h1
    exact (Fact.out : n.Prime).one_lt.ne' h1
  · exfalso
    have sh := omShape_mBar0 hOm hThree
    have h36 := sh.card_X
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card] at h36
    exact hn36 h36

end S152Y

end CFSG.Quasithin
