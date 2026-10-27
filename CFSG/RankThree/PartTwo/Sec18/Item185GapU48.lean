module

public import CFSG.RankThree.PartTwo.Sec18.Item185OuterSpU4
public import CFSG.RankThree.PartTwo.Sec18.Item185FixedFacts
import CFSG.RankThree.PartTwo.Sec4.RonanK429RowLieU4

public section

namespace CFSG.RankThree.PartTwo.Sec18.Item185Proof

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo

theorem gapU48_holds :
    GapU48 := by
  intro σ hout h3
  obtain ⟨k, hk3, hk1, F, hF, h₀, ⟨e⟩⟩ :=
    CFSG.RankThree.PartTwo.Sec4.RonanK429Lie.exists_autFix_mulEquiv_unitarySU_four
      (n := 3) (by norm_num) h3 hout
  have hk : k = 1 := by omega
  subst hk
  haveI := CFSG.RankThree.PartTwo.Sec4.RonanK429Lie.isSimpleGroup_unitarySU_four h₀
  have hfix : fixedSubgroup σ = Sec4.autFix σ := Subgroup.ext fun _ => Iff.rfl
  have eF := (MulEquiv.subgroupCongr hfix).trans e
  haveI hsimple : IsSimpleGroup (fixedSubgroup σ) := eF.isSimpleGroup
  have hna : ¬ ∀ x y : fixedSubgroup σ, x * y = y * x := by
    intro hc
    haveI : IsMulCommutative (fixedSubgroup σ) := ⟨⟨fun a b => hc a b⟩⟩
    have hprime : (Nat.card (fixedSubgroup σ)).Prime :=
      Group.is_simple_iff_prime_card.mp inferInstance
    rw [Nat.card_congr eF.toEquiv,
      CFSG.RankThree.PartTwo.Sec4.Item419Res3.card_unitarySU_four h₀] at hprime
    norm_num at hprime
  exact fixedFactsAt_of_simple hsimple hna

end CFSG.RankThree.PartTwo.Sec18.Item185Proof
