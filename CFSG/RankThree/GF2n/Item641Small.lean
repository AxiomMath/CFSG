module

public import CFSG.RankThree.GF2n.Item310
import CFSG.RankThree.PartTwo.Sec5.Tools
public import CFSG.RankThree.PartTwo.Sec6.Statements

public section

namespace CFSG.RankThree.GF2n

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
  CFSG.RankThree.PartTwo.Sec6

theorem rank3II_6_4_1_of_item3_10_small (h310 : Item3_10_small) : Item6_4_1 := by
  intro G _ _ hG A hA
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hne
  obtain ⟨hAab, hA27, U0, hU01, hU02, hAU0⟩ := hA
  obtain ⟨M, hM, -⟩ := exists_mem_scriptM_of_isTwoLocal (X := (A : Set G))
    (H := Subgroup.normalizer (U0 : Set G)) ⟨U0, hU01, hU02, rfl⟩ fun x hx => hAU0 hx
  have hAM : A ≤ M := fun x hx => hM.2 hx
  obtain ⟨V, -, hVmax⟩ := Finite.exists_le_maximal (p := fun W : Subgroup G => W ≤ M ∧
      M ≤ Subgroup.normalizer (W : Set G) ∧ CFSG.Assembly.IsElemAbelian 2 W) (a := ⊥)
    ⟨bot_le, fun m _ => Subgroup.mem_normalizer_iff.mpr fun x => by simp,
      ⟨⟨fun a b => Subsingleton.elim _ _⟩⟩, fun x hx => by rw [Subgroup.mem_bot.mp hx, one_pow]⟩
  obtain ⟨-, hMV, hVab⟩ := hVmax.prop
  have hV2 : Nat.card V ≤ 2 := by
    obtain ⟨k, hk⟩ := (Sec5.isPGroup_of_isElemAbelian hVab).exists_card_eq
    have hk1 : k ≤ 1 := by
      by_contra h
      push Not at h
      obtain ⟨U, hUA, -⟩ := exists_mem_fourGroups_le hAab hA27 hVab
        (by
          rw [hk]
          calc 4 = 2 ^ 2 := by norm_num
            _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) h) (hAM.trans hMV)
      exact hne ⟨U, hUA⟩
    rw [hk]
    calc 2 ^ k ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hk1
      _ = 2 := by norm_num
  have hTI : ∀ g : G, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V ⊓ V.map (MulAut.conj g).toMonoidHom = V := by
    intro g
    by_cases h : V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥
    · exact Or.inl h
    · refine Or.inr (Subgroup.eq_of_le_of_card_ge inf_le_left ?_)
      have := (Subgroup.one_lt_card_iff_ne_bot _).mpr h
      omega
  exact hG.not_inCatalog (h310 G hG.isSimpleGroup hG.nonabelian hG.kProper hG.charTwoType M hM.1
    V hVmax hTI hV2)

end CFSG.RankThree.GF2n
