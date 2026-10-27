module

public import CFSG.RankThree.PartTwo.Sec6.Item641
import CFSG.RankThree.GF2n.QTwo
import CFSG.RankThree.GF2n.Assembly
import CFSG.RankThree.PartTwo.Sec5.Tools
import CFSG.GH74.EvenRank
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Open.GLADefs
public import CFSG.RankThree.PartTwo.Sec6.Statements

public section

namespace CFSG.RankThree.PartTwo.Sec6

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

@[expose] def GF2TypeE27 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], PartTwoStanding G → ∀ t : G, orderOf t = 2 →
    ∀ E : Subgroup G, CFSG.Assembly.IsElemAbelian 3 E → Nat.card E = 27 →
      E ≤ Subgroup.centralizer ({t} : Set G) →
      ¬ CFSG.Open.GLASymplecticType
        (inSubgroup generalizedFitting (Subgroup.centralizer ({t} : Set G)))

@[expose] def Item3_10_smallE27 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], PartTwoStanding G →
    ∀ M : Subgroup G, CFSG.IsMaximalTwoLocal M → ∀ V : Subgroup G,
      Maximal (fun W : Subgroup G => W ≤ M ∧ M ≤ Subgroup.normalizer (W : Set G) ∧
        CFSG.Assembly.IsElemAbelian 2 W) V →
      Nat.card V ≤ 2 →
      ∀ A : Subgroup G, CFSG.Assembly.IsElemAbelian 3 A → Nat.card A = 27 → A ≤ M → False

namespace LitScope

variable {G : Type} [Group G] [Finite G]

theorem exists_symplectic_of_card_le_two (hchar : CFSG.Assembly.IsCharTwoType G)
    {M V : Subgroup G} (hM : CFSG.IsMaximalTwoLocal M)
    (hV : Maximal (fun W : Subgroup G => W ≤ M ∧ M ≤ Subgroup.normalizer (W : Set G) ∧
      CFSG.Assembly.IsElemAbelian 2 W) V) (hV2 : Nat.card V ≤ 2) :
    ∃ z : G, orderOf z = 2 ∧ M = Subgroup.centralizer ({z} : Set G) ∧
      CFSG.Open.GLASymplecticType
        (inSubgroup generalizedFitting (Subgroup.centralizer ({z} : Set G))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hchar' : IsCharacteristicPType G 2 := (GH74.isCharTwoType_iff).mp hchar
  have hV2' : Nat.card V = 2 := by
    rcases GF2n.card_eq_two_or_four_le hM.1 hV with h | h
    · exact h
    · omega
  obtain ⟨z, hzo, hVz, hMz⟩ := GF2n.exists_eq_centralizer_of_card_eq_two hM hV hV2'
  have hsymp := GF2n.glaSymplecticType_of_card_eq_two hV hV2' hVz hMz.le
  refine ⟨z, hzo, hMz, ?_⟩
  have hF : generalizedFitting M = pCore 2 M := GF2n.generalizedFitting_eq_pCore hchar' hM.1
  have hFG : inSubgroup generalizedFitting M = inSubgroup (pCore 2) M := by
    unfold inSubgroup
    rw [hF]
  rw [← hMz, hFG]
  exact hsymp

end LitScope

theorem item3_10_smallE27_of (h : GF2TypeE27) : Item3_10_smallE27 := by
  intro G _ _ hG M hM V hV hV2 A hAe hA27 hAM
  obtain ⟨z, hzo, hMz, hsymp⟩ :=
    LitScope.exists_symplectic_of_card_le_two hG.charTwoType hM hV hV2
  exact h G hG z hzo A hAe hA27 (hMz ▸ hAM) hsymp

theorem rank3II_6_4_1_of_smallE27 (h310 : Item3_10_smallE27) : Item6_4_1 := by
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
  exact h310 G hG M hM.1 V hVmax hV2 A hAab hA27 hAM

theorem rank3II_6_4_1_of_e27 (h : GF2TypeE27) : Item6_4_1 :=
  rank3II_6_4_1_of_smallE27 (item3_10_smallE27_of h)

end CFSG.RankThree.PartTwo.Sec6
