module

public import CFSG.Quasithin.EmptyFaithful.S152Y22
public import CFSG.Quasithin.EmptyFaithful.S152Y23
public import CFSG.Quasithin.EmptyFaithful.S152NAbs
public import CFSG.Quasithin.EmptyFaithful.S152Y14

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

namespace S152Y

variable {G : Type} [Group G] [Finite G] {T Mc M : Subgroup G}

theorem autOn_yOf_eq_commutator (h : Data T Mc M)
    (hEodd : Odd (Nat.card (oTwoUpper (mBar0 T Mc M)))) :
    autOn (yOf152 T Mc M) (V154 T Mc M) =
      ⁅oTwoUpper (mBar0 T Mc M), autOn (rcOf Mc M) (V154 T Mc M)⁆ := by
  have hodd0 : Odd (Nat.card (autOn (y0Of T Mc M) (V154 T Mc M))) := by
    rw [h.autOn_y0Of]; exact hEodd
  have := lemma_14_1_17_two h.qtfe h.hyp (y0Of_le T Mc M) h.T_le_normalizer_y0Of hodd0
  rw [h.autOn_y0Of] at this
  exact this

theorem omShape_mBar0 (hOm : Om4IsoStatement)
    (hThree : Case1517Three M (V154 T Mc M) (mBar0 T Mc M)) : OmShape (mBar0 T Mc M) := by
  obtain ⟨-, hA, hV, hX⟩ := hThree
  have := omShape_of_isOmegaFourPlus hOm (V := IntMod (V154 T Mc M) hV) (X := autOn M (V154 T Mc M)) hX
  rw [← hA]
  exact this

theorem three_main (h : Data T Mc M) (h113 : StageLemma14113) (hOm : Om4IsoStatement)
    (hThree : Case1517Three M (V154 T Mc M) (mBar0 T Mc M))
    (hYnorm : M ≤ Subgroup.normalizer (yOf152 T Mc M : Set G)) :
    autOn (yOf152 T Mc M) (V154 T Mc M) ≠ ⊥ ∧
      autOn (yOf152 T Mc M) (V154 T Mc M) =
        ⁅autOn (yOf152 T Mc M) (V154 T Mc M), autOn (rcOf Mc M) (V154 T Mc M)⁆ ∧
      (Case15203i T Mc M ∨ Case15203ii T Mc M ∨ Case15203iii T Mc M) := by
  have sh := omShape_mBar0 hOm hThree
  set Eb : Subgroup (MulAut (V154 T Mc M)) := oTwoUpper (mBar0 T Mc M) with hEb
  set Rb : Subgroup (MulAut (V154 T Mc M)) := autOn (rcOf Mc M) (V154 T Mc M) with hRb
  have hA : autOn M (V154 T Mc M) = mBar0 T Mc M := hThree.2.1
  have hE9 : Nat.card Eb = 9 := sh.card_O
  have hEodd : Odd (Nat.card Eb) := by rw [hE9]; decide
  have hEab := sh.comm_O
  have hEexp := sh.exp_O
  have hRV : rcOf Mc M ≤ Subgroup.normalizer (V154 T Mc M : Set G) := h.rc_le_M.trans h.hMV
  have hR2 : IsPGroup 2 Rb := isPGroup_autOn (rc_isPGroup Mc M) hRV
  have hRne : Rb ≠ ⊥ := lemma_14_1_17_one h113 h.qtfe h.hyp
  have hRM : Rb ≤ autOn M (V154 T Mc M) := A4.autOn_mono h.rc_le_M
  have hRX : Rb ≤ mBar0 T Mc M := hA ▸ hRM
  have hRcomm : ∀ a ∈ Rb, ∀ b ∈ Rb, a * b = b * a := by
    obtain ⟨-, -, hV, hX⟩ := hThree
    have hW2 : ∀ w : IntMod (V154 T Mc M) hV, w * w = 1 := fun w => by
      rw [← pow_two]; exact IntMod.sq_eq_one w
    exact S152N.comm_of_isOmegaFourPlus (W := IntMod (V154 T Mc M) hV) hW2 hX hRM hR2
  have hY : autOn (yOf152 T Mc M) (V154 T Mc M) = ⁅Eb, Rb⁆ := autOn_yOf_eq_commutator h hEodd
  have hRbE : Rb ≤ Subgroup.normalizer (Eb : Set (MulAut (V154 T Mc M))) :=
    (hRM.trans (mBar0_normalizer T Mc M)).trans (normalizer_le_normalizer_oTwoUpper _)
  have hYle : ⁅Eb, Rb⁆ ≤ Eb := Subgroup.le_normalizer_iff_commutator_le_left.mp hRbE
  have conclude_i : autOn (yOf152 T Mc M) (V154 T Mc M) = Eb →
      Ys T Mc M ⊓ (piStar h).ker = ⊥ →
      Case15203i T Mc M := by
    intro hYb hK
    exact ⟨hYb, yOf_inf_centralizer_le h hK, fun _ =>
      threePrime_of_K_bot h hE9 hEexp hEab hYb hK⟩
  have hsq : ∀ ρ ∈ Rb, ρ * ρ = 1 := fun ρ hρ => by
    obtain ⟨k, hk⟩ := hR2 ⟨ρ, hρ⟩
    exact sh.two_elements ρ (hRX hρ) ⟨k, by simpa using congrArg Subtype.val hk⟩
  rcases rCase_of_omShape sh hRX hR2 hRne hRcomm with ⟨hYE, hρ⟩ | ⟨hYE, hRcard, hρ⟩ | ⟨hY3, hRcard, hρ⟩
  ·
    have hYb : autOn (yOf152 T Mc M) (V154 T Mc M) = Eb := hY.trans hYE
    obtain ⟨ρ, hρR, hρ1, hρni⟩ := hρ
    obtain ⟨e₁, he₁, e₂, he₂, -, -, h₁, h₂, hgen⟩ :=
      (sh.inv_or_eigen ρ (hRX hρR) (hsq ρ hρR) hρ1).resolve_left hρni
    have hab := Ys_abelian_of_eigen h hYb hEab hρR he₁ he₂ hgen h₁ h₂
    have hK := Data.K_eq_bot_of_abelian h hEodd hab
    refine ⟨?_, ?_, Or.inl (conclude_i hYb hK)⟩
    · rw [hYb]; intro hbot
      have : Nat.card Eb = 1 := by rw [hbot]; exact Subgroup.card_bot
      omega
    · rw [hYb]; exact hYE.symm
  ·
    have hYb : autOn (yOf152 T Mc M) (V154 T Mc M) = Eb := hY.trans hYE
    have hne : autOn (yOf152 T Mc M) (V154 T Mc M) ≠ ⊥ := by
      rw [hYb]; intro hbot
      have : Nat.card Eb = 1 := by rw [hbot]; exact Subgroup.card_bot
      omega
    have hce : autOn (yOf152 T Mc M) (V154 T Mc M) =
        ⁅autOn (yOf152 T Mc M) (V154 T Mc M), autOn (rcOf Mc M) (V154 T Mc M)⁆ := by
      rw [hYb]; exact hYE.symm
    refine ⟨hne, hce, ?_⟩
    by_cases hab : ∀ a ∈ Ys T Mc M, ∀ c ∈ Ys T Mc M, a * c = c * a
    · exact Or.inl (conclude_i hYb (Data.K_eq_bot_of_abelian h hEodd hab))
    · refine Or.inr (Or.inl ⟨hThree, hRcard, hρ, ?_, ?_, ?_, ?_⟩)
      · rw [hA]
      · rw [hA, hYb]
      · obtain ⟨b, hbR, hb1⟩ : ∃ b ∈ Rb, b ≠ 1 := by
          obtain ⟨⟨b, hb⟩, hb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hRne
          exact ⟨b, hb, fun h' => hb1 (Subtype.ext h')⟩
        exact Ys_isPOnePlusTwo h hE9 hEexp hEab hbR (hρ b hbR hb1) hab
      · have hP : IsPOnePlusTwo 3 ↥(Ys T Mc M) := by
          obtain ⟨b, hbR, hb1⟩ : ∃ b ∈ Rb, b ≠ 1 := by
            obtain ⟨⟨b, hb⟩, hb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hRne
            exact ⟨b, hb, fun h' => hb1 (Subtype.ext h')⟩
          exact Ys_isPOnePlusTwo h hE9 hEexp hEab hbR (hρ b hbR hb1) hab
        exact oTwoUpper_oTwoZIn_eq_theta h hEab hYnorm hab hP
  ·
    have hYcard : Nat.card (autOn (yOf152 T Mc M) (V154 T Mc M)) = 3 := by rw [hY]; exact hY3
    have hcyc : IsCyclic ↥(autOn (yOf152 T Mc M) (V154 T Mc M)) := isCyclic_of_prime_card hYcard
    have hab := Ys_abelian_of_cyclic h hcyc
    have hK := Data.K_eq_bot_of_abelian h hEodd hab
    have hne : autOn (yOf152 T Mc M) (V154 T Mc M) ≠ ⊥ := by
      intro hbot
      have : Nat.card (autOn (yOf152 T Mc M) (V154 T Mc M)) = 1 := by
        rw [hbot]; exact Subgroup.card_bot
      omega
    have hce : autOn (yOf152 T Mc M) (V154 T Mc M) =
        ⁅autOn (yOf152 T Mc M) (V154 T Mc M), autOn (rcOf Mc M) (V154 T Mc M)⁆ := by
      apply le_antisymm
      · obtain ⟨ρ, hρR, hρ1⟩ : ∃ ρ ∈ Rb, ρ ≠ 1 := by
          obtain ⟨⟨b, hb⟩, hb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hRne
          exact ⟨b, hb, fun h' => hb1 (Subtype.ext h')⟩
        intro a ha
        have haE : a ∈ Eb := hYle (hY ▸ ha)
        exact mem_commutator_of_inverted hρR ha (m := 3) (by decide) (hEexp a haE)
          (hρ ρ hρR hρ1 a (hY ▸ ha))
      · have hRbY : Rb ≤ Subgroup.normalizer
            ((autOn (yOf152 T Mc M) (V154 T Mc M) : Subgroup _) : Set (MulAut (V154 T Mc M))) := by
          rw [hY]
          exact le_normalizer_commutator_of_le hRbE Subgroup.le_normalizer
        exact Subgroup.le_normalizer_iff_commutator_le_left.mp hRbY
    refine ⟨hne, hce, Or.inr (Or.inr ⟨hThree, hRcard, ?_, hYcard, yOf_inf_centralizer_le h hK, ?_⟩)⟩
    · intro b hb hb1 a ha
      exact hρ b hb hb1 a (hY ▸ ha)
    · exact exists_sylow_three h hA sh.card_X hE9 hEexp hEab hYcard hK hYnorm

end S152Y

end CFSG.Quasithin
