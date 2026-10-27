module

public import CFSG.Quasithin.Vol2.Ch5Sec2LocalLem522BotCanon
public import CFSG.Quasithin.Vol2.Ch5Sec2LocalLem522BotD4
public import CFSG.Quasithin.Vol2.Ch5Sec2LocalLem522BotU4
public import CFSG.Quasithin.Vol2.Ch5Sec2LocalCanon2Common
public import CFSG.Quasithin.Recognition.AS14216QO2D4
public import CFSG.Quasithin.Recognition.AS14216QO2J2

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin

section General

variable {G : Type} [Group G] [Finite G]

theorem borelOf_eq_of_perm_three {Y S : Subgroup G} (hS : IsSylowTwoOf S Y)
    (hY : Nonempty (oTwoQuot ↥Y ≃* Equiv.Perm (Fin 3))) : borelOf Y S = S := by
  obtain ⟨e⟩ := hY
  have hcard : Nat.card (OTwoQuot Y) = 2 ^ 1 * 3 := by
    rw [Nat.card_congr e.toEquiv, card_perm_fin_three]
    norm_num
  have h := inf_normalizer_eq_of_card_quot hS le_rfl (by norm_num) (by decide) hcard
  unfold borelOf
  rw [inf_eq_left.mpr hS.1]
  exact h

theorem sup_bigB_eq_of_borelOf_eq {L1 L2 S : Subgroup G} (h : borelOf L2 S = S) :
    L1 ⊔ bigB L1 L2 S = L1 ⊔ S := by
  unfold bigB
  rw [h]
  apply le_antisymm
  · exact sup_le le_sup_left (sup_le (sup_le ((F1.borelOf_le L1 S).trans le_sup_left) le_sup_right)
      le_sup_right)
  · exact sup_le le_sup_left (le_sup_right.trans le_sup_right)

theorem false_of_autJ2_entryC {L₂ Y S : Subgroup G} (hSY : IsSylowTwoOf S Y)
    (hY : Nonempty (oTwoQuot ↥Y ≃* Equiv.Perm (Fin 3))) (hY6 : Nat.card ↥(pCoreOf 2 Y) = 2 ^ 6)
    (hSL : S ≤ Subgroup.normalizer (L₂ : Set G)) (hSyl : IsSylowTwoOf (S ⊓ L₂) L₂)
    (h5 : Nonempty (oTwoQuot ↥(L₂ ⊔ S) ≃* Equiv.Perm (Fin 5)))
    (hQ : Nat.card ↥(pCoreOf 2 (L₂ ⊔ S)) = 32) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS : Nat.card ↥S = 2 ^ 7 := by
    rw [card_eq_two_mul_of_perm_three hSY hY, hY6]
    norm_num
  have hS2 : IsPGroup 2 ↥S := hSY.2.1
  have hSyl' : IsSylowTwoOf S (L₂ ⊔ S) :=
    C124.L2.isSylowTwoOf_sup_of_normalizing hSL hS2 hSyl
  obtain ⟨e⟩ := h5
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp (pCoreOf_isPGroup 2 (L₂ ⊔ S))
  have hX : Nat.card ↥(L₂ ⊔ S) = 2 ^ (3 + a) * 15 := by
    rw [card_eq_card_oTwoQuot_mul_card_pCoreOf, Nat.card_congr e.toEquiv, card_perm_fin_five, ha,
      pow_add]
    ring
  have h1 := card_sylow_eq_pow hSyl'.1 hSyl' (by decide) hX
  rw [hS] at h1
  have ha4 : a = 4 := by
    have := Nat.pow_right_injective (le_refl 2) h1
    omega
  rw [ha, ha4] at hQ
  norm_num at hQ

end General

theorem stmt5_2_2_bot_listC_of
    (hRL : RankOneListedFacts.{0}) (hD4 : Stmt5_2_2_bot_D4)
    (hJ2 : Stmt5_2_2_bot_J2) (hU4 : Stmt5_2_2_bot_U4) : Stmt5_2_2_bot_listC := by
  intro G _ _ T M L V H B D L₂ Dp n hyp hO hS3 L1' L2' hor h111 hcen hlist _
  have hR : Hyp111R L1' L2' (sec52S M H) := Hyp111R.of_hyp111 hRL h111
  have hSDp : sec52S M H ≤ Dp ⊔ sec52S M H := le_sup_right
  have hY : ∀ {X : Subgroup G}, X = Dp ⊔ sec52S M H →
      IsSylowTwoOf (sec52S M H ⊓ X) X → IsSylowTwoOf (sec52S M H) (Dp ⊔ sec52S M H) := by
    rintro X rfl h
    rwa [inf_eq_left.mpr le_sup_right] at h
  simp only [F112ListB] at hlist
  rcases hlist with h4 | h6 | h10 | h11
  ·
    obtain ⟨hA, hq1, hsp, hq2, hcard⟩ := h4
    obtain ⟨rfl, rfl⟩ := orient_of_isL2Quot_left (f := 3) (by norm_num) hS3 hor hq1
    have hc1 : pCoreOf 2 (L1' ⊔ bigB L1' (Dp ⊔ sec52S M H) (sec52S M H)) = pCoreOf 2 L1' := by
      refine le_antisymm ?_ (F1.pCoreOf_le_pCoreOf_parabolic hR)
      obtain ⟨Y, _, hY3, T', M₁, M₂, hpair, ⟨Φ⟩⟩ := hA
      have h504 : Nat.card (OTwoQuot L1') = 504 :=
        (IsL2Quot.card (by norm_num) hq1).trans (by norm_num)
      exact AS14216.pCoreOf_le_pCoreOf_of_d4 le_sup_left (F1.parabolic_le_normalizer hR)
        (F1.parabolic_charTwo hR) hsp h504 hY3 (M₁.subtype.comp Φ.φ1.toMonoidHom)
        (M₁.subtype_injective.comp Φ.φ1.injective)
    have hc2 := pCoreOf_parabolic'_eq_of_le hR hSDp
    exact hD4 G T M L V H B D L1' Dp n hyp hO hS3 h111 hcen hA hq1 (by rw [← hc1]; exact hsp)
      (by rw [← hc2]; exact hcard)
  ·
    obtain ⟨hA, hq1, hsp, hb2, hq2, hO6, hAlt⟩ := h6
    obtain ⟨rfl, rfl⟩ := orient_of_isL2Quot_right (f := 2) (by norm_num) hS3 hor hq2
    have hc1 := pCoreOf_parabolic_eq_of_le hR hSDp
    exact hU4 G T M L V H B D L2' Dp n hyp hO hS3 h111 hcen hA (by rw [← hc1]; exact hsp) hb2 hq2
      hO6 hAlt
  ·
    obtain ⟨hA, hq1, hQ8, hq2, hcard⟩ := h10
    obtain ⟨rfl, rfl⟩ := orient_of_isL2Quot_left (f := 2) (by norm_num) hS3 hor hq1
    have hc1 : pCoreOf 2 (L1' ⊔ bigB L1' (Dp ⊔ sec52S M H) (sec52S M H)) = pCoreOf 2 L1' := by
      refine le_antisymm ?_ (F1.pCoreOf_le_pCoreOf_parabolic hR)
      have h60 : Nat.card (OTwoQuot L1') = 60 :=
        (IsL2Quot.card (by norm_num) hq1).trans (by norm_num)
      have h5 : 5 ∣ Nat.card L1' := by
        rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.Open.pCore 2 ↥L1')]
        exact Dvd.dvd.mul_right (h60 ▸ (by norm_num : 5 ∣ 60)) _
      exact AS14216.pCoreOf_le_pCoreOf_of_isQ8D8 le_sup_left (F1.parabolic_le_normalizer hR)
        (F1.parabolic_charTwo hR) hQ8 h5
    have hc2 := pCoreOf_parabolic'_eq_of_le hR hSDp
    exact hJ2 G T M L V H B D L1' Dp n hyp hO hS3 h111 hcen hA hq1 (by rw [← hc1]; exact hQ8)
      (by rw [← hc2]; exact hcard)
  ·
    obtain ⟨hA, h5, hQ8, hq2, hcard⟩ := h11
    obtain ⟨rfl, rfl⟩ := orient_of_perm_five le_sup_right hS3 hor h5
    have hSY := hY rfl h111.h2.sylow
    have hB2 : borelOf (Dp ⊔ sec52S M H) (sec52S M H) = sec52S M H :=
      borelOf_eq_of_perm_three hSY hS3
    have hv := sup_bigB_eq_of_borelOf_eq (L1 := L1') hB2
    have hc2 := pCoreOf_parabolic'_eq_of_le hR hSDp
    refine false_of_autJ2_entryC hSY hS3 (by rw [← hc2]; exact hcard) h111.h1.normalizes
      h111.h1.sylow h5 ?_
    have hQ := hQ8.1
    rwa [hv] at hQ

theorem stmt5_2_2_bot_listC_holds
    (hRL : RankOneListedFacts.{0}) (h510 : Stmt5_1_10) (h331 : Stmt3_3_1)
    (hR : L2RankOneSylowFact) (hLie : Stmt5_2_L2Lie) : Stmt5_2_2_bot_listC :=
  stmt5_2_2_bot_listC_of hRL (stmt5_2_2_bot_D4_of h510 h331 hR hLie)
    (stmt5_2_2_bot_J2_of h510 h331 hR) (stmt5_2_2_bot_U4_of h510 h331 hR)

end CFSG.Quasithin.H13
