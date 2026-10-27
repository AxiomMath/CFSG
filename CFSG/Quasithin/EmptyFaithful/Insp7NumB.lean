module

public import CFSG.Timmesfeld.Orders.Classical
public import CFSG.Timmesfeld.Orders.Exceptional
public import CFSG.LieType.Ree.SuzukiOrder
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115List
public import CFSG.Quasithin.Background.F1Models

public section

namespace CFSG.Quasithin

open CFSG.Open (ordA ordTwistedA ordBC ordG2 ordTrialityD4 ordSuzuki)
open CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1 CFSG.Assembly.LowTwoRank CFSG.Blueprint

namespace Insp7

theorem dvd_mul_div_of_dvd' (a b g : ℕ) (h : g ∣ b) : a ∣ a * b / g := by
  rw [Nat.mul_div_assoc a h]
  exact Dvd.intro _ rfl

theorem sub_dvd_pow_two (q : ℕ) : q - 1 ∣ q ^ 2 - 1 := by
  simpa using Nat.sub_dvd_pow_sub_pow q 1 2

theorem two_pow_dvd_ordA_one {f : ℕ} : 2 ^ f ∣ ordA 1 (2 ^ f) := by
  unfold ordA
  have h2 : ∏ i ∈ Finset.Icc 2 (1 + 1), ((2 ^ f) ^ i - 1) = (2 ^ f) ^ 2 - 1 := by
    rw [show Finset.Icc 2 (1 + 1) = {2} by decide, Finset.prod_singleton]
  rw [show (1 : ℕ) * (1 + 1) / 2 = 1 by norm_num, h2, pow_one]
  have h3 : Nat.gcd (1 + 1) (2 ^ f - 1) ∣ (2 ^ f) ^ 2 - 1 :=
    (Nat.gcd_dvd_right _ _).trans (sub_dvd_pow_two _)
  exact dvd_mul_div_of_dvd' _ _ _ h3

theorem two_pow_dvd_ordA_two {f : ℕ} : 2 ^ (3 * f) ∣ ordA 2 (2 ^ f) := by
  unfold ordA
  have h1 : (2 : ℕ) * (2 + 1) / 2 = 3 := by norm_num
  have h2 : ∏ i ∈ Finset.Icc 2 (2 + 1), ((2 ^ f) ^ i - 1) =
      ((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 3 - 1) := by
    rw [show Finset.Icc 2 (2 + 1) = {2, 3} by decide, Finset.prod_pair (by norm_num)]
  rw [h1, h2]
  have h3 : Nat.gcd (2 + 1) (2 ^ f - 1) ∣ ((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 3 - 1) :=
    Dvd.dvd.mul_right ((Nat.gcd_dvd_right _ _).trans (sub_dvd_pow_two _)) _
  have hq : (2 : ℕ) ^ (3 * f) = (2 ^ f) ^ 3 := by rw [← pow_mul, mul_comm]
  rw [hq]
  exact dvd_mul_div_of_dvd' _ _ _ h3

theorem two_pow_dvd_ordA_four : 2 ^ 9 ∣ ordA 4 2 := by
  decide +kernel

theorem two_pow_dvd_ordTwistedA_two {f : ℕ} : 2 ^ (3 * f) ∣ ordTwistedA 2 (2 ^ f) := by
  unfold ordTwistedA
  have h1 : (2 : ℕ) * (2 + 1) / 2 = 3 := by norm_num
  rw [h1]
  have hq : (2 : ℕ) ^ (3 * f) = (2 ^ f) ^ 3 := by rw [← pow_mul, mul_comm]
  rw [hq]
  refine dvd_mul_div_of_dvd' _ _ _ ?_
  rw [show Finset.Icc 2 (2 + 1) = {2, 3} by decide, Finset.prod_pair (by norm_num)]
  refine Dvd.dvd.mul_left ?_ _
  have h3 : ((2 ^ f : ℕ) : ℤ) ^ 3 - (-1 : ℤ) ^ 3 = (((2 ^ f) ^ 3 + 1 : ℕ) : ℤ) := by
    push_cast; ring
  rw [h3, Int.toNat_natCast]
  refine (Nat.gcd_dvd_right _ _).trans ?_
  simpa using Odd.nat_add_dvd_pow_add_pow (2 ^ f) 1 (by decide : Odd 3)

theorem two_pow_dvd_ordBC_two {f : ℕ} : 2 ^ (4 * f) ∣ ordBC 2 (2 ^ f) := by
  unfold ordBC
  have hq : (2 : ℕ) ^ (4 * f) = (2 ^ f) ^ (2 * 2) := by rw [← pow_mul, mul_comm]
  rw [hq]
  refine dvd_mul_div_of_dvd' _ _ _ ?_
  rw [show Finset.Icc 1 2 = {1, 2} by decide, Finset.prod_pair (by norm_num)]
  refine Dvd.dvd.mul_right ?_ _
  refine (Nat.gcd_dvd_right _ _).trans ?_
  simpa using Nat.sub_dvd_pow_sub_pow (2 ^ f) 1 2

theorem two_pow_dvd_ordG2 {f : ℕ} : 2 ^ (6 * f) ∣ ordG2 (2 ^ f) := by
  unfold ordG2
  have hq : (2 : ℕ) ^ (6 * f) = (2 ^ f) ^ 6 := by rw [← pow_mul, mul_comm]
  rw [hq]
  exact Dvd.dvd.mul_right (dvd_mul_right _ _) _

theorem two_pow_dvd_ordTrialityD4 {f : ℕ} : 2 ^ (12 * f) ∣ ordTrialityD4 (2 ^ f) := by
  unfold ordTrialityD4
  have hq : (2 : ℕ) ^ (12 * f) = (2 ^ f) ^ 12 := by rw [← pow_mul, mul_comm]
  rw [hq]
  exact Dvd.dvd.mul_right (Dvd.dvd.mul_right (dvd_mul_right _ _) _) _

theorem two_pow_dvd_card_suzuki
    {L : Type} [Group L] {f : ℕ} (h : SuzukiModel L 2 f) :
    2 ^ (2 * f) ∣ Nat.card L := by
  obtain ⟨-, a, -, K, _, _, hf, hK, ⟨e⟩⟩ := h
  rw [Nat.card_congr e.toEquiv, CFSG.LieType.Ree.suzuki_order (hf ▸ hK), ← hf]
  have hq : (2 : ℕ) ^ (2 * f) = (2 ^ f) ^ 2 := by rw [← pow_mul, mul_comm]
  rw [hq]
  exact Dvd.dvd.mul_right (dvd_mul_right _ _) _

@[expose] def BigDvd (L : Type) [Group L] : Prop :=
  2 ^ 9 ∣ Nat.card (L ⧸ Subgroup.center L)

@[expose] def SmallLie (L : Type) [Group L] : Prop :=
  (∃ f : ℕ, 2 ≤ f ∧ f ≤ 8 ∧ StatedClassicalModel L .PSL 2 2 f) ∨
    StatedClassicalModel L .PSL 3 2 1 ∨ StatedClassicalModel L .PSL 3 2 2 ∨
    StatedClassicalModel L .PSU 3 2 2 ∨ StatedClassicalModel L .PSp 2 2 2 ∨
    StatedClassicalModel L .PSL 4 2 1 ∨ Nonempty (L ≃* alternatingGroup (Fin 6)) ∨
    StatedClassicalModel L .PSU 3 3 1 ∨ SuzukiModel L 2 3 ∨
    (Subgroup.center L ≠ ⊥ ∧ Subgroup.center L = CFSG.pCore 2 L ∧
      StatedClassicalModel (L ⧸ CFSG.pCore 2 L) .PSL 3 2 2)

@[expose] def LargeReeTits (L : Type) [Group L] : Prop :=
  (∃ f : ℕ, Odd f ∧ 3 ≤ f ∧ ReeTitsModel L .twistedF4 2 f) ∨ ReeTitsModel L .Tits 2 1

theorem bigDvd_of_simple {L : Type} [Group L] (hq : CFSG.IsQuasisimple L) (hs : IsSimpleGroup L)
    (h : 2 ^ 9 ∣ Nat.card L) : BigDvd L := by
  have hc : Subgroup.center L = ⊥ := by
    rcases (Subgroup.center L).normal_of_characteristic.eq_bot_or_eq_top with h0 | h0
    · exact h0
    · exfalso
      obtain ⟨a, b, hab⟩ := hq.2.2
      apply hab
      have : Subsingleton (L ⧸ Subgroup.center L) := by
        rw [h0]; exact QuotientGroup.subsingleton_quotient_top
      exact Subsingleton.elim _ _
  unfold BigDvd
  rw [hc, Nat.card_congr (QuotientGroup.quotientBot (G := L)).toEquiv]
  exact h

theorem lieCharTwo_cases
    {L : Type} [Group L] (hq : CFSG.IsQuasisimple L) (hs : IsSimpleGroup L)
    (h : Lemma115LieCharTwo L) : BigDvd L ∨ SmallLie L ∨ LargeReeTits L := by
  have big : ∀ k : ℕ, 9 ≤ k → 2 ^ k ∣ Nat.card L → BigDvd L := fun k hk hd =>
    bigDvd_of_simple hq hs ((pow_dvd_pow 2 hk).trans hd)
  rcases h with ((⟨f, hf⟩ | hT) | ⟨n, hn, hL⟩) | hA6 | hU33
  · rcases hf with ⟨h2, hm⟩ | ⟨h1, hm⟩ | ⟨h2, hm⟩ | ⟨h2, hm⟩ | ⟨h2, hm⟩ | ⟨h1, hm⟩ |
      ⟨hodd, h3, hm⟩ | ⟨hodd, h3, hm⟩
    ·
      by_cases h9 : 9 ≤ f
      · refine Or.inl (big f h9 ?_)
        rw [(CFSG.Timmesfeld.card_statedClassicalModel_two hm).1 rfl]
        exact two_pow_dvd_ordA_one
      · exact Or.inr (Or.inl (Or.inl ⟨f, h2, by omega, hm⟩))
    ·
      rcases (by omega : f = 1 ∨ f = 2 ∨ 3 ≤ f) with rfl | rfl | h3
      · exact Or.inr (Or.inl (by unfold SmallLie; tauto))
      · exact Or.inr (Or.inl (by unfold SmallLie; tauto))
      · refine Or.inl (big (3 * f) (by omega) ?_)
        rw [(CFSG.Timmesfeld.card_statedClassicalModel_two hm).1 rfl]
        exact two_pow_dvd_ordA_two
    ·
      rcases (by omega : f = 2 ∨ 3 ≤ f) with rfl | h3
      · exact Or.inr (Or.inl (by unfold SmallLie; tauto))
      · refine Or.inl (big (3 * f) (by omega) ?_)
        rw [(CFSG.Timmesfeld.card_statedClassicalModel_two hm).2.1 rfl]
        exact two_pow_dvd_ordTwistedA_two
    ·
      rcases (by omega : f = 2 ∨ 3 ≤ f) with rfl | h3
      · exact Or.inr (Or.inl (by unfold SmallLie; tauto))
      · refine Or.inl (big (4 * f) (by omega) ?_)
        rw [(CFSG.Timmesfeld.card_statedClassicalModel_two hm).2.2.1 rfl]
        exact two_pow_dvd_ordBC_two
    ·
      refine Or.inl (big (6 * f) (by omega) ?_)
      rw [CFSG.Timmesfeld.card_chevalleyExceptionalModel_two hm]
      exact two_pow_dvd_ordG2
    ·
      refine Or.inl (big (12 * f) (by omega) ?_)
      rw [CFSG.Timmesfeld.card_chevalleyExceptionalModel_two hm]
      exact two_pow_dvd_ordTrialityD4
    ·
      exact Or.inr (Or.inr (Or.inl ⟨f, hodd, h3, hm⟩))
    ·
      by_cases h5 : 5 ≤ f
      · refine Or.inl (big (2 * f) (by omega) ?_)
        exact two_pow_dvd_card_suzuki hm
      · have : f = 3 := by
          obtain ⟨k, hk⟩ := hodd
          omega
        subst this
        exact Or.inr (Or.inl (by unfold SmallLie; tauto))
  · exact Or.inr (Or.inr (Or.inr hT))
  · rcases hn with rfl | rfl
    · exact Or.inr (Or.inl (by unfold SmallLie; tauto))
    · refine Or.inl (big 9 le_rfl ?_)
      rw [(CFSG.Timmesfeld.card_statedClassicalModel_two hL).1 rfl]
      exact two_pow_dvd_ordA_four
  · exact Or.inr (Or.inl (by unfold SmallLie; tauto))
  · exact Or.inr (Or.inl (by unfold SmallLie; tauto))

end Insp7

end CFSG.Quasithin
