module

public import CFSG.Quasithin.Vol2.KGFactC31NoM22Exc
public import CFSG.Quasithin.Vol2.Ch10SecK2Tn
public import CFSG.Quasithin.Vol2.KGFactC31NoM22OrdNT

public section

namespace CFSG.Quasithin.KGC31

@[expose] def NoM22SectionLieExcRes : Prop :=
  ∀ (S : Type) [Group S] [Finite S],
    (∃ f : ℕ, (2 ≤ f ∧ 10 ∣ f ∧ IsG2 2 f S) ∨ (1 ≤ f ∧ 10 ∣ f ∧ Is3D4 2 f S) ∨
      (Odd f ∧ 3 ≤ f ∧ 15 ∣ f ∧ Is2F4 f S)) →
    ∀ (Y : Subgroup S) (φ : ↥Y →* CFSG.Blueprint.NativeSporadic.Carrier .M22),
      ¬ Function.Surjective φ

theorem noM22SectionLieExc_of_res
    (h : NoM22SectionLieExcRes) : NoM22SectionLieExc := by
  unfold NoM22SectionLieExc
  intro S _ _ hS Y φ hφ
  have hM : Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .M22) = 443520 :=
    CFSG.Sporadic.Schreier.m22_card
  have hdvd : Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .M22) ∣ Nat.card S :=
    (Subgroup.card_dvd_of_surjective hφ).trans (Subgroup.card_subgroup_dvd_card Y)
  rw [hM] at hdvd
  obtain ⟨f, hf⟩ := hS
  rcases hf with ⟨hf2, hG⟩ | ⟨hf1, hD⟩ | ⟨hodd, hf3, hF⟩
  · have hord : Nat.card S = 2 ^ (6 * f) * (((2 ^ f) ^ 6 - 1) * ((2 ^ f) ^ 2 - 1)) :=
      CFSG.Quasithin.Vol2.Ch10.SecC.C10KH.card_of_isG2 hG
    rw [hord] at hdvd
    exact h S ⟨f, Or.inl ⟨hf2, kgC31Ord_ten_dvd_of_G2_order f hdvd, hG⟩⟩ Y φ hφ
  · have hord : Nat.card S = CFSG.Open.ordTrialityD4 (2 ^ f) :=
      CFSG.Timmesfeld.card_chevalleyExceptionalModel_two
        (t := CFSG.Assembly.LowTwoRank.StatedLieTag.trialityD4) hD
    unfold CFSG.Open.ordTrialityD4 at hord
    rw [hord] at hdvd
    exact h S ⟨f, Or.inr (Or.inl ⟨hf1, kgC31Ord_ten_dvd_of_D4_order f hdvd, hD⟩)⟩ Y φ hφ
  · have hord : Nat.card S = CFSG.Open.ordTwistedF4 (2 ^ f) :=
      CFSG.RankThree.PartOne.S12K.card_of_reeTitsModel_twistedF4 hF
    unfold CFSG.Open.ordTwistedF4 at hord
    rw [hord] at hdvd
    exact h S ⟨f, Or.inr (Or.inr ⟨hodd, hf3, kgC31Ord_fifteen_dvd_of_F4_order f hdvd, hF⟩)⟩
      Y φ hφ

end CFSG.Quasithin.KGC31

end
