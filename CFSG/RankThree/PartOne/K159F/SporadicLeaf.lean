module

public import CFSG.RankThree.PartOne.CTP.StrongPSporadic

public section

namespace CFSG.RankThree.PartOne.K159F

open CFSG.Blueprint TauCeti CFSG.RankThree.PartOne CFSG.RankThree.PartOne.CTP
  CFSG.RankThree.PartOne.StrongP
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

@[expose] def SporadicFiveInput : Prop :=
  ∀ p : ℕ, p.Prime → 5 ≤ p →
    ∀ (H : Type) [Group H] [Finite H] (S : Subgroup H), S.Normal → IsSimpleGroup ↥S →
      (∃ a b : ↥S, a * b ≠ b * a) →
      (∃ s ∈ Census3.sporadicsThm3, Nonempty (↥S ≃* (TauCeti.CFSGIndex.sporadic s).Group)) →
      Subgroup.centralizer (S : Set H) = ⊥ →
      ∀ P : Subgroup H, IsSylowOf p P ⊤ → IsElementaryAbelian p (omegaOne p P) →
        Nat.card (omegaOne p P) = p ^ 3 → False

theorem sporadicFiveInput_of_leTwo (hLeTwo : SporadicOuterOrderLeTwoSimple) :
    SporadicFiveInput := by
  have hOut := sporadicOuterNoLargePrime_of_leTwo hLeTwo
  intro p hp hp5 H _ _ S hSn hSs hnonab ⟨s, hs, ⟨e⟩⟩ hSc P hP hab hΩ
  have : Fact p.Prime := ⟨hp⟩
  have : IsSimpleGroup s.Group := MulEquiv.isSimpleGroup e.symm
  obtain ⟨φ⟩ := Census3.nonempty_carrier_mulEquiv_of_mem hs
  let e' : ↥S ≃* NativeSporadic.Carrier s := e.trans φ.symm
  by_cases hnc : SporadicPairNC s p
  · have hpair' : HasNoncommPair p (NativeSporadic.Carrier s) := hasNoncommPair_carrier hnc
    exact false_of_hasNoncommPair S hP hab (hpair'.map e'.symm.toMonoidHom e'.symm.injective)
  · have hcube : ¬ p ^ 3 ∣ Nat.card ↥S := by
      intro h3
      have h2 : p ^ 2 ∣ Nat.card (NativeSporadic.Carrier s) := by
        rw [← Nat.card_congr e'.toEquiv]
        exact (pow_dvd_pow p (by norm_num)).trans h3
      have h3' : p ^ 3 ∣ Nat.card (NativeSporadic.Carrier s) := by
        rwa [← Nat.card_congr e'.toEquiv]
      rcases sporadicPair_of_sq_dvd hs hp hp5 h2 with hnc' | hab'
      · exact hnc hnc'
      · rcases hab' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · rw [show Nat.card (NativeSporadic.Carrier .J2) = _ from CFSG.Sporadic.J2.card_J2] at h3'
          norm_num at h3'
        · rw [show Nat.card (NativeSporadic.Carrier .He) = _ from CFSG.Sporadic.He.card_He] at h3'
          norm_num at h3'
        · rw [show Nat.card (NativeSporadic.Carrier .Suz) = _ from CFSG.Sporadic.Suz.card_Suz] at h3'
          norm_num at h3'
        · rw [show Nat.card (NativeSporadic.Carrier .Th) = _ from card_Th] at h3'
          norm_num at h3'
    have hOut' := hOut s hs ↥S hnonab ⟨e'⟩ p hp hp5
    have hnd : ¬ p ∣ Nat.card (H ⧸ S) := fun h => hOut' (h.trans (card_quotient_dvd_outer S hSc))
    have hPS : P ≤ S := le_of_isPGroup_of_not_dvd_card_quotient hP.2.1 hnd
    have hPdvd : Nat.card P ∣ Nat.card S := Subgroup.card_dvd_of_le hPS
    have hPcard : p ^ 3 ∣ Nat.card P := by
      obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hP.2.1
      have h1 : p ^ 3 ≤ Nat.card P := by
        rw [← hΩ]
        exact Subgroup.card_le_of_le (omegaOne_le P)
      rw [hk] at h1 ⊢
      exact pow_dvd_pow p ((Nat.pow_le_pow_iff_right hp.one_lt).mp h1)
    exact hcube (hPcard.trans hPdvd)

end CFSG.RankThree.PartOne.K159F
