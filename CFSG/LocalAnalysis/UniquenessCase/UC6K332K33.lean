module

public import CFSG.LocalAnalysis.UniquenessCase.UC6K332K33NonLie
public import CFSG.LocalAnalysis.UniquenessCase.UC6K332K33Cover
public import CFSG.LocalAnalysis.UniquenessCase.UC6K332K33Cls
public import CFSG.LocalAnalysis.UniquenessCase.UC6K332K33Exc

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK.K332Route

open CFSG.Open (IsElemAbelian)
open CFSG.Blueprint.NativeSporadic (Carrier)

theorem k33Models_of_lie
    (d : TauCeti.ValidLieTypeIndex) {L : Type} [Group L] [Finite L]
    (hs : IsSimpleGroup L) (hna : ∃ a b : L, a * b ≠ b * a)
    (e : L ≃* (TauCeti.CFSGIndex.lie d).Group)
    (h2 : CFSG.Open.pRank 3 (⊤ : Subgroup L) = 2) : K33Models L := by
  obtain ⟨i, hv⟩ := d
  have e' : L ≃* TauCeti.ValidLieTypeIndex.Group ⟨i, hv⟩ := e
  cases i with
  | A r q => exact k33Models_A hv e' h2
  | twistedA r q => exact k33Models_twistedA hv e' h2
  | B r q => exact k33Models_B hv e' h2
  | C r q => exact k33Models_C hv e' h2
  | D r q => exact k33Models_D hv e' h2
  | twistedD r q => exact k33Models_twistedD hv e' h2
  | E6 q => exact k33Models_E6 hv e' h2
  | E7 q => exact k33Models_E7 hv e' h2
  | E8 q => exact k33Models_E8 hv e' h2
  | F4 q => exact k33Models_F4 hv e' h2
  | G2 q => exact k33Models_G2 hv e'
  | twistedE6 q => exact k33Models_twistedE6 hv hs hna e' h2
  | trialityD4 q => exact k33Models_trialityD4 hv e'
  | suzuki m => exact k33Models_suzuki hv e' h2
  | reeG2 m => exact k33Models_reeG2 hv e' h2
  | reeF4 m => exact k33Models_reeF4 hv e'
  | tits => exact k33Models_tits hv e'

theorem k33Models_of_index
    (hbr : ∀ s : TauCeti.SporadicName, Nonempty (Carrier s ≃* s.Group))
    (hJ1 : Nat.card (Carrier .J1) = 2 ^ 3 * 3 * 5 * 7 * 11 * 19)
    (hW : CFSG.SectionRank.SporadicThreeRankWitnesses)
    (hM : Nontrivial (Carrier .M) →
      ∃ E : Subgroup (Carrier .M), IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 4)
    (i : TauCeti.CFSGIndex) {L : Type} [Group L] [Finite L]
    (hs : IsSimpleGroup L) (hna : ∃ a b : L, a * b ≠ b * a) (e : L ≃* i.Group)
    (h2 : CFSG.Open.pRank 3 (⊤ : Subgroup L) = 2) : K33Models L := by
  haveI : Nontrivial L := hs.toNontrivial
  cases i with
  | cyclic p hp => exact k33Models_cyclic hp e hna
  | alternating n hn => exact k33Models_alternating hn e h2
  | lie d => exact k33Models_of_lie d hs hna e h2
  | sporadic s => exact k33Models_sporadic hbr hJ1 hW hM e h2

theorem k33_holds
    : UCK.K33 := by
  intro L _ _ hq hcat hZp h2
  suffices H : K33Cover L ∨ K33Models L from H
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hbr := CFSG.RankThree.PartOne.TCB.nonempty_carrier_mulEquiv_group
  by_cases h3 : 3 ∣ Nat.card (Subgroup.center L)
  · exact Or.inl (k33_threeCover_of_three_dvd
      CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement
      CFSG.Alternating.Multipliers.schurAlternatingMultiplierInput
      CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.sporadicMultipliers_holds
      (hbr .M22) L hq hcat hZp h3 h2)
  · refine Or.inr ?_
    have hZ1 : Subgroup.center L = ⊥ := by
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hZp
      rcases k with _ | k
      · exact Subgroup.eq_bot_of_card_eq _ (by rw [hk]; rfl)
      · rw [hk] at h3
        exact absurd (dvd_pow_self 3 (Nat.succ_ne_zero k)) h3
    obtain ⟨e0⟩ := nonempty_quotCenter_mulEquiv hZ1
    have hs : IsSimpleGroup L := (MulEquiv.isSimpleGroup_congr e0).mp hq.2
    haveI : Nontrivial L := hs.toNontrivial
    have hna : ∃ a b : L, a * b ≠ b * a := by
      by_contra hall
      obtain ⟨x, hx⟩ := exists_ne (1 : L)
      have hxc : x ∈ Subgroup.center L :=
        Subgroup.mem_center_iff.mpr fun g => not_not.mp fun h => hall ⟨g, x, h⟩
      rw [hZ1] at hxc
      exact hx (Subgroup.mem_bot.mp hxc)
    obtain ⟨i, ⟨e⟩⟩ := hcat
    exact k33Models_of_index hbr
      (CFSG.GH74.card_of_isSporadic_J1 ⟨MulEquiv.refl _⟩)
      CFSG.SectionRank.sporadicThreeRankWitnesses
      (fun hN => by
        haveI : Nontrivial CFSG.Blueprint.NativeSporadic.M := hN
        exact CFSG.SectionRank.M_nontrivial_elementary_three_rank_four)
      i hs hna (e0.symm.trans e) h2

end CFSG.LocalAnalysis.UniquenessCase.UCK.K332Route
