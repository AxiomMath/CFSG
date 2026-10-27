module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.CentralSylowTransfer

public section

namespace CFSG.RankThree.PerfectCover

open Subgroup

variable {L : Type*} [Group L]

theorem sylow_le_center_of_not_dvd_card_quotient_center [Finite L] {p : ℕ} [Fact p.Prime]
    (P : Sylow p L) (h : ¬ p ∣ Nat.card (L ⧸ center L)) : (P : Subgroup L) ≤ center L := by
  have hmap : IsPGroup p ((P : Subgroup L).map (QuotientGroup.mk' (center L))) :=
    P.isPGroup'.map _
  have hbot : (P : Subgroup L).map (QuotientGroup.mk' (center L)) = ⊥ := by
    rcases hmap.card_eq_or_dvd with h1 | hdvd
    · exact Subgroup.card_eq_one.mp h1
    · exact absurd (hdvd.trans (Subgroup.card_subgroup_dvd_card _)) h
  rwa [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hbot

theorem sylow_eq_bot_of_not_dvd_card_quotient_center [Finite L] [Group.IsPerfect L] {p : ℕ}
    [Fact p.Prime] (P : Sylow p L) (h : ¬ p ∣ Nat.card (L ⧸ center L)) :
    (P : Subgroup L) = ⊥ := by
  have hZ := sylow_le_center_of_not_dvd_card_quotient_center P h
  have hle := CFSG.ShultStronglyClosedTI.central_pSubgroup_le_sylow_derived P (P : Subgroup L)
    hZ P.isPGroup'
  rw [Subgroup.map_subtype_commutator] at hle
  have hc : ⁅(P : Subgroup L), (P : Subgroup L)⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (hZ.trans (Subgroup.center_le_centralizer _))
  rw [hc] at hle
  exact le_bot_iff.mp hle

theorem perfect_central_quotient_prime_support [Finite L] [Group.IsPerfect L] {p : ℕ}
    (hp : p.Prime) (h : ¬ p ∣ Nat.card (L ⧸ center L)) : ¬ p ∣ Nat.card L := by
  have : Fact p.Prime := ⟨hp⟩
  intro hdvd
  obtain P : Sylow p L := default
  exact P.ne_bot_of_dvd_card hdvd (sylow_eq_bot_of_not_dvd_card_quotient_center P h)

theorem perfect_central_quotient_primeFactors_eq [Finite L] [Group.IsPerfect L] :
    (Nat.card L).primeFactors = (Nat.card (L ⧸ center L)).primeFactors := by
  ext p
  simp only [Nat.mem_primeFactors]
  constructor
  · rintro ⟨hp, hdvd, -⟩
    refine ⟨hp, ?_, Nat.card_pos.ne'⟩
    by_contra hnd
    exact perfect_central_quotient_prime_support hp hnd hdvd
  · rintro ⟨hp, hdvd, -⟩
    exact ⟨hp, hdvd.trans (Subgroup.card_quotient_dvd_card _), Nat.card_pos.ne'⟩

end CFSG.RankThree.PerfectCover
