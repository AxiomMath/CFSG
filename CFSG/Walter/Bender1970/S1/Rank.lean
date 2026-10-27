module

public import CFSG.LocalAnalysis.SectionRank.PRank
import CFSG.LocalAnalysis.SectionRank.SubgroupRank

public section

namespace CFSG.Walter

open CFSG.Open CFSG.SectionRank

variable {G : Type*} [Group G] [Finite G]

@[expose] noncomputable def rank (X : Subgroup G) : ℕ :=
  sSup {n | ∃ p : ℕ, p.Prime ∧ n ≤ pRank p X}

theorem pRank_le_card {p : ℕ} (hp : p.Prime) (X : Subgroup G) : pRank p X ≤ Nat.card G :=
  CFSG.SectionRank.pRank_le_card_of_one_lt hp.one_lt X

private theorem rank_set_bddAbove (X : Subgroup G) :
    BddAbove {n | ∃ p : ℕ, p.Prime ∧ n ≤ pRank p X} :=
  ⟨Nat.card G, fun _ ⟨_, hp, hn⟩ => hn.trans (pRank_le_card hp X)⟩

theorem pRank_le_rank {p : ℕ} (hp : p.Prime) (X : Subgroup G) : pRank p X ≤ rank X :=
  le_csSup (rank_set_bddAbove X) ⟨p, hp, le_rfl⟩

theorem rank_le {X : Subgroup G} {n : ℕ} (h : ∀ p : ℕ, p.Prime → pRank p X ≤ n) :
    rank X ≤ n :=
  csSup_le ⟨0, 2, Nat.prime_two, Nat.zero_le _⟩ fun _ ⟨p, hp, hm⟩ => hm.trans (h p hp)

theorem rank_le_iff {X : Subgroup G} {n : ℕ} :
    rank X ≤ n ↔ ∀ p : ℕ, p.Prime → pRank p X ≤ n :=
  ⟨fun h _ hp => (pRank_le_rank hp X).trans h, rank_le⟩

theorem exists_pRank_eq_rank (X : Subgroup G) : ∃ p : ℕ, p.Prime ∧ pRank p X = rank X := by
  obtain ⟨p, hp, hle⟩ := Nat.sSup_mem (s := {n | ∃ p : ℕ, p.Prime ∧ n ≤ pRank p X})
    ⟨0, 2, Nat.prime_two, Nat.zero_le _⟩ (rank_set_bddAbove X)
  exact ⟨p, hp, le_antisymm (pRank_le_rank hp X) hle⟩

theorem exists_isElemAbelian_card_eq_pow_rank (X : Subgroup G) :
    ∃ p : ℕ, p.Prime ∧ ∃ E : Subgroup G, E ≤ X ∧ IsElemAbelian p E ∧
      Nat.card E = p ^ rank X := by
  obtain ⟨p, hp, hpr⟩ := exists_pRank_eq_rank X
  obtain ⟨E, hEX, hE, hcard⟩ := exists_pRank hp.one_lt X
  exact ⟨p, hp, E, hEX, hE, hpr ▸ hcard⟩

theorem le_rank {p : ℕ} (hp : p.Prime) {X E : Subgroup G} (hEX : E ≤ X)
    (hE : IsElemAbelian p E) {k : ℕ} (hk : Nat.card E = p ^ k) : k ≤ rank X :=
  (le_pRank hp.one_lt hEX hE hk).trans (pRank_le_rank hp X)

theorem rank_mono {X Y : Subgroup G} (hXY : X ≤ Y) : rank X ≤ rank Y :=
  rank_le fun _ hp => (pRank_mono hp.one_lt hXY).trans (pRank_le_rank hp Y)

theorem pRank_eq_zero_of_isPGroup {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : q ≠ p)
    {X : Subgroup G} (hX : IsPGroup p X) : pRank q X = 0 := by
  obtain ⟨E, hEX, -, hcard⟩ := exists_pRank hq.one_lt X
  by_contra hne
  have hqE : q ∣ Nat.card E := by
    rw [hcard]
    exact dvd_pow_self q hne
  have hEp : IsPGroup p E := hX.to_le hEX
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨m, hm⟩ := hEp.exists_card_eq
  rw [hm] at hqE
  exact hpq ((Nat.prime_dvd_prime_iff_eq hq hp).1 (hq.dvd_of_dvd_pow hqE))

theorem rank_eq_pRank_of_isPGroup {p : ℕ} (hp : p.Prime) {X : Subgroup G}
    (hX : IsPGroup p X) : rank X = pRank p X := by
  refine le_antisymm (rank_le fun q hq => ?_) (pRank_le_rank hp X)
  by_cases hqp : q = p
  · rw [hqp]
  · rw [pRank_eq_zero_of_isPGroup hp hq hqp hX]
    exact Nat.zero_le _

end CFSG.Walter
