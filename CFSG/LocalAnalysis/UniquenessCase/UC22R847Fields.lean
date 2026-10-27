module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront08
import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdRank
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup

variable {G : Type} [Group G] [Finite G]

@[expose] def R847ThinCZ (D : Data G) : Prop :=
  ∀ Y ∈ calC D.M, F08.Thin8 Y → ∀ X : Subgroup G, X ≤ Y →
    (Nat.card X).Prime → Nat.card X ≠ 2 →
      pCoreOf 2 D.M ⊓ centralizer (X : Set G) ≠ ⊥ → normalizer (X : Set G) ≤ D.M

@[expose] def R847ThinPair (D : Data G) : Prop :=
  ∀ Y ∈ calC D.M, (Y.subgroupOf D.M).Normal → F08.Thin8 Y → 1 ≤ pRank 3 Y →
    ∀ K ∈ calC D.M, K ≠ Y → 1 ≤ pRank 3 K →
      ∀ X : Subgroup G, X ≤ Y → (Nat.card X).Prime → Nat.card X ≠ 2 →
        normalizer (X : Set G) ≤ D.M

@[expose] def R847SU3G4 (D : Data G) : Prop :=
  ∀ Y ∈ calC D.M, (Y.subgroupOf D.M).Normal → ∀ n : ℕ, IsSU3 (Bar2 Y) n →
    ∀ X : Subgroup G, X ≤ Y → ∀ q : ℕ, q.Prime → q ≠ 2 → q ∣ 2 ^ n - 1 → Nat.card X = q →
      ∀ p ∈ D.sig, normalizer (X : Set G) ≤ D.M ∨
        (p = 3 ∧ (n % 6 = 1 ∨ n % 6 = 5) ∧ evenRank G = 3)

theorem false_of_r847ThinPair (D : Data G) (h : R847ThinPair D) {L K : Subgroup G}
    (hL : L ∈ calC D.M) (hK : K ∈ calC D.M) (hLK : L ≠ K) {p : ℕ} (hp5 : 5 < p)
    (hLp : IsL2Odd (Bar2 L) p) (hLN : (L.subgroupOf D.M).Normal) (hL3 : 1 ≤ pRank 3 L)
    (hK3 : 1 ≤ pRank 3 K) {A : Subgroup G} (hAL : A ≤ L) (hAcard : (Nat.card A).Prime)
    (hAodd : Odd (Nat.card A)) (hAnM : ¬ normalizer (A : Set G) ≤ D.M) : False := by
  have hthin : F08.Thin8 L := fun q hq hq2 => by
    have : Fact q.Prime := ⟨hq⟩
    have hN : ¬ q ∣ Nat.card (CFSG.pCore 2 ↥L) := by
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 2) (G := ↥L))
      rw [hk]
      intro hdvd
      exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 (hq.dvd_of_dvd_pow hdvd))
    rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := q) L,
      ← CFSG.SectionRank.pRank_quotient_eq (p := q) (CFSG.pCore 2 ↥L) hN]
    exact CFSG.QuasithinUnique.Id2519.pRank_le_one_psl_two_prime hLp.admissible.1 (by omega)
      (hLp.statedClassicalModel_of_ne_zero (by norm_num)) hq hq2
  have hq2 : Nat.card A ≠ 2 := fun h2 => by
    rw [h2] at hAodd
    exact (by decide : ¬ Odd 2) hAodd
  exact hAnM (h L hL hLN hthin hL3 K hK hLK.symm hK3 A hAL hAcard hq2)

theorem hkey_of_r847SU3G4 {D : Data G} {L X : Subgroup G} {n r : ℕ} (h : R847SU3G4 D)
    (hL : L ∈ calC D.M) (hLN : (L.subgroupOf D.M).Normal) (hXL : X ≤ L)
    (hXcard : Nat.card X = r) (hSU : IsSU3 (Bar2 L) n) (hrPrime : r.Prime) (hr2 : r ≠ 2)
    (hN : ¬ normalizer (X : Set G) ≤ D.M) (hrn : r ∣ 2 ^ n - 1) :
    ∀ p ∈ D.sig, p = 3 ∧ (n % 6 = 1 ∨ n % 6 = 5) ∧ evenRank G = 3 := by
  intro p hp
  rcases h L hL hLN n hSU X hXL r hrPrime hr2 hrn hXcard p hp with h1 | h2
  · exact absurd h1 hN
  · exact h2

end CFSG.LocalAnalysis.UniquenessCase.UC22
