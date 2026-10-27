module

public import CFSG.Assembly.RankThreeEvenDefs
import CFSG.RankThree.OddKernel.ThreeComplementQuotient

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven

namespace PlaneAux

theorem evenRank_le_of_injective {X Y : Type*} [Group X] [Group Y] [Finite X] [Finite Y]
    (f : X →* Y) (hf : Function.Injective f) : evenRank X ≤ evenRank Y := by
  apply csSup_le'
  rintro _ ⟨p, K, hp, hp2, ⟨P, hP, hP2, rfl⟩, rfl⟩
  refine ((CFSG.RankThreeEvenClassification.Helpers.pRank_le_map_of_injective p hp f hf
    (Subgroup.normalizer (P : Set X))).trans
      (CFSG.RankThreeEvenClassification.Helpers.pRank_mono p hp
        (Subgroup.le_normalizer_map f))).trans
    (CFSG.RankThreeEvenClassification.Helpers.pRank_le_evenRank p hp hp2 _
      ⟨P.map f, fun h => hP ((Subgroup.map_eq_bot_iff_of_injective P hf).mp h), hP2.map _, rfl⟩)

theorem localRank_le_of_injective {X Y : Type*} [Group X] [Group Y] [Finite X] [Finite Y]
    {p : ℕ} (hp : p.Prime) (f : X →* Y) (hf : Function.Injective f) :
    localRank p X ≤ localRank p Y := by
  apply csSup_le'
  rintro _ ⟨K, ⟨P, hP, hP2, rfl⟩, rfl⟩
  refine ((CFSG.RankThreeEvenClassification.Helpers.pRank_le_map_of_injective p hp f hf
    (Subgroup.normalizer (P : Set X))).trans
      (CFSG.RankThreeEvenClassification.Helpers.pRank_mono p hp
        (Subgroup.le_normalizer_map f))).trans ?_
  exact CFSG.RankThreeEvenClassification.Helpers.pRank_le_twoLocalRank p hp _
      ⟨P.map f, fun h => hP ((Subgroup.map_eq_bot_iff_of_injective P hf).mp h), hP2.map _, rfl⟩

theorem localRank_eq_zero_of_not_dvd {r : ℕ} (hr : r.Prime) {X : Type*} [Group X] [Finite X]
    (h : ¬ r ∣ Nat.card X) : localRank r X = 0 := by
  apply Nat.eq_zero_of_le_zero
  apply csSup_le'
  rintro _ ⟨K, -, rfl⟩
  exact (CFSG.RankThreeEvenClassification.Helpers.pRank_eq_zero_of_not_dvd r hr h K).le

theorem evenRank_le_of_localRank_le_of_card {X : Type*} [Group X] [Finite X] {p m : ℕ}
    (hp : p.Prime)
    (hcard : ∀ r : ℕ, r.Prime → r ∣ Nat.card X → r = 2 ∨ r = p) (h : localRank p X ≤ m) :
    evenRank X ≤ m := by
  refine CFSG.RankThree.OddKernel.evenRank_le_of_localRank_le fun r hr hr2 => ?_
  by_cases hrd : r ∣ Nat.card X
  · rcases hcard r hr hrd with h2 | rfl
    · exact absurd h2 hr2
    · exact h
  · rw [localRank_eq_zero_of_not_dvd hr hrd]
    exact Nat.zero_le _

theorem le_evenRank_of_hom_normalizes {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {A : Type*} [Group A] (hcomm : ∀ a b : A, a * b = b * a)
    (hpow : ∀ a : A, a ^ p = 1) {k : ℕ} (hA : Nat.card A = p ^ k) (f : A →* G)
    (hf : Function.Injective f) {U : Subgroup G} (hU : U ≠ ⊥) (hU2 : IsPGroup 2 U)
    (hfU : ∀ a : A, f a ∈ Subgroup.normalizer (U : Set G)) : k ≤ evenRank G :=
  (CFSG.SectionRank.le_pRank_of_injective hp.one_lt hcomm hpow hA f hf
    (fun _ ⟨a, ha⟩ => ha ▸ hfU a)).trans
    (CFSG.RankThreeEvenClassification.Helpers.pRank_le_evenRank p hp hp2 _ ⟨U, hU, hU2, rfl⟩)

theorem eq_one_of_smul_eq_inner {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {B S : Type*} [Group B]
    [Group S] [MulDistribMulAction B S] [Finite B] [Finite S] (hB : IsPGroup p B)
    (hS : IsPGroup 2 S) (hfaith : ∀ c : B, (∀ t : S, c • t = t) → c = 1) {s : S} {b : B}
    (h : ∀ t : S, b • t = s⁻¹ * t * s) : b = 1 := by
  have hbs : b • s = s := by rw [h s]; group
  have hpowk : ∀ (k : ℕ) (t : S), (b ^ k) • t = (s ^ k)⁻¹ * t * s ^ k := by
    intro k
    induction k with
    | zero => intro t; simp
    | succ k ih =>
      intro t
      rw [pow_succ', mul_smul, ih t, smul_mul', smul_mul', smul_inv', smul_pow', hbs, h t]
      group
  obtain ⟨j, hj⟩ := hB b
  have hbn : b ^ (p ^ j) = 1 := hj
  have hcentral : ∀ t : S, (s ^ (p ^ j)) * t = t * s ^ (p ^ j) := by
    intro t
    have := hpowk (p ^ j) t
    rw [hbn, one_smul] at this
    calc s ^ (p ^ j) * t = s ^ (p ^ j) * ((s ^ (p ^ j))⁻¹ * t * s ^ (p ^ j)) := by rw [← this]
      _ = t * s ^ (p ^ j) := by group
  obtain ⟨i, hi⟩ := hS s
  have hcop : IsCoprime ((p ^ j : ℕ) : ℤ) ((2 ^ i : ℕ) : ℤ) := by
    rw [Nat.isCoprime_iff_coprime]
    exact Nat.Coprime.pow _ _ ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
  obtain ⟨u, v, huv⟩ := hcop
  have hs : s = (s ^ (p ^ j)) ^ u := by
    have h1 : s ^ (2 ^ i) = 1 := hi
    have e : ((p ^ j : ℕ) : ℤ) * u + ((2 ^ i : ℕ) : ℤ) * v = 1 := by linarith
    calc s = s ^ (((p ^ j : ℕ) : ℤ) * u + ((2 ^ i : ℕ) : ℤ) * v) := by rw [e, zpow_one]
      _ = (s ^ (p ^ j)) ^ u := by
        rw [zpow_add, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast, h1, one_zpow, mul_one]
  have hscomm : ∀ t : S, s * t = t * s := fun t => by
    have hc : Commute (s ^ (p ^ j)) t := hcentral t
    have h2 := (hc.zpow_left u).eq
    rwa [← hs] at h2
  refine hfaith b fun t => ?_
  rw [h t]
  calc s⁻¹ * t * s = s⁻¹ * (t * s) := mul_assoc _ _ _
    _ = s⁻¹ * (s * t) := by rw [hscomm t]
    _ = t := inv_mul_cancel_left s t

end PlaneAux

end CFSG.RankThree.PartOne
