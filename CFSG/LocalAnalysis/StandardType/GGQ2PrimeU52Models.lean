module

public import CFSG.LocalAnalysis.StandardType.GGQ2PrimeU52Bridge
public import CFSG.Adapters.StatedClassicalUnitaryOrders
public import CFSG.Adapters.LieModelSimple
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.StandardType.GGPRankBoundsSU

public section

namespace CFSG.GGQ2Prime

open Subgroup CFSG.Open CFSG.Models
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)

theorem exists_noncomm_of_simple {M : Type} [Group M]
    [Finite M] [IsSimpleGroup M] {p : ℕ} (hp : p.Prime)
    (hd : p ∣ Nat.card M) (hne : Nat.card M ≠ p) : ∃ a b : M, a * b ≠ b * a := by
  by_contra h
  push Not at h
  haveI := Fact.mk hp
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hd
  haveI hN : (zpowers x).Normal := ⟨fun n hn g => by
    have : g * n * g⁻¹ = n := by rw [h g n]; group
    rw [this]; exact hn⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (zpowers x) with h1 | h1
  · have : x = 1 := by rw [← mem_bot, ← h1]; exact mem_zpowers x
    rw [this, orderOf_one] at hx
    exact hp.ne_one hx.symm
  · apply hne
    have := Nat.card_zpowers x
    rw [h1, card_top, hx] at this
    exact this

theorem center_eq_bot_of_noncomm {M : Type} [Group M]
    [IsSimpleGroup M] (h : ∃ a b : M, a * b ≠ b * a) :
    center M = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center M) with h1 | h1
  · exact h1
  · obtain ⟨a, b, hab⟩ := h
    exact absurd (mem_center_iff.1 (h1 ▸ mem_top b) a) hab

theorem model_SU (K : Type) [Field K] [Finite K] (n : ℕ) (hn : 4 ≤ n)
    (hK : Nat.card K = (2 ^ 1) ^ 2) :
    StatedClassicalModel (StatedProj (StatedSU n (2 ^ 1) K)) .PSU n 2 1 :=
  ⟨⟨Nat.prime_two, le_rfl, by omega, fun h => by
    have := congrArg Prod.fst h; simp only at this; omega⟩,
    K, inferInstance, inferInstance, hK, ⟨MulEquiv.refl _⟩⟩

theorem u52_finite (K : Type) [Field K] [Finite K] (hK : Nat.card K = (2 ^ 1) ^ 2) :
    Finite (StatedProj (StatedSU 5 (2 ^ 1) K)) :=
  Nat.finite_of_card_ne_zero (by
    rw [CFSG.Open.StatedAPI.card_of_statedClassicalModel_psu_five_two
      (model_SU K 5 (by norm_num) hK)]; norm_num)

theorem u52_center (K : Type) [Field K] [Finite K] (hK : Nat.card K = (2 ^ 1) ^ 2) :
    center (StatedProj (StatedSU 5 (2 ^ 1) K)) = ⊥ := by
  have hmod := model_SU K 5 (by norm_num) hK
  have hcard := CFSG.Open.StatedAPI.card_of_statedClassicalModel_psu_five_two hmod
  haveI := u52_finite K hK
  haveI := CFSG.Open.StatedAPI.isSimpleGroup_of_statedClassicalModel hmod
  exact center_eq_bot_of_noncomm
    (exists_noncomm_of_simple Nat.prime_two (by rw [hcard]; norm_num) (by rw [hcard]; norm_num))

theorem u52OrderThreeAutInner : U52OrderThreeAutInner := by
  intro K _ _ hK φ hφ
  have hO := CFSG.StandardType.PRankBounds.card_outer_psu5 (model_SU K 5 (by norm_num) hK)
  set q : Outer (StatedProj (StatedSU 5 (2 ^ 1) K)) := QuotientGroup.mk' (inner _) φ with hq
  have h3 : q ^ 3 = 1 := by rw [hq, ← map_pow, hφ, map_one]
  have h2 : q ^ 2 = 1 := by
    have := pow_card_eq_one' (G := Outer (StatedProj (StatedSU 5 (2 ^ 1) K))) (x := q)
    rwa [hO] at this
  have h1 : q = 1 := by
    calc q = q ^ 3 * (q ^ 2)⁻¹ := by group
      _ = 1 := by rw [h3, h2]; group
  rw [hq, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  obtain ⟨r, hr⟩ := h1
  exact ⟨r, hr.symm⟩

end CFSG.GGQ2Prime

end
