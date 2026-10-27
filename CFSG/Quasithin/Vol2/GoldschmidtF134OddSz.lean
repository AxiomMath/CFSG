module

public import CFSG.Quasithin.Vol2.GoldschmidtF134OddShared
public import CFSG.Quasithin.Vol2.GoldschmidtF134OddSzArith
public import CFSG.Quasithin.Vol2.GoldschmidtF134OddSzCore
public import CFSG.LieType.Suzuki.SuzukiOuterCyclic
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeBasicBase

public section

namespace CFSG.Quasithin.H13.NQCore

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Vol2Native
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.Blueprint CFSG.LieType.Ree

theorem center_suzukiGroup_eq_bot {a : ℕ} {K : Type} [Field K]
    [Finite K] (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    Subgroup.center (suzukiGroup a K) = ⊥ := by
  obtain ⟨-, hnt, hsimp⟩ := suzuki_simple ha hK
  have hperf := (suzuki_perfect ha hK).2
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (suzukiGroup a K)) with h | h
  · exact h
  · exact absurd (commutator_eq_bot_iff _ |>.1 ((commutator_eq_bot_iff_center_eq_top _).2 h))
      (Group.IsPerfect.not_isMulCommutative _)

theorem normalizer_of_suzuki_borel {A : Type} [Group A]
    {L B U : Subgroup A} {m p : ℕ} (hp : p.Prime) (hL : CFSG.Blueprint.SuzukiModel ↥L 2 m)
    (hUB : U ≤ B) (hBL : B ≤ L) (hU : IsSylowTwoOf U L)
    (hB : ∀ q : ℕ, q.Prime → q ∣ Nat.card B → q = 2 ∨ q = p) :
    B ≤ Subgroup.normalizer (U : Set A) := by
  obtain ⟨-, a, ha, K, _, _, rfl, hK, ⟨e⟩⟩ := hL
  have hUL : U ≤ L := hU.1
  set U' : Subgroup (suzukiGroup a K) := (U.subgroupOf L).map e.toMonoidHom with hU'
  set B' : Subgroup (suzukiGroup a K) := (B.subgroupOf L).map e.toMonoidHom with hB'
  have hU2 : IsPGroup 2 ↥(U.subgroupOf L) :=
    hU.2.1.of_injective (Subgroup.subgroupOfEquivOfLe hUL).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hUL).injective
  have hcard : Nat.card B' = Nat.card B := by
    rw [hB', Subgroup.card_map_of_injective e.injective]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBL).toEquiv
  have hmain : B' ≤ Subgroup.normalizer (U' : Set (suzukiGroup a K)) :=
    le_normalizer_of_not_dvd_card ha hK (hU2.map _)
      (by rw [hU']; exact (Subgroup.index_map_equiv _ e).symm ▸ hU.2.2)
      (Subgroup.map_mono (Subgroup.subgroupOf_mono L hUB))
      (by rw [hcard]; exact not_dvd_of_prime_factors hp ha hB)
  intro y hy
  have hyL : y ∈ L := hBL hy
  have h1 : e ⟨y, hyL⟩ ∈ Subgroup.normalizer (U' : Set (suzukiGroup a K)) :=
    hmain (Subgroup.mem_map_equiv.2 (by
      rw [e.symm_apply_apply]
      exact Subgroup.mem_subgroupOf.2 hy))
  rw [hU', ← Subgroup.map_normalizer_eq_of_bijective _ e.bijective, Subgroup.mem_map_equiv,
    e.symm_apply_apply, ← Subgroup.subgroupOf_normalizer_eq hUL, Subgroup.mem_subgroupOf] at h1
  exact h1

theorem facts134Odd_szLocal :
    ∀ (A : Type) [Group A] [Finite A] (L B U : Subgroup A) (m p : ℕ) (y g : A),
      SQTKHypCat A → p.Prime → 5 ≤ p → IsSz m ↥L → U ≤ B → B ≤ L → IsSylowTwoOf U L →
      (∀ q : ℕ, q.Prime → q ∣ Nat.card B → q = 2 ∨ q = p) → y ∈ B → orderOf y = p →
      g ∈ Subgroup.normalizer (L : Set A) → g ∈ Subgroup.normalizer (U : Set A) →
      g ∈ Subgroup.normalizer ((Subgroup.zpowers y : Subgroup A) : Set A) →
      (∃ k : ℕ, g ^ 2 ^ k = 1) → g * y * g⁻¹ = y := by
  intro A _ _ L B U m p y g _ hp hp5 hL hUB hBL hU hB hyB hyo hgL hgU hgy hg2
  have hSz : CFSG.Blueprint.SuzukiModel ↥L 2 m := hL
  have hodd : Odd (Nat.card (Outer ↥L)) :=
    (CFSG.LieType.Suzuki.Suzuki_model_and_perfect_cover_outer_cyclicity.{0} ↥L 2 m hSz).1.2.2
  have hyN : y ∈ Subgroup.normalizer (U : Set A) :=
    normalizer_of_suzuki_borel hp hSz hUB hBL hU hB hyB
  have hZ : Subgroup.center ↥L = ⊥ := by
    obtain ⟨-, a, ha, K, _, _, rfl, hK, ⟨e⟩⟩ := hSz
    refine (Subgroup.eq_bot_iff_forall _).2 fun x hx => ?_
    have hex : e x ∈ Subgroup.center (suzukiGroup a K) := by
      rw [Subgroup.mem_center_iff] at hx ⊢
      intro s
      obtain ⟨l, rfl⟩ := e.surjective s
      rw [← map_mul, ← map_mul, hx l]
    rw [center_suzukiGroup_eq_bot ha hK, Subgroup.mem_bot] at hex
    exact e.injective (hex.trans (map_one e).symm)
  obtain ⟨x, hx⟩ := exists_inner_of_odd_outer hgL hodd hg2
  exact fix_of_inner hZ hU hp (by omega) (hBL hyB) hyo hyN hgU hgy hg2 hx

end CFSG.Quasithin.H13.NQCore
