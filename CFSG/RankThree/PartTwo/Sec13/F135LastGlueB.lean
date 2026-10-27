module

public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.LocalAnalysis.SectionRank.SQT

public section

namespace CFSG.RankThree.PartTwo.Sec13.F135Last

open CFSG Subgroup
open scoped commutatorElement

theorem gb_pRank_le_card {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : 1 < p)
    (H : Subgroup G) : CFSG.Open.pRank p H ≤ Nat.card G := by
  obtain ⟨E, -, -, hE⟩ := CFSG.SectionRank.exists_pRank hp H
  have h1 : CFSG.Open.pRank p H < p ^ CFSG.Open.pRank p H := Nat.lt_pow_self hp
  have h2 : Nat.card E ≤ Nat.card G := Subgroup.card_le_card_group E
  omega

theorem gb_pRank_le_evenRank {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {H : Subgroup G} (hH : CFSG.Open.IsTwoLocal H) :
    CFSG.Open.pRank p H ≤ CFSG.Open.evenRank G := by
  have hbdd : BddAbove {k | ∃ (q : ℕ) (K : Subgroup G), q.Prime ∧ q ≠ 2 ∧
      CFSG.Open.IsTwoLocal K ∧ CFSG.Open.pRank q K = k} := by
    refine ⟨Nat.card G, ?_⟩
    rintro k ⟨q, K, hq, -, -, rfl⟩
    exact gb_pRank_le_card hq.one_lt K
  have hmem : CFSG.Open.pRank p H ∈ {k | ∃ (q : ℕ) (K : Subgroup G), q.Prime ∧ q ≠ 2 ∧
      CFSG.Open.IsTwoLocal K ∧ CFSG.Open.pRank q K = k} :=
    ⟨p, H, hp, hp2, hH, rfl⟩
  exact le_csSup hbdd hmem

theorem gb_conj_fix_zpowers {G : Type*} [Group G] {g x : G} (hc : g * x = x * g) :
    ∀ z ∈ Subgroup.zpowers x, g * z * g⁻¹ = z := by
  intro z hz
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
  rw [((show Commute g x from hc).zpow_right k).eq, mul_assoc, mul_inv_cancel, mul_one]

theorem gb_mem_zpowers_conj_iff {G : Type*} [Group G] {g x : G} (hc : g * x = x * g) (h : G) :
    h ∈ Subgroup.zpowers x ↔ g * h * g⁻¹ ∈ Subgroup.zpowers x := by
  have hc' : g⁻¹ * x = x * g⁻¹ := ((show Commute g x from hc).inv_left).eq
  constructor
  · intro hh
    rw [gb_conj_fix_zpowers hc h hh]
    exact hh
  · intro hh
    have e := gb_conj_fix_zpowers hc' _ hh
    rw [inv_inv, show g⁻¹ * (g * h * g⁻¹) * g = h by group] at e
    rw [e]
    exact hh

theorem gb_centralizer_eq_normalizer_zpowers {G : Type*} [Group G] {x : G} (hx1 : x ≠ 1)
    (hxx : x * x = 1) :
    Subgroup.centralizer ({x} : Set G) =
      Subgroup.normalizer ((Subgroup.zpowers x : Subgroup G) : Set G) := by
  have hord : orderOf x = 2 := orderOf_eq_prime (p := 2) (by rw [pow_two]; exact hxx) hx1
  ext g
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_normalizer_iff]
  refine ⟨fun hc h => gb_mem_zpowers_conj_iff hc h, fun hn => ?_⟩
  have hy : g * x * g⁻¹ ∈ Subgroup.zpowers x := (hn x).1 (Subgroup.mem_zpowers x)
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hy
  have hk2 : x ^ (k % 2) = x ^ k := by
    have := zpow_mod_orderOf x k
    rw [hord] at this
    exact_mod_cast this
  rcases Int.emod_two_eq_zero_or_one k with h0 | h1
  · exfalso
    have h1' : g * x * g⁻¹ = 1 := by rw [← hk, ← hk2, h0, zpow_zero]
    apply hx1
    simpa using h1'
  · have hy' : g * x * g⁻¹ = x := by rw [← hk, ← hk2, h1, zpow_one]
    exact mul_inv_eq_iff_eq_mul.1 hy'

theorem gb_isTwoLocal_centralizer {G : Type*} [Group G] {x : G} (hx1 : x ≠ 1)
    (hxx : x * x = 1) : CFSG.Open.IsTwoLocal (Subgroup.centralizer ({x} : Set G)) := by
  have hord : orderOf x = 2 := orderOf_eq_prime (p := 2) (by rw [pow_two]; exact hxx) hx1
  refine ⟨Subgroup.zpowers x, fun h => hx1 (Subgroup.zpowers_eq_bot.1 h), ?_,
    gb_centralizer_eq_normalizer_zpowers hx1 hxx⟩
  exact IsPGroup.of_card ((Nat.card_zpowers x).trans (hord.trans (pow_one (2 : ℕ)).symm))

theorem hrank3_of_evenRank {G : Type} [Group G] [Finite G] (h : CFSG.Open.evenRank G = 3)
    (M : Subgroup G) : ∀ t : M, t ≠ 1 → t * t = 1 → ∀ X : Subgroup M, IsPGroup 3 X →
      X ≤ centralizer ({t} : Set M) → CFSG.pRank 3 X ≤ 3 := by
  intro t ht htt X _ hXt
  have hx1 : (t : G) ≠ 1 := fun h1 => ht (Subtype.ext (by simpa using h1))
  have hxx : (t : G) * (t : G) = 1 := by
    have h2 := congrArg (fun y : M => (y : G)) htt
    simpa using h2
  have hHrank : CFSG.Open.pRank 3 (Subgroup.centralizer ({(t : G)} : Set G)) ≤ 3 := by
    have hle := gb_pRank_le_evenRank (p := 3) Nat.prime_three (by norm_num)
      (gb_isTwoLocal_centralizer hx1 hxx)
    rwa [h] at hle
  have hf : Function.Injective (M.subtype.comp X.subtype) :=
    fun a b hab => Subtype.ext (Subtype.ext hab)
  have hmap : (⊤ : Subgroup ↥X).map (M.subtype.comp X.subtype) ≤
      Subgroup.centralizer ({(t : G)} : Set G) := by
    intro z hz
    obtain ⟨y, -, rfl⟩ := Subgroup.mem_map.1 hz
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hy := Subgroup.mem_centralizer_singleton_iff.1 (hXt y.2)
    have hy' := congrArg (fun w : M => (w : G)) hy
    simpa using hy'
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top 3 ↥X]
  calc CFSG.Open.pRank 3 (⊤ : Subgroup ↥X)
      ≤ CFSG.Open.pRank 3 ((⊤ : Subgroup ↥X).map (M.subtype.comp X.subtype)) :=
        CFSG.SectionRank.pRank_le_map (p := 3) (by norm_num) _ hf _
    _ ≤ CFSG.Open.pRank 3 (Subgroup.centralizer ({(t : G)} : Set G)) :=
        CFSG.SectionRank.pRank_mono (p := 3) (by norm_num) hmap
    _ ≤ 3 := hHrank

theorem exists_noncentral_of_relIndex {H : Type*} [Group H] (J Ebar : Subgroup H) (p : ℕ)
    (hp : 2 ≤ p ^ 3) (h : p ^ 3 ≤ (Subgroup.centralizer (J : Set H) ⊓ Ebar).relIndex Ebar) :
    ∃ e ∈ Ebar, ∃ j ∈ J, ⁅e, j⁆ ≠ 1 := by
  by_contra hcon
  have hcon' : ∀ e ∈ Ebar, ∀ j ∈ J, ⁅e, j⁆ = 1 := fun e he j hj =>
    not_not.1 fun hne => hcon ⟨e, he, j, hj, hne⟩
  have hle : Ebar ≤ Subgroup.centralizer (J : Set H) := by
    intro e he
    rw [Subgroup.mem_centralizer_iff]
    intro j hj
    exact (commutatorElement_eq_one_iff_mul_comm.1 (hcon' e he j hj)).symm
  rw [inf_eq_right.2 hle, Subgroup.relIndex_self] at h
  omega

end CFSG.RankThree.PartTwo.Sec13.F135Last
