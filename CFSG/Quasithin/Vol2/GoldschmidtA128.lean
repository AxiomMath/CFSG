module

public import CFSG.Quasithin.Vol2.Ch11StatementsInputsAS
public import CFSG.Quasithin.Vol2.GoldschmidtA128Rank
public import CFSG.Quasithin.Vol2.GoldschmidtA128Loc
import CFSG.LocalAnalysis.SectionRank.AmbientRank

public section

namespace CFSG.Quasithin.ASInputs

open Subgroup CFSG.Open CFSG.SectionRank CFSG.QuasithinUnique CFSG.Quasithin.Vol2.A128

theorem pRank_eq_open (p : ℕ) {G : Type*} [Group G] [Finite G] (X : Subgroup G) :
    CFSG.pRank p ↥X = CFSG.Open.pRank p X := CFSG.SectionRank.pRank_coe_eq_openPRank p X

theorem as_A_1_28_holds : AS_A_1_28 := by
  intro G _ _ p hp hp2 hG0 H hH0
  have : Fact p.Prime := ⟨hp⟩
  have hG : ∀ P : Subgroup G, P ≠ ⊥ → IsPGroup 2 P →
      CFSG.Open.pRank p (normalizer (P : Set G)) ≤ 2 := fun P hP h2 => by
    rw [← pRank_eq_open]
    exact hG0 P hP h2
  have hH : 2 < CFSG.Open.pRank p (pCoreOf p H) := by
    rw [← pRank_eq_open]
    exact hH0
  have hPn : (CFSG.Open.pCore p ↥H).Normal := CFSG.LieType.BorelTits.pCore_normal p
  have hP : IsPGroup p (CFSG.Open.pCore p ↥H) := CFSG.LieType.BorelTits.pCore_isPGroup p
  have hP1 : CFSG.Open.pCore p ↥H ≠ ⊥ := by
    intro h
    have h0 : CFSG.Open.pRank p (pCoreOf p H) ≤ 0 := by
      refine CFSG.SectionRank.pRank_le hp.one_lt fun E hE _ => ?_
      have : pCoreOf p H = ⊥ := by
        unfold pCoreOf
        rw [h, Subgroup.map_bot]
      rw [this, le_bot_iff] at hE
      rw [hE, Subgroup.card_bot]
      simp
    omega
  have hno : ∀ t : ↥H, t * t = 1 → t ≠ 1 → ∃ x ∈ CFSG.Open.pCore p ↥H, t * x ≠ x * t := by
    intro t ht ht1
    by_contra hcon
    push Not at hcon
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have ht2 : orderOf (t : G) = 2 := by
      refine orderOf_eq_prime ?_ ?_
      · have := congrArg Subtype.val ht
        simpa [pow_two] using this
      · exact fun h => ht1 (Subtype.ext h)
    refine not_centralizes_core hG hH ht2 ?_
    rintro _ ⟨x, hx, rfl⟩
    exact congrArg Subtype.val (hcon x hx)
  have hloc : ∀ t : ↥H, orderOf t = 2 → CFSG.Open.pRank p (centralizer {t} : Subgroup ↥H) ≤ 2 :=
    fun t ht => pRank_centralizer_le hG H ht
  obtain ⟨E, hEH, hEel, hEcard⟩ := CFSG.SectionRank.exists_pRank (G := G) (p := 2) one_lt_two H
  have hE'card : Nat.card (E.subgroupOf H) = Nat.card E :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEH).toEquiv
  have hE'sq : ∀ x ∈ E.subgroupOf H, x * x = 1 := by
    intro x hx
    have := hEel.2 (x : G) (Subgroup.mem_subgroupOf.mp hx)
    exact Subtype.ext (by simpa [pow_two] using this)
  have hE'comm : ∀ x ∈ E.subgroupOf H, ∀ y ∈ E.subgroupOf H, x * y = y * x := by
    intro x hx y hy
    have := hEel.1.is_comm.comm ⟨(x : G), Subgroup.mem_subgroupOf.mp hx⟩
      ⟨(y : G), Subgroup.mem_subgroupOf.mp hy⟩
    exact Subtype.ext (congrArg (fun z : E => (z : G)) this)
  obtain ⟨hle, hspec⟩ := rank_bound_of_setting hp2 hP hP1 hno hloc (E.subgroupOf H) hE'sq hE'comm
  rw [pRank_eq_open]
  refine ⟨?_, fun h3 => ?_⟩
  · have h8 : 2 ^ CFSG.Open.pRank 2 H ≤ 2 ^ 3 := by
      rw [← hEcard, ← hE'card]
      simpa using hle
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 h8
  · have h8 : Nat.card (E.subgroupOf H) = 8 := by
      rw [hE'card, hEcard, h3]
      norm_num
    obtain ⟨a, haE, ha1, hcomm⟩ := hspec h8
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine ⟨(a : G), a.2, ?_, fun h hh => ?_⟩
    · refine orderOf_eq_prime ?_ ?_
      · have := congrArg Subtype.val (hE'sq a haE)
        simpa [pow_two] using this
      · exact fun h => ha1 (Subtype.ext h)
    · exact ⟨a * ⟨h, hh⟩ * a⁻¹ * ⟨h, hh⟩⁻¹, hcomm ⟨h, hh⟩, rfl⟩

end CFSG.Quasithin.ASInputs
