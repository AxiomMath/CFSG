module

public import CFSG.RankThree.PartOne.Q1327.Defs
public import CFSG.RankThree.PartOne.KF.ClsCenter
public import CFSG.RankThree.PartOne.KF.RowCore
public import CFSG.RankThree.PartTwo.Census.Classical.EvenWitness

public section

namespace CFSG.RankThree.PartOne.Q1327C

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.Assembly.LowTwoRank
  CFSG.RankThree.PartOne

variable {G : Type} [Group G] [Finite G]

namespace T123Base

variable {p : ℕ} {L A₀ F : Subgroup G} (h : Q1327.T123Base p L A₀ F)

include h in
theorem coprime_center : Nat.Coprime p (Nat.card (Subgroup.center ↥L)) :=
  (Nat.Prime.coprime_iff_not_dvd h.prime).mpr h.center_pPrime

include h in
theorem toCore : Table123Core p L A₀ F :=
  { prime := h.prime
    five_le := h.five_le
    quasisimple := h.quasisimple
    center_pPrime := h.center_pPrime
    A₀_le := h.A₀_le
    A₀_elem := h.A₀_elem
    A₀_card := h.A₀_card
    A₀_invariant := h.A₀_invariant
    F_le := h.F_le
    F_elem := h.F_elem
    A₀_le_F := h.A₀_le_F
    F_le_centralizer := h.F_le_centralizer
    F_max := h.F_max }

include h in
theorem two_le_localRank_quot : 2 ≤ localRank p (↥L ⧸ Subgroup.center ↥L) := by
  obtain ⟨S, hSL, hS0, hS2, hAS, hSA⟩ := h.A₀_invariant
  have hp := h.prime
  have := h.A₀_elem
  have hE : IsElemAbelian p (A₀.subgroupOf L) := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
    · apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun y : ↥A₀ => (y : G))
        (h.A₀_elem.is_comm.comm ⟨(a : G), a.2⟩ ⟨(b : G), b.2⟩)
    · apply Subtype.ext
      have hx' : ((x : ↥L) : G) ^ p = 1 :=
        elemPow_eq_one_of_isElementaryAbelian (p := p) (x : G) hx
      rw [Subgroup.coe_pow, OneMemClass.coe_one]
      exact hx'
  have hc : Nat.card (A₀.subgroupOf L) = p ^ 2 := by
    rw [← h.A₀_card]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.A₀_le).toEquiv
  have hEN : A₀.subgroupOf L ⊓ Subgroup.center ↥L = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxA, hxZ⟩
    have hxp : x ^ p = 1 := by
      apply Subtype.ext
      have hx' : ((x : ↥L) : G) ^ p = 1 :=
        elemPow_eq_one_of_isElementaryAbelian (p := p) (x : G) hxA
      exact hx'
    have h1 : orderOf x ∣ p := orderOf_dvd_of_pow_eq_one hxp
    have h2 : orderOf x ∣ Nat.card (Subgroup.center ↥L) :=
      Subgroup.orderOf_dvd_natCard (Subgroup.center ↥L) hxZ
    have h3 : orderOf x ∣ Nat.gcd p (Nat.card (Subgroup.center ↥L)) := Nat.dvd_gcd h1 h2
    rw [coprime_center h] at h3
    exact Subgroup.mem_bot.mpr (orderOf_eq_one_iff.mp (Nat.dvd_one.mp h3))
  have hP2 : IsPGroup 2 (S.subgroupOf L) := hS2.comap_subtype
  have hPN : ¬ S.subgroupOf L ≤ Subgroup.center ↥L := by
    intro hle
    apply hS0
    rw [hSA, eq_bot_iff, Subgroup.commutator_le]
    intro s hs a ha
    have hsL : (⟨s, hSL hs⟩ : ↥L) ∈ Subgroup.center ↥L := hle hs
    have := Subgroup.mem_center_iff.mp hsL ⟨a, h.A₀_le ha⟩
    rw [Subgroup.mem_bot, commutatorElement_def]
    have h4 : s * a = a * s := congrArg Subtype.val this.symm
    calc s * a * s⁻¹ * a⁻¹ = (a * s) * s⁻¹ * a⁻¹ := by rw [h4]
      _ = 1 := by group
  have hEP : A₀.subgroupOf L ≤ Subgroup.normalizer ((S.subgroupOf L : Subgroup ↥L) : Set ↥L) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have hxA : (x : G) ∈ A₀ := hx
    have h5 := Subgroup.mem_normalizer_iff.mp (hAS hxA) (y : G)
    change (y : G) ∈ S ↔ (x : G) * y * (x : G)⁻¹ ∈ S at h5
    exact h5
  exact CFSG.RankThree.PartTwo.Census.le_localRank_quotient_of_le_normalizer
    (Subgroup.center ↥L) hp hE hc hEN hP2 hPN hEP

include h in
theorem two_le_localRank_of_mulEquiv {Y : Type} [Group Y] [Finite Y]
    (e : ↥L ⧸ Subgroup.center ↥L ≃* Y) : 2 ≤ localRank p Y := by
  rw [← CFSG.RankThree.PartTwo.Census.localRank_eq_of_mulEquiv e h.prime]
  exact two_le_localRank_quot h

include h in
theorem localRank_quot_le_three
    (hZ : ∀ r : ℕ, r.Prime → r ≠ 2 → ¬ r ∣ Nat.card (Subgroup.center ↥L)) {r : ℕ}
    (hr : r.Prime) (hr2 : r ≠ 2) : localRank r (↥L ⧸ Subgroup.center ↥L) ≤ 3 := by
  have h1 := CFSG.RankThree.Classical2.localRank_quotient_le hr hr2 (Subgroup.center ↥L)
    (hZ r hr hr2)
  exact h1.trans ((CFSG.RankThree.OddKernel.localRank_le_evenRank hr hr2).trans h.evenRank_le)

include h in
theorem localRank_quot_le_three_of {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hrZ : ¬ r ∣ Nat.card (Subgroup.center ↥L)) :
    localRank r (↥L ⧸ Subgroup.center ↥L) ≤ 3 := by
  have h1 := CFSG.RankThree.Classical2.localRank_quotient_le hr hr2 (Subgroup.center ↥L) hrZ
  exact h1.trans ((CFSG.RankThree.OddKernel.localRank_le_evenRank hr hr2).trans h.evenRank_le)

include h in
theorem evenRank_quot_le
    (hZ : ∀ r : ℕ, r.Prime → r ≠ 2 → ¬ r ∣ Nat.card (Subgroup.center ↥L)) :
    evenRank (↥L ⧸ Subgroup.center ↥L) ≤ 3 :=
  CFSG.RankThree.OddKernel.evenRank_le_of_localRank_le (m := 3) fun _ hr hr2 =>
    localRank_quot_le_three h hZ hr hr2

include h in
theorem card_center_dvd_multiplier
    (hGA : CFSG.Open.GriessAllModelsStatement)
    {t : StatedLieTag} {n f : ℕ} (hm : Models.LieModel (↥L ⧸ Subgroup.center ↥L) t n 2 f) :
    Nat.card (Subgroup.center ↥L) ∣
      Nat.card (Blueprint.Multiplier.generic t n 2 f ×
        Blueprint.Multiplier.exceptional t n 2 f) := by
  obtain ⟨hperf, hcard⟩ := card_hopfMultiplier_of_model hGA hm
  have hd := card_ker_dvd_card_hopfMultiplier hperf h.quasisimple.1
    (QuotientGroup.mk' (Subgroup.center ↥L)) (QuotientGroup.mk'_surjective _)
    (by rw [QuotientGroup.ker_mk'])
  rwa [QuotientGroup.ker_mk', hcard] at hd

end T123Base

end CFSG.RankThree.PartOne.Q1327C
