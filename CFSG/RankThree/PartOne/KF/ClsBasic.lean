module

public import CFSG.RankThree.PartOne.S12.InputsTable
public import CFSG.RankThree.PartTwo.Census.Classical.EvenWitness
public import CFSG.RankThree.Classical2.TwoLocalRankCoprimeQuotient
public import CFSG.RankThree.PartOne.S9.Planes.Basic

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven

variable {G : Type} [Group G] [Finite G]

theorem exists_elemAbelian_of_le_localRank {X : Type*} [Group X] [Finite X] {p : ℕ}
    (hp : p.Prime) {k : ℕ} (hk : 1 ≤ k) (hle : k ≤ localRank p X) :
    ∃ U : Subgroup X, IsPGroup 2 U ∧ U ≠ ⊥ ∧ ∃ E : Subgroup X,
      E ≤ Subgroup.normalizer (U : Set X) ∧ IsElementaryAbelian p E ∧ Nat.card E = p ^ k := by
  by_contra hno
  push Not at hno
  have hlt : localRank p X ≤ k - 1 := by
    refine csSup_le' ?_
    rintro m ⟨H', ⟨S, hS0, hS2, rfl⟩, rfl⟩
    by_contra hm
    push Not at hm
    obtain ⟨E, hEN, hE, hEc⟩ := (CFSG.RankThree.PartOne.Planes.le_pRank_iff hp
      (Subgroup.normalizer (S : Set X)) k).1 (by omega)
    exact hno S hS2 hS0 E hEN hE hEc
  omega

namespace Table123Generic

variable {p : ℕ} {L A₀ F : Subgroup G} (h : Table123Generic p L A₀ F)

include h in
theorem coprime_center : Nat.Coprime p (Nat.card (Subgroup.center ↥L)) :=
  (Nat.Prime.coprime_iff_not_dvd h.prime).mpr h.center_pPrime

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
    rw [h.coprime_center] at h3
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
theorem localRank_quot_le : localRank p (↥L ⧸ Subgroup.center ↥L) ≤ 2 := by
  have := CFSG.RankThree.Classical2.localRank_quotient_le h.prime
    (by have := h.five_le; omega) (Subgroup.center ↥L) h.center_pPrime
  rw [h.localRank_eq] at this
  exact this

include h in
theorem localRank_quot_eq : localRank p (↥L ⧸ Subgroup.center ↥L) = 2 :=
  le_antisymm h.localRank_quot_le h.two_le_localRank_quot

include h in
theorem localRank_eq_two_of_mulEquiv {X : Type} [Group X] [Finite X]
    (e : ↥L ⧸ Subgroup.center ↥L ≃* X) : localRank p X = 2 := by
  rw [← CFSG.RankThree.PartTwo.Census.localRank_eq_of_mulEquiv e h.prime]
  exact h.localRank_quot_eq

end Table123Generic

end CFSG.RankThree.PartOne
