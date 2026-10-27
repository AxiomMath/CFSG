module

public import CFSG.RankThree.PartOne.KF.F128Lie
public import CFSG.RankThree.PartOne.K1214.SylowShape

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG.RankThree.PartOne.Sec66T CFSG.RankThree.PartOne.FieldFix
open CFSG.RankThree.PartOne.K1214 (SylowShape)

variable {G : Type} [Group G]

theorem card_le_of_fixedFacts [Finite G] {p e : ℕ} (hp : p.Prime) {J : Subgroup G}
    (hZ : ¬ p ∣ Nat.card (Subgroup.center J)) {a : G} (hu : a ∈ Subgroup.normalizer (J : Set G))
    (hF : FixedFacts p (centerQuotientConj J ⟨a, hu⟩))
    (hN : SylowShape p 2 e ↥(fixRes (centerQuotientConj J ⟨a, hu⟩))) {S : Subgroup G}
    (hSp : IsPGroup p ↥S) (hSJ : S ≤ J) (hcent : ∀ s ∈ S, a * s * a⁻¹ = s) :
    Nat.card ↥S ≤ p ^ (2 * e) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  set α : MulAut (↥J ⧸ Subgroup.center ↥J) := centerQuotientConj J ⟨a, hu⟩ with hα
  set πJ : ↥J →* ↥J ⧸ Subgroup.center ↥J := QuotientGroup.mk' (Subgroup.center ↥J) with hπ
  set S₀ : Subgroup ↥J := S.subgroupOf J with hS₀
  set Sbar : Subgroup (↥J ⧸ Subgroup.center ↥J) := S₀.map πJ with hSbar
  have hS₀p : IsPGroup p S₀ := hSp.comap_subtype
  have hinj : ∀ x ∈ S₀, ∀ y ∈ S₀, πJ x = πJ y → x = y := by
    intro x hx y hy hxy
    have hz : x⁻¹ * y ∈ Subgroup.center ↥J := QuotientGroup.eq.mp hxy
    have hxy' : x⁻¹ * y ∈ S₀ := S₀.mul_mem (S₀.inv_mem hx) hy
    obtain ⟨k, hk⟩ := hS₀p ⟨x⁻¹ * y, hxy'⟩
    have hk' : (x⁻¹ * y) ^ (p ^ k) = 1 := congrArg Subtype.val hk
    have hdvd : orderOf (⟨x⁻¹ * y, hz⟩ : Subgroup.center ↥J) ∣
        Nat.card (Subgroup.center ↥J) := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at hdvd
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).mp (orderOf_dvd_of_pow_eq_one hk')
    by_cases hj0 : j = 0
    · rw [hj0, pow_zero] at hj
      exact inv_mul_eq_one.mp (orderOf_eq_one_iff.mp hj)
    · exfalso
      apply hZ
      rw [hj] at hdvd
      exact (dvd_pow_self p hj0).trans hdvd
  have hSbarcard : Nat.card Sbar = Nat.card S := by
    rw [hSbar, card_map_eq_of_injOn πJ S₀ hinj]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSJ).toEquiv
  have hSbarp : IsPGroup p Sbar := hS₀p.map πJ
  have hSbarfix : Sbar ≤ fixSub α := by
    rintro _ ⟨x, hx, rfl⟩
    show α (πJ x) = πJ x
    have hxS : (x : G) ∈ S := Subgroup.mem_subgroupOf.mp hx
    have h1 : α (πJ x) = πJ ⟨a * (x : G) * a⁻¹,
        (Subgroup.mem_normalizer_iff.mp hu (x : G)).mp x.2⟩ := rfl
    rw [h1]
    congr 1
    exact Subtype.ext (hcent x hxS)
  have hSbarN : Sbar ≤ fixRes α := by
    intro x hx
    refine hF.pElements x (hSbarfix hx) ?_
    obtain ⟨k, hk⟩ := hSbarp ⟨x, hx⟩
    have h1 : x ^ (p ^ k) = 1 := congrArg Subtype.val hk
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).mp (orderOf_dvd_of_pow_eq_one h1)
    exact ⟨j, hj⟩
  set N : Subgroup (↥J ⧸ Subgroup.center ↥J) := fixRes α with hNdef
  set Sb : Subgroup ↥N := Sbar.subgroupOf N with hSb
  have hSbp : IsPGroup p Sb := hSbarp.comap_subtype
  have hSbcard : Nat.card Sb = Nat.card Sbar :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSbarN).toEquiv
  obtain ⟨Q, hQ⟩ := hSbp.exists_le_sylow
  obtain ⟨φ⟩ := hN (Q : Subgroup ↥N) Q.isPGroup' Q.not_dvd_index
  have hQcard : Nat.card (Q : Subgroup ↥N) = p ^ (2 * e) := by
    rw [Nat.card_congr φ.toEquiv, Nat.card_pi, Nat.card_eq_fintype_card]
    simp [Finset.prod_const, ZMod.card, ← pow_mul, mul_comm]
  calc Nat.card S = Nat.card Sbar := hSbarcard.symm
    _ = Nat.card Sb := hSbcard.symm
    _ ≤ Nat.card (Q : Subgroup ↥N) := Subgroup.card_le_of_le hQ
    _ = p ^ (2 * e) := hQcard

end CFSG.RankThree.PartOne
