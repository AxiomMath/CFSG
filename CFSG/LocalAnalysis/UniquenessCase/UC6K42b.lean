module

public import CFSG.LocalAnalysis.UniquenessCase.UC6K42a

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6

open Subgroup CFSG.Open
open CFSG.LocalAnalysis.UniquenessCase.UCK (fixV)
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {p : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod p) V]

theorem false_of_r_two_uc6 (ρ : Representation (ZMod p) G V) (hρ : Function.Injective ρ)
    (D : Subgroup G) (hD : Nat.card D = 2) (hfix : fixV ρ D = ⊥) (Q : Subgroup G)
    (hQne : Q ≠ ⊥) (hcomm : ⁅D, Q⁆ = Q) : False := by
  obtain ⟨x, hxD, hxord⟩ := exists_generator_uc6 Nat.prime_two hD
  have hx2 : x * x = 1 := by rw [← pow_two]; exact hxord ▸ pow_orderOf_eq_one x
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
  have hρx2 : ρ x * ρ x = 1 := by rw [← map_mul, hx2, map_one]
  have hneg : ∀ v : V, ρ x v = -v := by
    intro v
    have hu : (v + ρ x v) ∈ fixV ρ D := by
      rw [hxD, mem_fixV_zpowers_uc6]
      have := congrArg (fun f : Module.End (ZMod p) V => f v) hρx2
      simp only [Module.End.mul_apply, Module.End.one_apply] at this
      rw [map_add, this, add_comm]
    rw [hfix] at hu
    exact eq_neg_of_add_eq_zero_right ((Submodule.mem_bot _).1 hu)
  have hcent : ∀ y : G, x * y * x⁻¹ = y := by
    intro y
    apply hρ
    rw [map_mul, map_mul, hxinv]
    apply LinearMap.ext
    intro w
    simp only [Module.End.mul_apply, hneg, map_neg, neg_neg]
  have hbot : ⁅D, Q⁆ ≤ ⊥ := by
    rw [Subgroup.commutator_le]
    intro g₁ hg₁ g₂ _
    rw [Subgroup.mem_bot]
    rw [hxD] at hg₁
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg₁
    have hc : Commute x g₂ := mul_inv_eq_iff_eq_mul.1 (hcent g₂)
    exact commutatorElement_eq_one_iff_mul_comm.2 (Commute.zpow_left hc n).eq
  exact hQne (le_bot_iff.1 (hcomm ▸ hbot))

theorem false_of_odd_uc6 [Fact p.Prime] (ρ : Representation (ZMod p) G V)
    (hρ : Function.Injective ρ) {q r : ℕ} (hq : q.Prime) (hr : r.Prime) (hpq : q ≠ p)
    (hpr : r ≠ p) (hqr : q ≠ r) (hq2 : q ≠ 2) (hr2 : r ≠ 2) (D : Subgroup G)
    (hD : Nat.card D = r) (hfix : fixV ρ D = ⊥) (Q : Subgroup G) (hQp : IsPGroup q Q)
    (hQne : Q ≠ ⊥) (hDQ : D ≤ normalizer (Q : Set G)) (hcomm : ⁅D, Q⁆ = Q) : False := by
  haveI : Fact q.Prime := ⟨hq⟩
  let H : Subgroup G := Q ⊔ D
  have hQH : Q ≤ H := le_sup_left
  have hDH : D ≤ H := le_sup_right
  have hHN : H ≤ normalizer (Q : Set G) := sup_le Subgroup.le_normalizer hDQ
  let K : Subgroup ↥H := Q.subgroupOf H
  let R : Subgroup ↥H := D.subgroupOf H
  have hKnormal : K.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hQH).2 hHN
  let eK : ↥K ≃* ↥Q := Subgroup.subgroupOfEquivOfLe hQH
  let eR : ↥R ≃* ↥D := Subgroup.subgroupOfEquivOfLe hDH
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hQp
  have hKcard : Nat.card K = q ^ n := (Nat.card_congr eK.toEquiv).trans hn
  have hRcard : Nat.card R = r := (Nat.card_congr eR.toEquiv).trans hD
  have hcop : Nat.Coprime (q ^ n) r :=
    Nat.Coprime.pow_left n ((Nat.coprime_primes hq hr).2 hqr)
  have hdisj : Disjoint K R := by
    rw [Subgroup.disjoint_def]
    intro y hyK hyR
    have h1 : orderOf y ∣ q ^ n := by
      have := orderOf_dvd_natCard (⟨y, hyK⟩ : ↥K)
      rwa [Subgroup.orderOf_mk, hKcard] at this
    have h2 : orderOf y ∣ r := by
      have := orderOf_dvd_natCard (⟨y, hyR⟩ : ↥R)
      rwa [Subgroup.orderOf_mk, hRcard] at this
    exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hcop h1 h2)
  have hsupK : K ⊔ R = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hQH hDH]
    exact Subgroup.subgroupOf_self (Q ⊔ D)
  have hmul : (K : Set ↥H) * (R : Set ↥H) = Set.univ := by
    rw [← Subgroup.normal_mul K R, hsupK]
    rfl
  have hKR : K.IsComplement' R := Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisj hmul
  have hcardH : Nat.card ↥H = q ^ n * r := by
    rw [← hKR.card_mul, hKcard, hRcard]
  have hsolv : Group.IsSolvable ↥H := by
    haveI : Fact (IsPGroup q ↥K) := ⟨hQp.of_injective eK.toMonoidHom eK.injective⟩
    haveI : Group.IsNilpotent ↥K := IsPGroup.isNilpotent (Fact.out : IsPGroup q ↥K)
    haveI : Group.IsSolvable ↥K := inferInstance
    have hqcard : Nat.card (↥H ⧸ K) = r := by
      have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (s := K)
      rw [hcardH, hKcard] at h1
      exact Nat.eq_of_mul_eq_mul_left (pow_pos hq.pos n) (by rw [h1, mul_comm])
    haveI : Fact r.Prime := ⟨hr⟩
    haveI : IsCyclic (↥H ⧸ K) := isCyclic_of_prime_card hqcard
    haveI : Group.IsSolvable (↥H ⧸ K) := inferInstance
    exact Group.isSolvable_of_ker_le_range K.subtype (QuotientGroup.mk' K)
      (by rw [QuotientGroup.ker_mk', K.range_subtype])
  have hodd : Odd (Nat.card ↥H) := by
    rw [hcardH]
    exact ((hq.odd_of_ne_two hq2).pow).mul (hr.odd_of_ne_two hr2)
  have hchar : ringChar (ZMod p) = 0 ∨
      (Nat.Prime (ringChar (ZMod p)) ∧ Nat.Coprime (ringChar (ZMod p)) (Nat.card ↥H)) := by
    right
    rw [ZMod.ringChar_zmod_n, hcardH]
    refine ⟨Fact.out, Nat.Coprime.mul_right ?_ ?_⟩
    · exact Nat.Coprime.pow_right n ((Nat.coprime_primes Fact.out hq).2 hpq.symm)
    · exact (Nat.coprime_primes Fact.out hr).2 hpr.symm
  let ρH : Representation (ZMod p) ↥H V := ρ.comp H.subtype
  have hfixR : ρH.fixedSubspace R = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    have hv' : ∀ g : ↥R, ρ (((g : ↥H)) : G) v = v := by
      intro g
      have := (Representation.mem_invariants (ρH.comp R.subtype) v).1 hv g
      simpa [ρH] using this
    have : v ∈ fixV ρ D := fun d hd => hv' ⟨⟨d, hDH hd⟩, hd⟩
    rw [hfix] at this
    exact this
  have hmain := theorem_3_4 K R ρH hsolv hodd hKnormal hKR (by rw [hKcard, hRcard]; exact hcop)
    (by rw [hRcard]; exact hr) hchar hfixR
  apply hQne
  rw [eq_bot_iff]
  intro y hy
  rw [Subgroup.mem_bot]
  have hy' : y ∈ (⁅R, K⁆).map H.subtype := by
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hDH,
      Subgroup.map_subgroupOf_eq_of_le hQH, hcomm]
    exact hy
  obtain ⟨z, hz, hzy⟩ := hy'
  have hzker := (hmain hz).2
  apply hρ
  rw [map_one]
  have h1 : ρH z = 1 := hzker
  have h2 : ρH z = ρ y := by
    show ρ (H.subtype z) = ρ y
    rw [hzy]
  rw [← h2, h1]

theorem q_eq_two_uc6 [Fact p.Prime] (ρ : Representation (ZMod p) G V)
    (hρ : Function.Injective ρ) {q r : ℕ} (hq : q.Prime) (hr : r.Prime) (hpq : q ≠ p)
    (hpr : r ≠ p) (hqr : q ≠ r) (D : Subgroup G) (hD : Nat.card D = r) (hfix : fixV ρ D = ⊥)
    (Q : Subgroup G) (hQp : IsPGroup q Q) (hQne : Q ≠ ⊥) (hDQ : D ≤ normalizer (Q : Set G))
    (hcomm : ⁅D, Q⁆ = Q) : q = 2 := by
  by_contra hq2
  by_cases hr2 : r = 2
  · subst hr2
    exact false_of_r_two_uc6 ρ hρ D hD hfix Q hQne hcomm
  · exact false_of_odd_uc6 ρ hρ hq hr hpq hpr hqr hq2 hr2 D hD hfix Q hQp hQne hDQ hcomm

end CFSG.LocalAnalysis.UniquenessCase.UC6
