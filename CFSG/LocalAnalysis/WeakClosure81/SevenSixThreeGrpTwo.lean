module

public import CFSG.LocalAnalysis.WeakClosure81.SevenSixThreeGrp
public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Subgroup
open scoped commutatorElement Pointwise

variable {G : Type*} [Group G]

private lemma s763H_conj_commutator_self {u x : G} (hu : u * u = 1) :
    u * ⁅x, u⁆ * u⁻¹ = ⁅x, u⁆⁻¹ := by
  have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_left hu
  have hb : ⁅x, u⁆ = x * u * x⁻¹ * u := by
    rw [commutatorElement_def, huinv]
  rw [hb, huinv]
  have hL : u * (x * u * x⁻¹ * u) * u = u * x * u * x⁻¹ := by
    calc u * (x * u * x⁻¹ * u) * u = u * x * u * x⁻¹ * (u * u) := by group
      _ = u * x * u * x⁻¹ := by rw [hu, mul_one]
  have hR : (x * u * x⁻¹ * u)⁻¹ = u * x * u * x⁻¹ := by
    rw [show (x * u * x⁻¹ * u)⁻¹ = u⁻¹ * x * u⁻¹ * x⁻¹ by group]
    rw [huinv]
  rw [hL, hR]

private lemma s763H_conj_eq_inv_commutator_mul (c u : G) :
    u * c * u⁻¹ = ⁅c, u⁆⁻¹ * c := by
  rw [commutatorElement_def]
  group

theorem PInvol.exists_not_central_commutator {p : ℕ} {Q : Subgroup G} {u : G} (h : PInvol p Q u)
    (hQ : ∃ x ∈ Q, ∃ y ∈ Q, ⁅x, y⁆ ≠ 1) : ∃ x ∈ Q, ∃ y ∈ Q, ⁅⁅x, u⁆, y⁆ ≠ 1 := by
  by_contra hcon
  push Not at hcon
  have hle : ⁅Q, Subgroup.zpowers u⁆ ≤ Subgroup.centralizer (Q : Set G) := by
    rw [Subgroup.commutator_le]
    intro x hx v hv
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
    have hu2 : u ^ (2 : ℕ) = 1 := by rw [pow_two]; exact h.sq_eq_one
    have hk : u ^ k = u ^ (k % 2) := zpow_eq_zpow_emod' k hu2
    rcases Int.emod_two_eq_zero_or_one k with hk0 | hk1
    · rw [hk, hk0]; simp [commutatorElement_def]
    · rw [hk, hk1, zpow_one]
      exact (commutatorElement_eq_one_iff_mul_comm.mp (hcon x hx y hy)).symm
  have hQle : Q ≤ Subgroup.centralizer (Q : Set G) := h.le_commutator.trans hle
  obtain ⟨x, hx, y, hy, hxy⟩ := hQ
  exact hxy (commutatorElement_eq_one_iff_mul_comm.mpr
    ((Subgroup.mem_centralizer_iff.mp (hQle hx)) y hy).symm)

theorem relIndex_centralizer_le_card_commutator [Finite G] {Q : Subgroup G} {a : G}
    (ha : a ∈ Q) :
    (Subgroup.centralizer {a}).relIndex Q ≤ Nat.card (⁅Q, Q⁆ : Subgroup G) := by
  let C : Subgroup G := Subgroup.centralizer {a}
  let C' : Subgroup ↥Q := C.subgroupOf Q
  change C.relIndex Q ≤ Nat.card (⁅Q, Q⁆ : Subgroup G)
  have hcard : C.relIndex Q = Nat.card (↥Q ⧸ C') := by
    rw [Subgroup.relIndex, Subgroup.index_eq_card]
  let f : (↥Q ⧸ C') → ↥(⁅Q, Q⁆ : Subgroup G) :=
    Quotient.lift (fun x : ↥Q => ⟨⁅(x : G), a⁆, Subgroup.commutator_mem_commutator x.2 ha⟩)
      (fun x y hxy => by
        apply Subtype.ext
        change ⁅(x : G), a⁆ = ⁅(y : G), a⁆
        have hmem : x⁻¹ * y ∈ C' := QuotientGroup.leftRel_apply.mp hxy
        have hcomm : ((x⁻¹ * y : ↥Q) : G) * a = a * ((x⁻¹ * y : ↥Q) : G) :=
          Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_subgroupOf.mp hmem)
        have hcomm' : (x : G)⁻¹ * (y : G) * a = a * ((x : G)⁻¹ * (y : G)) := by
          simpa using hcomm
        have key : (x : G) * a * (x : G)⁻¹ = (y : G) * a * (y : G)⁻¹ := by
          have h1 : (y : G) * a = (x : G) * a * (x : G)⁻¹ * (y : G) := by
            calc (y : G) * a = (x : G) * ((x : G)⁻¹ * (y : G)) * a := by group
              _ = (x : G) * (((x : G)⁻¹ * (y : G)) * a) := by group
              _ = (x : G) * (a * ((x : G)⁻¹ * (y : G))) := by rw [hcomm']
              _ = (x : G) * a * (x : G)⁻¹ * (y : G) := by group
          rw [h1]
          group
        rw [commutatorElement_def, commutatorElement_def, key])
  have hf : Function.Injective f := by
    intro q1 q2 hq
    revert hq
    refine Quotient.inductionOn q1 ?_
    intro x
    refine Quotient.inductionOn q2 ?_
    intro y hq
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf,
      Subgroup.mem_centralizer_singleton_iff]
    have hxy : ⁅(x : G), a⁆ = ⁅(y : G), a⁆ := congrArg Subtype.val hq
    have key : (x : G) * a * (x : G)⁻¹ = (y : G) * a * (y : G)⁻¹ := by
      have h2 : (x : G) * a * (x : G)⁻¹ * a⁻¹ = (y : G) * a * (y : G)⁻¹ * a⁻¹ := by
        simpa [commutatorElement_def] using hxy
      calc (x : G) * a * (x : G)⁻¹ = (x : G) * a * (x : G)⁻¹ * a⁻¹ * a := by group
        _ = (y : G) * a * (y : G)⁻¹ * a⁻¹ * a := by rw [h2]
        _ = (y : G) * a * (y : G)⁻¹ := by group
    have hcomm : (x : G)⁻¹ * (y : G) * a = a * ((x : G)⁻¹ * (y : G)) := by
      calc (x : G)⁻¹ * (y : G) * a
          = (x : G)⁻¹ * ((y : G) * a * (y : G)⁻¹) * (y : G) := by group
        _ = (x : G)⁻¹ * ((x : G) * a * (x : G)⁻¹) * (y : G) := by rw [key]
        _ = a * ((x : G)⁻¹ * (y : G)) := by group
    simpa using hcomm
  rw [hcard]
  exact Nat.card_le_card_of_injective f hf

theorem card_sup_le_of_commute [Finite G] {H K : Subgroup G}
    (hHK : ∀ x ∈ H, ∀ y ∈ K, x * y = y * x) :
    Nat.card (H ⊔ K : Subgroup G) ≤ Nat.card H * Nat.card K := by
  have hle : H ≤ Subgroup.normalizer (K : Set G) := by
    refine (show H ≤ Subgroup.centralizer (K : Set G) from ?_).trans
      (Subgroup.centralizer_le_normalizer (K : Set G))
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (hHK x hx y hy).symm
  have hcoe : (↑(H ⊔ K) : Set G) = ↑H * ↑K :=
    Subgroup.coe_mul_of_left_le_normalizer_right H K hle
  let f : ↥H × ↥K → ↥(H ⊔ K) :=
    fun p => ⟨(p.1 : G) * (p.2 : G), Subgroup.mul_mem_sup p.1.2 p.2.2⟩
  have hf : Function.Surjective f := by
    intro z
    have hz : (z : G) ∈ (↑H : Set G) * ↑K := by
      rw [← hcoe]; exact z.2
    rw [Set.mem_mul] at hz
    obtain ⟨x, hx, y, hy, hxy⟩ := hz
    exact ⟨(⟨x, hx⟩, ⟨y, hy⟩), Subtype.ext hxy⟩
  have h := Nat.card_le_card_of_surjective f hf
  rwa [Nat.card_prod] at h

theorem PInvol.inf_centralizer_le_sup_zpowers [Finite G] {p : ℕ} {Q : Subgroup G} {u : G}
    (h : PInvol p Q u) (h1 : InvertedSmall p Q u) {a : G} (haQ : a ∈ Q) (ha1 : a ≠ 1)
    (hua : u * a * u⁻¹ = a⁻¹) :
    Q ⊓ Subgroup.centralizer {a} ≤ ⁅Q, Q⁆ ⊔ Subgroup.zpowers a := by
  haveI : Fact p.Prime := ⟨h.prime⟩
  have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_left h.sq_eq_one
  intro c hc
  rw [Subgroup.mem_inf] at hc
  obtain ⟨hcQ, hcC⟩ := hc
  rw [Subgroup.mem_centralizer_singleton_iff] at hcC
  let b : G := ⁅c, u⁆
  have hb_eq : b = c * (u * c⁻¹ * u⁻¹) := by
    rw [show b = ⁅c, u⁆ from rfl, commutatorElement_def]; group
  have hbQ : b ∈ Q := by
    have hux : u * c⁻¹ * u⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.mp h.mem_normalizer (c⁻¹)).mp (Q.inv_mem hcQ)
    rw [hb_eq]
    exact Q.mul_mem hcQ hux
  have hbInv : u * b * u⁻¹ = b⁻¹ := s763H_conj_commutator_self h.sq_eq_one
  have hbComm : b * a = a * b := by
    have hua' : u * a * u = a⁻¹ := by simpa [huinv] using hua
    have h_ua : u * a = a⁻¹ * u := by
      calc u * a = u * a * (u * u) := by rw [h.sq_eq_one, mul_one]
        _ = (u * a * u) * u := by group
        _ = a⁻¹ * u := by rw [hua']
    have h_uainv : u * a⁻¹ = a * u := by
      have h2 : u * a⁻¹ * u = a := by
        have h3 : u * (a⁻¹ * u) = a := by
          have h4 : (u * a * u)⁻¹ = a := by rw [hua', inv_inv]
          simpa [mul_inv_rev, huinv] using h4
        rw [mul_assoc]
        exact h3
      calc u * a⁻¹ = u * a⁻¹ * (u * u) := by rw [h.sq_eq_one, mul_one]
        _ = (u * a⁻¹ * u) * u := by group
        _ = a * u := by rw [h2]
    have hca_inv : c⁻¹ * a⁻¹ = a⁻¹ * c⁻¹ := by
      have := congrArg Inv.inv hcC
      simpa [mul_inv_rev] using this.symm
    have huca : Commute (u * c⁻¹ * u⁻¹) a := by
      rw [huinv]
      calc (u * c⁻¹ * u) * a = u * c⁻¹ * (u * a) := by group
        _ = u * c⁻¹ * (a⁻¹ * u) := by rw [h_ua]
        _ = u * (c⁻¹ * (a⁻¹ * u)) := by group
        _ = u * ((c⁻¹ * a⁻¹) * u) := by group
        _ = u * ((a⁻¹ * c⁻¹) * u) := by rw [hca_inv]
        _ = u * (a⁻¹ * (c⁻¹ * u)) := by group
        _ = (u * a⁻¹) * (c⁻¹ * u) := by group
        _ = (a * u) * (c⁻¹ * u) := by rw [h_uainv]
        _ = a * (u * c⁻¹ * u) := by group
    rw [hb_eq]
    calc c * (u * c⁻¹ * u⁻¹) * a = c * ((u * c⁻¹ * u⁻¹) * a) := by group
      _ = c * (a * (u * c⁻¹ * u⁻¹)) := by rw [huca]
      _ = a * (c * (u * c⁻¹ * u⁻¹)) := by rw [← mul_assoc, hcC, mul_assoc]
  let S : Subgroup G := Subgroup.closure ({a, b} : Set G)
  have hpair : ({a, b} : Set G).Pairwise Commute := by
    intro x hx y hy hxy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact absurd rfl hxy
    · exact hbComm.symm
    · exact hbComm
    · exact absurd rfl hxy
  haveI : IsMulCommutative ↥S := isMulCommutative_closure hpair
  have haS : a ∈ S := Subgroup.subset_closure (by simp)
  have hbS : b ∈ S := Subgroup.subset_closure (by simp)
  have hSQ : S ≤ Q := Subgroup.closure_le Q |>.mpr (by
    intro x hx
    rcases hx with rfl | rfl
    · exact haQ
    · exact hbQ)
  have hSinv : ∀ s ∈ S, u * s * u⁻¹ = s⁻¹ := by
    intro s hs
    induction hs using Subgroup.closure_induction with
    | mem x hx =>
        rcases hx with rfl | rfl
        · exact hua
        · exact hbInv
    | one => group
    | mul x y hx hy ihx ihy =>
        calc u * (x * y) * u⁻¹ = (u * x * u⁻¹) * (u * y * u⁻¹) := by group
          _ = x⁻¹ * y⁻¹ := by rw [ihx, ihy]
          _ = (y * x)⁻¹ := by rw [← mul_inv_rev y x]
          _ = (x * y)⁻¹ := by rw [setLike_mul_comm hx hy]
    | inv x hx ih =>
        rw [inv_inv]
        calc u * x⁻¹ * u⁻¹ = (u * x * u⁻¹)⁻¹ := by group
          _ = (x⁻¹)⁻¹ := by rw [ih]
          _ = x := by rw [inv_inv]
  have hScard : Nat.card S ≤ p := h1 S hSQ hSinv
  have ha_order : orderOf a = p := orderOf_eq_prime (h.exp a haQ) ha1
  have hcard_a : Nat.card (Subgroup.zpowers a) = p := by rw [Nat.card_zpowers, ha_order]
  have hza_le : Subgroup.zpowers a ≤ S := Subgroup.zpowers_le.mpr haS
  have hzeq : Subgroup.zpowers a = S :=
    Subgroup.eq_of_le_of_card_ge hza_le (by rw [hcard_a]; exact hScard)
  have hb_zp : b ∈ Subgroup.zpowers a := by rw [hzeq]; exact hbS
  obtain ⟨k, hbk⟩ := Subgroup.mem_zpowers_iff.mp hb_zp
  obtain ⟨m, hm⟩ := h.prime.odd_of_ne_two h.odd
  let j : ℤ := (m : ℤ) * k
  have hmp : (p : ℤ) = 2 * (m : ℤ) + 1 := by omega
  have hjk : 2 * j + k = (p : ℤ) * k := by
    rw [show j = (m : ℤ) * k from rfl, hmp]; ring
  have h2jk : a ^ (2 * j) * b = 1 := by
    rw [← hbk, ← zpow_add, hjk, zpow_mul, zpow_natCast, h.exp a haQ, one_zpow]
  have hb_inv : b⁻¹ = a ^ (2 * j) := (eq_inv_of_mul_eq_one_left h2jk).symm
  have hua_zpow : u * a ^ j * u⁻¹ = a ^ (-j) := by
    rw [← MulAut.conj_apply u (a ^ j), map_zpow, MulAut.conj_apply u a, hua, inv_zpow,
      ← zpow_neg]
  have hca : Commute c a := hcC
  have hca_negj : Commute c (a ^ (-j)) := hca.zpow_right (-j)
  have hca_j' : Commute (a ^ j) c := (hca.zpow_right j).symm
  have h2j : 2 * j + (-j) = j := by ring
  have hconj : u * (c * a ^ j) * u⁻¹ = c * a ^ j := by
    calc u * (c * a ^ j) * u⁻¹ = (u * c * u⁻¹) * (u * a ^ j * u⁻¹) := by group
      _ = (b⁻¹ * c) * a ^ (-j) := by
        rw [s763H_conj_eq_inv_commutator_mul c u, hua_zpow]
      _ = (a ^ (2 * j) * c) * a ^ (-j) := by rw [hb_inv]
      _ = a ^ (2 * j) * (c * a ^ (-j)) := by group
      _ = a ^ (2 * j) * (a ^ (-j) * c) := by rw [hca_negj]
      _ = (a ^ (2 * j) * a ^ (-j)) * c := by group
      _ = a ^ j * c := by rw [← zpow_add, h2j]
      _ = c * a ^ j := by rw [hca_j']
  have hdu : u * (c * a ^ j) = (c * a ^ j) * u := by
    calc u * (c * a ^ j) = (u * (c * a ^ j) * u⁻¹) * u := by group
      _ = (c * a ^ j) * u := by rw [hconj]
  have hdQ : c * a ^ j ∈ Q := Q.mul_mem hcQ (Subgroup.zpow_mem Q haQ j)
  have hdD : c * a ^ j ∈ ⁅Q, Q⁆ := h.mem_commutator_of_commute hdQ hdu
  have hc_eq : c = (c * a ^ j) * (a ^ j)⁻¹ := by group
  rw [hc_eq]
  exact Subgroup.mul_mem_sup hdD (Subgroup.inv_mem _
    (Subgroup.zpow_mem (Subgroup.zpowers a) (Subgroup.mem_zpowers a) j))

theorem PInvol.card_le_of_not_commutative [Finite G] {p : ℕ} {Q : Subgroup G} {u : G}
    (h : PInvol p Q u) (hQ : ∃ x ∈ Q, ∃ y ∈ Q, ⁅x, y⁆ ≠ 1) (h1 : InvertedSmall p Q u)
    (h2 : CentralSmall p Q u) : Nat.card Q ≤ p ^ 3 := by
  haveI : Fact p.Prime := ⟨h.prime⟩
  have hDle : ⁅Q, Q⁆ ≤ Subgroup.centralizer (Q : Set G) := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact (commutatorElement_eq_one_iff_mul_comm.mp (h.class_two x hx y hy z hz)).symm
  have hDcent : ∀ s ∈ ⁅Q, Q⁆, ∀ x ∈ Q, s * x = x * s := by
    intro s hs x hx
    exact ((Subgroup.mem_centralizer_iff.mp (hDle hs)) x hx).symm
  have hDu : ∀ s ∈ ⁅Q, Q⁆, u * s = s * u := fun s hs => h.commute_of_mem_commutator hs
  have hDcard : Nat.card (⁅Q, Q⁆ : Subgroup G) ≤ p :=
    h2 ⁅Q, Q⁆ (Subgroup.commutator_le_self Q) hDcent hDu
  obtain ⟨x, hx, y, hy, hxy⟩ := h.exists_not_central_commutator hQ
  let a : G := ⁅x, u⁆
  have haQ : a ∈ Q := by
    have hux : u * x⁻¹ * u⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.mp h.mem_normalizer (x⁻¹)).mp (Q.inv_mem hx)
    have ha : a = x * (u * x⁻¹ * u⁻¹) := by
      rw [show a = ⁅x, u⁆ from rfl, commutatorElement_def]; group
    rw [ha]
    exact Q.mul_mem hx hux
  have ha1 : a ≠ 1 := by
    intro h1a
    refine hxy ?_
    change ⁅a, y⁆ = 1
    rw [h1a]
    simp [commutatorElement_def]
  have hua : u * a * u⁻¹ = a⁻¹ := s763H_conj_commutator_self h.sq_eq_one
  have hcard_a_le : Nat.card (Subgroup.zpowers a) ≤ p := by
    rw [Nat.card_zpowers]
    exact Nat.le_of_dvd h.prime.pos (orderOf_dvd_of_pow_eq_one (h.exp a haQ))
  let C : Subgroup G := Subgroup.centralizer {a}
  have hrel : C.relIndex Q ≤ Nat.card (⁅Q, Q⁆ : Subgroup G) :=
    relIndex_centralizer_le_card_commutator haQ
  have hrel' : C.relIndex Q ≤ p := hrel.trans hDcard
  have hinf : C ⊓ Q ≤ ⁅Q, Q⁆ ⊔ Subgroup.zpowers a := by
    rw [inf_comm]
    exact h.inf_centralizer_le_sup_zpowers h1 haQ ha1 hua
  have hcard_inf : Nat.card (C ⊓ Q : Subgroup G) ≤ p * p := by
    have h1' : Nat.card (C ⊓ Q : Subgroup G) ≤
        Nat.card (⁅Q, Q⁆ ⊔ Subgroup.zpowers a : Subgroup G) :=
      Subgroup.card_le_of_le hinf
    have h2' : Nat.card (⁅Q, Q⁆ ⊔ Subgroup.zpowers a : Subgroup G) ≤
        Nat.card (⁅Q, Q⁆ : Subgroup G) * Nat.card (Subgroup.zpowers a) := by
      refine card_sup_le_of_commute ?_
      intro s hs t ht
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ht
      exact hDcent s hs (a ^ i) (Subgroup.zpow_mem Q haQ i)
    calc Nat.card (C ⊓ Q : Subgroup G) ≤
          Nat.card (⁅Q, Q⁆ ⊔ Subgroup.zpowers a : Subgroup G) := h1'
      _ ≤ Nat.card (⁅Q, Q⁆ : Subgroup G) * Nat.card (Subgroup.zpowers a) := h2'
      _ ≤ p * p := Nat.mul_le_mul hDcard hcard_a_le
  have hmain : Nat.card Q = C.relIndex Q * Nat.card (C ⊓ Q : Subgroup G) :=
    (Subgroup.relIndex_mul_card C Q).symm
  calc Nat.card Q = C.relIndex Q * Nat.card (C ⊓ Q : Subgroup G) := hmain
    _ ≤ p * (p * p) := Nat.mul_le_mul hrel' hcard_inf
    _ = p ^ 3 := by ring

theorem PInvol.card_main [Finite G] {p : ℕ} {Q : Subgroup G} {u : G} (h : PInvol p Q u)
    (hQ : Q ≠ ⊥) (h1 : InvertedSmall p Q u) (h2 : CentralSmall p Q u) :
    Nat.card Q = p ∨ (Nat.card Q = p ^ 3 ∧ ∃ x ∈ Q, ∃ y ∈ Q, ⁅x, y⁆ ≠ 1) := by
  haveI : Fact p.Prime := ⟨h.prime⟩
  have hpg : IsPGroup p ↥Q := by
    intro g
    refine ⟨1, ?_⟩
    rw [pow_one]
    exact Subtype.ext (h.exp (g : G) g.2)
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hpg
  by_cases hcomm : ∀ x ∈ Q, ∀ y ∈ Q, ⁅x, y⁆ = 1
  · left
    have hcard_le : Nat.card Q ≤ p := PInvol.card_le_of_commutative h hcomm h1
    rw [hn] at hcard_le
    have hn0 : n ≠ 0 := by
      intro hn0
      rw [hn0, pow_zero] at hn
      exact hQ (Subgroup.card_eq_one.mp hn)
    have hn_le : n ≤ 1 := by
      have h' : p ^ n ≤ p ^ 1 := by simpa using hcard_le
      exact (Nat.pow_le_pow_iff_right h.prime.one_lt).mp h'
    have hn1 : n = 1 := by omega
    rw [hn, hn1, pow_one]
  · right
    have hnot : ¬ (∀ x ∈ Q, ∀ y ∈ Q, ⁅x, y⁆ = 1) := hcomm
    push Not at hcomm
    have hcard_le : Nat.card Q ≤ p ^ 3 :=
      PInvol.card_le_of_not_commutative h hcomm h1 h2
    rw [hn] at hcard_le
    have hn_le : n ≤ 3 := by
      have h' : p ^ n ≤ p ^ 3 := hcard_le
      exact (Nat.pow_le_pow_iff_right h.prime.one_lt).mp h'
    have hn0 : n ≠ 0 := by
      intro hn0
      rw [hn0, pow_zero] at hn
      exact hQ (Subgroup.card_eq_one.mp hn)
    have hn1 : n ≠ 1 := by
      intro hn1
      haveI : IsCyclic ↥Q := isCyclic_of_prime_card (p := p) (by rw [hn, hn1, pow_one])
      exact hnot (fun x hx y hy => by
        rw [commutatorElement_eq_one_iff_mul_comm]
        simpa using congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : ↥Q) ⟨y, hy⟩))
    have hn2 : n ≠ 2 := by
      intro hn2
      haveI : IsMulCommutative ↥Q :=
        IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := p) (by rw [hn, hn2])
      exact hnot (fun x hx y hy => by
        rw [commutatorElement_eq_one_iff_mul_comm]
        simpa using congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : ↥Q) ⟨y, hy⟩))
    have hn3 : n = 3 := by omega
    exact ⟨by rw [hn, hn3], hcomm⟩

end CFSG.LocalAnalysis.WeakClosure81
