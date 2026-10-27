module

public import CFSG.RankThree.PartTwo.Census.Criteria
public import CFSG.RankThree.PartOne.KP.CentralCoverThree

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census

namespace TripleCoverLift

open CFSG.Assembly CFSG.Assembly.RankThreeEven
open scoped commutatorElement

section Lifts

variable {G X : Type*} [Group G] [Group X] {φ : G →* X}

theorem exists_lift_pow_eq_one_of_conj_eq_inv (hφ : Function.Surjective φ)
    (hker : φ.ker ≤ Subgroup.center G) {p : ℕ} (hp : Odd p) {x n : X} (hx : x ^ p = 1)
    (hn : n * x * n⁻¹ = x⁻¹) : ∃ y : G, φ y = x ∧ y ^ p = 1 := by
  obtain ⟨y₀, rfl⟩ := hφ x
  obtain ⟨m, rfl⟩ := hφ n
  obtain ⟨k, rfl⟩ := hp
  obtain ⟨c, hc⟩ : ∃ c : G, c = y₀ * (m * y₀ * m⁻¹) := ⟨_, rfl⟩
  obtain ⟨w, hw⟩ : ∃ w : G, w = y₀ ^ (2 * k + 1) := ⟨_, rfl⟩
  have hck : c ∈ φ.ker := by
    rw [hc, MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, hn, mul_inv_cancel]
  have hwk : w ∈ φ.ker := by rw [hw, MonoidHom.mem_ker, map_pow, hx]
  have hcZ : c ∈ Subgroup.center G := hker hck
  have hwZ : w ∈ Subgroup.center G := hker hwk
  have h1 : m * y₀ * m⁻¹ = y₀⁻¹ * c := by
    rw [hc, inv_mul_cancel_left]
  have h2 : w = w⁻¹ * c ^ (2 * k + 1) := by
    have hcomm : Commute y₀⁻¹ c := Subgroup.mem_center_iff.mp hcZ y₀⁻¹
    calc w = m * w * m⁻¹ := by
          rw [Subgroup.mem_center_iff.mp hwZ m, mul_inv_cancel_right]
      _ = (m * y₀ * m⁻¹) ^ (2 * k + 1) := by rw [hw, conj_pow]
      _ = w⁻¹ * c ^ (2 * k + 1) := by
          rw [h1, hcomm.mul_pow, inv_pow, hw]
  have h3 : w * w = c ^ (2 * k + 1) :=
    calc w * w = w * (w⁻¹ * c ^ (2 * k + 1)) := by rw [← h2]
      _ = c ^ (2 * k + 1) := mul_inv_cancel_left _ _
  have hzZ : w * (c ^ (k + 1))⁻¹ ∈ Subgroup.center G :=
    Subgroup.mul_mem _ hwZ (Subgroup.inv_mem _ (Subgroup.pow_mem _ hcZ _))
  have hzk : w * (c ^ (k + 1))⁻¹ ∈ φ.ker :=
    φ.ker.mul_mem hwk (φ.ker.inv_mem (φ.ker.pow_mem hck _))
  have h4 : w * (w * (c ^ (k + 1))⁻¹) ^ (2 * k + 1) = 1 := by
    have hwc : Commute w (c ^ (k + 1))⁻¹ := (Subgroup.mem_center_iff.mp hwZ _).symm
    rw [hwc.mul_pow, ← mul_assoc, ← pow_succ', show 2 * k + 1 + 1 = 2 * (k + 1) by ring,
      pow_mul, pow_two, h3, inv_pow, ← pow_mul, ← pow_mul, mul_comm (2 * k + 1) (k + 1),
      mul_inv_cancel]
  refine ⟨y₀ * (w * (c ^ (k + 1))⁻¹), ?_, ?_⟩
  · rw [map_mul, MonoidHom.mem_ker.mp hzk, mul_one]
  · have hcomm : Commute y₀ (w * (c ^ (k + 1))⁻¹) := Subgroup.mem_center_iff.mp hzZ y₀
    rw [hcomm.mul_pow, ← hw, h4]

def powOneSubgroup (φ : G →* X) (E : Subgroup X) (p : ℕ)
    (hcomm : ∀ x ∈ E.comap φ, ∀ y ∈ E.comap φ, x * y = y * x) : Subgroup G where
  carrier := {y | y ∈ E.comap φ ∧ y ^ p = 1}
  mul_mem' {x y} hx hy := ⟨(E.comap φ).mul_mem hx.1 hy.1, by
    rw [(show Commute x y from hcomm x hx.1 y hy.1).mul_pow, hx.2, hy.2, one_mul]⟩
  one_mem' := ⟨(E.comap φ).one_mem, one_pow p⟩
  inv_mem' {x} hx := ⟨(E.comap φ).inv_mem hx.1, by rw [inv_pow, hx.2, inv_one]⟩

theorem mem_powOneSubgroup {E : Subgroup X} {p : ℕ}
    {hcomm : ∀ x ∈ E.comap φ, ∀ y ∈ E.comap φ, x * y = y * x} {y : G} :
    y ∈ powOneSubgroup φ E p hcomm ↔ φ y ∈ E ∧ y ^ p = 1 :=
  Iff.rfl

theorem exists_lift_pow_eq_one_of_mem_closure {E : Subgroup X} {p : ℕ}
    (hcomm : ∀ x ∈ E.comap φ, ∀ y ∈ E.comap φ, x * y = y * x) {S : Set X} (hSE : S ⊆ E)
    (hS : ∀ s ∈ S, ∃ y : G, φ y = s ∧ y ^ p = 1) {e : X} (he : e ∈ Subgroup.closure S) :
    ∃ y : G, φ y = e ∧ y ^ p = 1 := by
  have hle : Subgroup.closure S ≤ (powOneSubgroup φ E p hcomm).map φ := by
    rw [Subgroup.closure_le]
    intro s hs
    obtain ⟨y, hy, hyp⟩ := hS s hs
    exact ⟨y, mem_powOneSubgroup.mpr ⟨hy ▸ hSE hs, hyp⟩, hy⟩
  obtain ⟨y, hy, rfl⟩ := hle he
  exact ⟨y, rfl, (mem_powOneSubgroup.mp hy).2⟩

theorem commute_of_sq_eq_one (hker : φ.ker ≤ Subgroup.center G) {p : ℕ} (hp : Odd p)
    {u x : G} (hu : u ^ 2 = 1) (hx : x ^ p = 1) (h : Commute (φ u) (φ x)) : Commute u x := by
  obtain ⟨c, hc⟩ : ∃ c : G, c = u * x * u⁻¹ * x⁻¹ := ⟨_, rfl⟩
  have hcZ : c ∈ Subgroup.center G := hker (by
    rw [hc, MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, h.eq]
    group)
  have hcomm : ∀ g : G, g * c = c * g := fun g => Subgroup.mem_center_iff.mp hcZ g
  have h1 : u * x * u⁻¹ = c * x := by rw [hc]; group
  have huu : u⁻¹ = u := by
    rw [inv_eq_iff_mul_eq_one, ← pow_two, hu]
  have hc2 : c ^ 2 = 1 := by
    have e : x = c * c * x :=
      calc x = u * (u * x * u⁻¹) * u⁻¹ := by
            rw [huu]
            calc x = (u * u) * x * (u * u) := by rw [← pow_two, hu, one_mul, mul_one]
              _ = u * (u * x * u) * u := by group
        _ = u * (c * x) * u⁻¹ := by rw [h1]
        _ = c * (u * x * u⁻¹) := by
            rw [← mul_assoc u c, hcomm u]
            group
        _ = c * c * x := by rw [h1, ← mul_assoc]
    rw [pow_two]
    exact (mul_eq_right.mp e.symm)
  have hcp : c ^ p = 1 := by
    have e : (u * x * u⁻¹) ^ p = 1 := by rw [conj_pow, hx, mul_one, mul_inv_cancel]
    rwa [h1, (show Commute c x from (hcomm x).symm).mul_pow, hx, mul_one] at e
  have hc1 : c = 1 := by
    obtain ⟨k, rfl⟩ := hp
    rwa [pow_succ, pow_mul, hc2, one_pow, one_mul] at hcp
  have h2 : u * x * u⁻¹ = x := by rw [h1, hc1, one_mul]
  calc u * x = u * x * u⁻¹ * u := by group
    _ = x * u := by rw [h2]

theorem commutatorElement_inv_right_of_mem_center {x y : G} (h : ⁅x, y⁆ ∈ Subgroup.center G) :
    ⁅x, y⁻¹⁆ = ⁅x, y⁆⁻¹ := by
  have h1 := CFSG.RankThree.PartOne.CentralCoverThree.commutator_mul_right_of_central
    (y := x) (z := y⁻¹) (z' := y) h
  rw [inv_mul_cancel, commutatorElement_one_right] at h1
  exact eq_inv_of_mul_eq_one_left h1.symm

theorem commutatorElement_pow_right_of_mem_center {x y : G} (h : ⁅x, y⁆ ∈ Subgroup.center G)
    (n : ℕ) : ⁅x, y ^ n⁆ = ⁅x, y⁆ ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, commutatorElement_one_right]
  | succ n ih =>
    rw [pow_succ, CFSG.RankThree.PartOne.CentralCoverThree.commutator_mul_right_of_central h, ih,
      pow_succ]

theorem commute_of_conj (hφ : Function.Surjective φ) (hker : φ.ker ≤ Subgroup.center G)
    {p : ℕ} (hp : Odd p) {x y : G} (hxy : Commute (φ x) (φ y)) (hy : φ y ^ p = 1) {n : X}
    (hn : (n * φ x * n⁻¹ = φ x ∧ n * φ y * n⁻¹ = (φ y)⁻¹) ∨
      (n * φ x * n⁻¹ = φ y ∧ n * φ y * n⁻¹ = φ x)) : x * y = y * x := by
  have hc : ⁅x, y⁆ ∈ Subgroup.center G :=
    CFSG.RankThree.PartOne.CentralCoverThree.commutator_mem_center_of_commute hker hxy
  obtain ⟨m, rfl⟩ := hφ n
  have hconj : ⁅m * x * m⁻¹, m * y * m⁻¹⁆ = ⁅x, y⁆ := by
    rw [← conjugate_commutatorElement, Subgroup.mem_center_iff.mp hc m, mul_inv_cancel_right]
  have hinv : ⁅x, y⁆ = ⁅x, y⁆⁻¹ := by
    rcases hn with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · calc ⁅x, y⁆ = ⁅m * x * m⁻¹, m * y * m⁻¹⁆ := hconj.symm
        _ = ⁅x, y⁻¹⁆ := CFSG.RankThree.PartOne.CentralCoverThree.commutator_eq_of_map_eq hker
            (by simp [h1]) (by simp [h2])
        _ = ⁅x, y⁆⁻¹ := commutatorElement_inv_right_of_mem_center hc
    · calc ⁅x, y⁆ = ⁅m * x * m⁻¹, m * y * m⁻¹⁆ := hconj.symm
        _ = ⁅y, x⁆ := CFSG.RankThree.PartOne.CentralCoverThree.commutator_eq_of_map_eq hker
            (by simp [h1]) (by simp [h2])
        _ = ⁅x, y⁆⁻¹ := (commutatorElement_inv _ _).symm
  have hc2 : ⁅x, y⁆ ^ 2 = 1 := by
    rw [pow_two]
    exact mul_eq_one_iff_eq_inv.mpr hinv
  have hcp : ⁅x, y⁆ ^ p = 1 := by
    have hyp : y ^ p ∈ Subgroup.center G := hker (by rw [MonoidHom.mem_ker, map_pow, hy])
    rw [← commutatorElement_pow_right_of_mem_center hc,
      commutatorElement_eq_one_iff_mul_comm]
    exact Subgroup.mem_center_iff.mp hyp x
  have hc1 : ⁅x, y⁆ = 1 := by
    obtain ⟨k, rfl⟩ := hp
    rwa [pow_succ, pow_mul, hc2, one_pow, one_mul] at hcp
  exact commutatorElement_eq_one_iff_mul_comm.mp hc1

theorem commute_of_mem_closure (hφ : Function.Surjective φ) (hker : φ.ker ≤ Subgroup.center G)
    {S : Set X} (hS : ∀ x y : G, φ x ∈ S → φ y ∈ S → φ x ≠ φ y → x * y = y * x) {x y : G}
    (hx : φ x ∈ Subgroup.closure S) (hy : φ y ∈ Subgroup.closure S) : x * y = y * x := by
  have hpair : (φ ⁻¹' S).Pairwise Commute := by
    intro a ha b hb _
    by_cases hab : φ a = φ b
    · have hz : a⁻¹ * b ∈ Subgroup.center G := hker (by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hab, inv_mul_cancel])
      calc a * b = a * (a * (a⁻¹ * b)) := by rw [mul_inv_cancel_left]
        _ = a * ((a⁻¹ * b) * a) := by rw [Subgroup.mem_center_iff.mp hz a]
        _ = b * a := by group
    · exact hS a b ha hb hab
  have hK := Subgroup.isMulCommutative_closure hpair
  have hmap : (Subgroup.closure (φ ⁻¹' S)).map φ = Subgroup.closure S := by
    rw [MonoidHom.map_closure, Set.image_preimage_eq S hφ]
  rw [← hmap] at hx hy
  obtain ⟨x', hx', hxx⟩ := hx
  obtain ⟨y', hy', hyy⟩ := hy
  have h1 : x' * y' = y' * x' := congrArg Subtype.val (hK.is_comm.comm ⟨x', hx'⟩ ⟨y', hy'⟩)
  have h2 : ⁅x', y'⁆ = ⁅x, y⁆ :=
    CFSG.RankThree.PartOne.CentralCoverThree.commutator_eq_of_map_eq hker hxx hyy
  rw [← commutatorElement_eq_one_iff_mul_comm, ← h2, commutatorElement_eq_one_iff_mul_comm]
  exact h1

end Lifts

section Rank

variable {G : Type} {X : Type*} [Group G] [Group X] {φ : G →* X}

theorem add_le_localRank_of_lift [Finite G] (hφ : Function.Surjective φ)
    (hker : φ.ker ≤ Subgroup.center G) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {Z : Subgroup G}
    (hZk : Z ≤ φ.ker) (hZp : ∀ z ∈ Z, z ^ p = 1) {s : ℕ} (hs : p ^ s ≤ Nat.card Z)
    {E : Subgroup X} (hcomm : ∀ x ∈ E.comap φ, ∀ y ∈ E.comap φ, x * y = y * x)
    (hlift : ∀ e ∈ E, ∃ y : G, φ y = e ∧ y ^ p = 1) {t : X} (ht1 : t ≠ 1) (ht2 : t ^ 2 = 1)
    (htE : ∀ e ∈ E, Commute t e) {r : ℕ} (hr : p ^ r ≤ Nat.card E) :
    r + s ≤ localRank p G := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  set U := powOneSubgroup φ E p hcomm with hUdef
  have hUab : IsElemAbelian p U :=
    ⟨⟨⟨fun a b => Subtype.ext (hcomm _ (mem_powOneSubgroup.mp a.2).1 _
      (mem_powOneSubgroup.mp b.2).1)⟩⟩, fun x hx => (mem_powOneSubgroup.mp hx).2⟩
  have hUP : IsPGroup p U := fun x => ⟨1, Subtype.ext (by
    rw [pow_one, Subgroup.coe_pow, OneMemClass.coe_one]
    exact (mem_powOneSubgroup.mp x.2).2)⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hUP
  let ψ : U →* X := φ.comp U.subtype
  have hψr : ψ.range = E := by
    ext e
    constructor
    · rintro ⟨x, rfl⟩
      exact (mem_powOneSubgroup.mp x.2).1
    · intro he
      obtain ⟨y, hy, hyp⟩ := hlift e he
      exact ⟨⟨y, mem_powOneSubgroup.mpr ⟨hy ▸ he, hyp⟩⟩, hy⟩
  have hZU : Z ≤ U := fun z hz => mem_powOneSubgroup.mpr
    ⟨by rw [MonoidHom.mem_ker.mp (hZk hz)]; exact E.one_mem, hZp z hz⟩
  have hZψ : Z.subgroupOf U ≤ ψ.ker := fun w hw =>
    MonoidHom.mem_ker.mpr (MonoidHom.mem_ker.mp (hZk (Subgroup.mem_subgroupOf.mp hw)))
  have hψk : p ^ s ≤ Nat.card ψ.ker := by
    calc p ^ s ≤ Nat.card Z := hs
      _ = Nat.card (Z.subgroupOf U) :=
          (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZU).toEquiv).symm
      _ ≤ Nat.card ψ.ker := Subgroup.card_le_of_le hZψ
  have hrk : r + s ≤ k := by
    have h1 : p ^ (r + s) ≤ p ^ k := by
      rw [← hk, ← Subgroup.card_ker_mul_card_range ψ, hψr, pow_add, mul_comm]
      exact Nat.mul_le_mul hψk hr
    exact (Nat.pow_le_pow_iff_right hp.one_lt).mp h1
  obtain ⟨y, hy⟩ := hφ t
  have hot : orderOf t = 2 := orderOf_eq_prime ht2 ht1
  have hdvd : 2 ∣ orderOf y := by
    rw [← hot, ← hy]
    exact orderOf_map_dvd φ y
  have hy0 : orderOf y ≠ 0 := (orderOf_pos y).ne'
  have hu : orderOf (y ^ (orderOf y / 2)) = 2 := orderOf_pow_orderOf_div hy0 hdvd
  have hu2 : (y ^ (orderOf y / 2)) ^ 2 = 1 := by
    have h := pow_orderOf_eq_one (y ^ (orderOf y / 2))
    rwa [hu] at h
  have hcent : ∀ x ∈ U, x * y ^ (orderOf y / 2) = y ^ (orderOf y / 2) * x := by
    intro x hx
    obtain ⟨hxE, hxp⟩ := mem_powOneSubgroup.mp hx
    have h : Commute (φ (y ^ (orderOf y / 2))) (φ x) := by
      rw [map_pow, hy]
      exact (htE _ hxE).pow_left _
    exact (commute_of_sq_eq_one hker (hp.odd_of_ne_two hp2) hu2 hxp h).eq.symm
  exact hrk.trans
    (CFSG.RankThree.PartTwo.Census.le_localRank_of_commute_involution hp hu hUab hk hcent)

theorem succ_le_localRank_of_lift [Finite G] (hφ : Function.Surjective φ)
    (hker : φ.ker ≤ Subgroup.center G) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpk : p ∣ Nat.card φ.ker) {E : Subgroup X}
    (hcomm : ∀ x ∈ E.comap φ, ∀ y ∈ E.comap φ, x * y = y * x)
    (hlift : ∀ e ∈ E, ∃ y : G, φ y = e ∧ y ^ p = 1) {t : X} (ht1 : t ≠ 1) (ht2 : t ^ 2 = 1)
    (htE : ∀ e ∈ E, Commute t e) {r : ℕ} (hr : p ^ r ≤ Nat.card E) :
    r + 1 ≤ localRank p G := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' p hpk
  have hzo : orderOf (z : G) = p := by rw [Subgroup.orderOf_coe, hz]
  refine add_le_localRank_of_lift hφ hker hp hp2 (Z := Subgroup.zpowers (z : G)) ?_ ?_ ?_
    hcomm hlift ht1 ht2 htE hr
  · rw [Subgroup.zpowers_le]
    exact z.2
  · rintro _ ⟨j, rfl⟩
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hzo,
      pow_orderOf_eq_one, one_zpow]
  · rw [Nat.card_zpowers, hzo, pow_one]

end Rank

end TripleCoverLift

end CFSG.RankThree.PartTwo.Sec4.Census
