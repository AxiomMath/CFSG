module

public import CFSG.RankThree.PartTwo.Sec3.ThompsonFamilyG

import Mathlib.Algebra.Group.Pointwise.Set.Card

public section

namespace CFSG.RankThree.PartTwo.Sec20

open Subgroup

section Tools

variable {X : Type*} [Group X]

private noncomputable def conjRestrict {U : Subgroup X} [Finite U] {x : X}
    (hx : ∀ w ∈ U, x * w * x⁻¹ ∈ U) : MulAut U :=
  MulEquiv.ofBijective
    (((MulAut.conj x).toMonoidHom.comp U.subtype).codRestrict U fun w => hx w w.2)
    (Finite.injective_iff_bijective.1 fun p q h => by
      have h' : x * (p : X) * x⁻¹ = x * q * x⁻¹ := congrArg Subtype.val h
      exact Subtype.ext (by simpa using h'))

private theorem coe_conjRestrict {U : Subgroup X} [Finite U] {x : X}
    (hx : ∀ w ∈ U, x * w * x⁻¹ ∈ U) (w : U) :
    ((conjRestrict hx w : U) : X) = x * w * x⁻¹ := rfl

private theorem coe_conjRestrict_pow {U : Subgroup X} [Finite U] {x : X}
    (hx : ∀ w ∈ U, x * w * x⁻¹ ∈ U) (n : ℕ) (w : U) :
    (((conjRestrict hx ^ n) w : U) : X) = x ^ n * w * (x ^ n)⁻¹ := by
  induction n generalizing w with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, MulAut.mul_apply, ih, coe_conjRestrict, pow_succ x n]
    group

private theorem pow_orderOf_conjRestrict_conj_eq {U : Subgroup X} [Finite U] {x : X}
    (hx : ∀ w ∈ U, x * w * x⁻¹ ∈ U) {w : X} (hw : w ∈ U) :
    x ^ orderOf (conjRestrict hx) * w * (x ^ orderOf (conjRestrict hx))⁻¹ = w := by
  have h := coe_conjRestrict_pow hx (orderOf (conjRestrict hx)) ⟨w, hw⟩
  rw [pow_orderOf_eq_one] at h
  exact h.symm

private theorem pow_factorial_conj_eq {U : Subgroup X} [Finite U] {x : X}
    (hx : ∀ w ∈ U, x * w * x⁻¹ ∈ U) {n : ℕ} (hn : Nat.card U ≤ n) {w : X} (hw : w ∈ U) :
    x ^ n.factorial * w * (x ^ n.factorial)⁻¹ = w := by
  have hord : conjRestrict hx ^ n.factorial = 1 := by
    rw [← orderOf_dvd_iff_pow_eq_one,
      ← orderOf_injective (MulAut.toPerm U) (fun f g h => MulEquiv.ext fun u => congr($h u))]
    refine (_root_.orderOf_dvd_natCard _).trans ?_
    rw [Nat.card_perm]
    exact Nat.factorial_dvd_factorial hn
  have h := coe_conjRestrict_pow hx n.factorial ⟨w, hw⟩
  rw [hord] at h
  exact h.symm

private theorem pow_comm_mem {I U : Subgroup X} {x : X} (hx : x ∈ normalizer (I : Set X))
    (hU : ∀ i ∈ I, x * i * x⁻¹ * i⁻¹ ∈ U) (n : ℕ) {i : X} (hi : i ∈ I) :
    x ^ n * i * (x ^ n)⁻¹ * i⁻¹ ∈ U := by
  induction n generalizing i with
  | zero => simp
  | succ n ih =>
    have hj : x ^ n * i * (x ^ n)⁻¹ ∈ I := (mem_normalizer_iff.1 (pow_mem hx n) i).1 hi
    have h : x ^ (n + 1) * i * (x ^ (n + 1))⁻¹ * i⁻¹ =
        (x * (x ^ n * i * (x ^ n)⁻¹) * x⁻¹ * (x ^ n * i * (x ^ n)⁻¹)⁻¹) *
          (x ^ n * i * (x ^ n)⁻¹ * i⁻¹) := by
      rw [pow_succ' x n]
      group
    rw [h]
    exact U.mul_mem (hU _ hj) (ih hi)

private theorem pow_two_mul_mem_centralizer {I U : Subgroup X} (hI : Sec3.IsElemTwo I)
    (hUI : U ≤ I) {x : X} (hx : x ∈ normalizer (I : Set X))
    (hU : ∀ i ∈ I, x * i * x⁻¹ * i⁻¹ ∈ U) {n : ℕ}
    (hn : ∀ w ∈ U, x ^ n * w * (x ^ n)⁻¹ = w) : x ^ (2 * n) ∈ centralizer (I : Set X) := by
  rw [pow_mul', mem_centralizer_iff]
  intro i hi
  set y := x ^ n
  have hw : y * i * y⁻¹ * i⁻¹ ∈ U := pow_comm_mem hx hU n hi
  have hyw : y * (y * i * y⁻¹ * i⁻¹) * y⁻¹ = y * i * y⁻¹ * i⁻¹ := hn _ hw
  have hw2 : (y * i * y⁻¹ * i⁻¹) * (y * i * y⁻¹ * i⁻¹) = 1 := hI.2 _ (hUI hw)
  generalize hwdef : y * i * y⁻¹ * i⁻¹ = w at hyw hw2
  have h1 : y * i * y⁻¹ = w * i := by rw [← hwdef]; group
  have h2 : y * (y * i * y⁻¹) * y⁻¹ = i := by
    calc y * (y * i * y⁻¹) * y⁻¹ = y * (w * i) * y⁻¹ := by rw [h1]
      _ = (y * w * y⁻¹) * (y * i * y⁻¹) := by group
      _ = w * (w * i) := by rw [hyw, h1]
      _ = (w * w) * i := (mul_assoc w w i).symm
      _ = i := by rw [hw2, one_mul]
  rw [pow_two]
  calc i * (y * y) = (y * (y * i * y⁻¹) * y⁻¹) * (y * y) := by rw [h2]
    _ = y * y * i := by group

private theorem pow_mem_centralizer_of_acts {I U : Subgroup X} [Finite U]
    (hI : Sec3.IsElemTwo I) (hUI : U ≤ I) {x : X} (hx : x ∈ normalizer (I : Set X))
    (hxU : ∀ w ∈ U, x * w * x⁻¹ ∈ U) (hU : ∀ i ∈ I, x * i * x⁻¹ * i⁻¹ ∈ U) {n : ℕ}
    (hn : Nat.card U ≤ n) : x ^ (2 * n.factorial) ∈ centralizer (I : Set X) :=
  pow_two_mul_mem_centralizer hI hUI hx hU fun _ hw => pow_factorial_conj_eq hxU hn hw

end Tools

section CommutatorMap

variable {X : Type*} [Group X] {I : Subgroup X}

private theorem comm_mem {g : X} (hg : g ∈ normalizer (I : Set X)) {i : X} (hi : i ∈ I) :
    g * i * g⁻¹ * i⁻¹ ∈ I :=
  I.mul_mem ((mem_normalizer_iff.1 hg i).1 hi) (I.inv_mem hi)

private def commMap (hI : ∀ a ∈ I, ∀ b ∈ I, a * b = b * a) {g : X}
    (hg : g ∈ normalizer (I : Set X)) : I →* X :=
  MonoidHom.mk' (fun i => g * i * g⁻¹ * (i : X)⁻¹) fun i j => by
    have hc := hI _ (comm_mem hg j.2) _ (I.inv_mem i.2)
    calc g * ↑(i * j) * g⁻¹ * (↑(i * j) : X)⁻¹
        = g * i * g⁻¹ * ((g * j * g⁻¹ * (j : X)⁻¹) * (i : X)⁻¹) := by
          rw [Subgroup.coe_mul]; group
      _ = g * i * g⁻¹ * ((i : X)⁻¹ * (g * j * g⁻¹ * (j : X)⁻¹)) := by rw [hc]
      _ = g * i * g⁻¹ * (i : X)⁻¹ * (g * j * g⁻¹ * (j : X)⁻¹) := by group

private theorem commMap_apply (hI : ∀ a ∈ I, ∀ b ∈ I, a * b = b * a) {g : X}
    (hg : g ∈ normalizer (I : Set X)) (i : I) :
    commMap hI hg i = g * i * g⁻¹ * (i : X)⁻¹ := rfl

private theorem range_commMap_le (hI : ∀ a ∈ I, ∀ b ∈ I, a * b = b * a) {g : X}
    (hg : g ∈ normalizer (I : Set X)) : (commMap hI hg).range ≤ I := by
  rintro _ ⟨i, rfl⟩
  exact comm_mem hg i.2

private theorem natCard_range_commMap (hI : ∀ a ∈ I, ∀ b ∈ I, a * b = b * a) {g : X}
    (hg : g ∈ normalizer (I : Set X)) :
    Nat.card (commMap hI hg).range = (centralizer ({g} : Set X)).relIndex I := by
  have hker : (commMap hI hg).ker = (centralizer ({g} : Set X)).subgroupOf I := by
    ext i
    rw [MonoidHom.mem_ker, mem_subgroupOf, mem_centralizer_iff, commMap_apply]
    simp only [Set.mem_singleton_iff, forall_eq]
    rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul]
  rw [← Subgroup.index_ker, hker]
  rfl

private theorem conj_mem_sup (hI : ∀ a ∈ I, ∀ b ∈ I, a * b = b * a) {g h : X}
    (hg : g ∈ normalizer (I : Set X)) (hh : h ∈ normalizer (I : Set X)) {w : X}
    (hw : w ∈ (commMap hI hg).range ⊔ (commMap hI hh).range) :
    g * w * g⁻¹ ∈ (commMap hI hg).range ⊔ (commMap hI hh).range := by
  have key : (commMap hI hg).range ⊔ (commMap hI hh).range ≤
      ((commMap hI hg).range ⊔ (commMap hI hh).range).comap (MulAut.conj g).toMonoidHom := by
    refine sup_le ?_ ?_
    · rintro _ ⟨i, rfl⟩
      change g * commMap hI hg i * g⁻¹ ∈ (commMap hI hg).range ⊔ (commMap hI hh).range
      refine Subgroup.mem_sup_left ⟨⟨g * i * g⁻¹, (mem_normalizer_iff.1 hg i).1 i.2⟩, ?_⟩
      rw [commMap_apply, commMap_apply]
      group
    · rintro _ ⟨j, rfl⟩
      have hwI : commMap hI hh j ∈ I := comm_mem hh j.2
      change g * commMap hI hh j * g⁻¹ ∈ (commMap hI hg).range ⊔ (commMap hI hh).range
      have h : g * commMap hI hh j * g⁻¹ = commMap hI hg ⟨_, hwI⟩ * commMap hI hh j := by
        rw [commMap_apply hI hg ⟨_, hwI⟩]
        group
      rw [h]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨_, rfl⟩) (Subgroup.mem_sup_right ⟨j, rfl⟩)
  exact key hw

open scoped Pointwise in
private theorem natCard_sup_le {R S : Subgroup X} (h : ∀ p ∈ R, ∀ q ∈ S, p * q = q * p) :
    Nat.card ↥(R ⊔ S) ≤ Nat.card R * Nat.card S := by
  have hRS : R ≤ centralizer (S : Set X) := fun p hp =>
    mem_centralizer_iff.2 fun q hq => (h p hp q hq).symm
  have hcoe : ((R ⊔ S : Subgroup X) : Set X) = (R : Set X) * S :=
    coe_mul_of_left_le_normalizer_right R S (hRS.trans (centralizer_le_normalizer _))
  calc Nat.card ↥(R ⊔ S) = Nat.card (((R ⊔ S : Subgroup X) : Set X)) := rfl
    _ = Nat.card ((R : Set X) * S : Set X) := by rw [hcoe]
    _ ≤ Nat.card (R : Set X) * Nat.card (S : Set X) := Set.natCard_mul_le

private theorem exists_subgroup_of_relIndex_le (hI : Sec3.IsElemTwo I) {u v : X}
    (hu : u ∈ normalizer (I : Set X)) (hv : v ∈ normalizer (I : Set X)) {a b : ℕ}
    (hua : (centralizer ({u} : Set X)).relIndex I ≤ a)
    (hvb : (centralizer ({v} : Set X)).relIndex I ≤ b) :
    ∃ U : Subgroup X, U ≤ I ∧ Nat.card U ≤ a * b ∧ (∀ w ∈ U, u * v * w * (u * v)⁻¹ ∈ U) ∧
      (∀ i ∈ I, u * v * i * (u * v)⁻¹ * i⁻¹ ∈ U) ∧ ∀ w ∈ U, u * w * u⁻¹ ∈ U := by
  have hc := hI.1
  have hRu := range_commMap_le hc hu
  have hRv := range_commMap_le hc hv
  refine ⟨(commMap hc hu).range ⊔ (commMap hc hv).range, sup_le hRu hRv, ?_, ?_, ?_, ?_⟩
  · refine (natCard_sup_le fun p hp q hq => hc p (hRu hp) q (hRv hq)).trans ?_
    rw [natCard_range_commMap, natCard_range_commMap]
    exact Nat.mul_le_mul hua hvb
  · intro w hw
    have h1 := conj_mem_sup hc hv hu (by rwa [sup_comm] : w ∈ _ ⊔ _)
    have h2 := conj_mem_sup hc hu hv (by rwa [sup_comm] at h1)
    rw [show u * v * w * (u * v)⁻¹ = u * (v * w * v⁻¹) * u⁻¹ by group]
    exact h2
  · intro i hi
    have h1 : v * i * v⁻¹ * i⁻¹ ∈ (commMap hc hu).range ⊔ (commMap hc hv).range :=
      Subgroup.mem_sup_right ⟨⟨i, hi⟩, rfl⟩
    have h2 := conj_mem_sup hc hu hv h1
    have h3 : u * i * u⁻¹ * i⁻¹ ∈ (commMap hc hu).range ⊔ (commMap hc hv).range :=
      Subgroup.mem_sup_left ⟨⟨i, hi⟩, rfl⟩
    rw [show u * v * i * (u * v)⁻¹ * i⁻¹ =
      (u * (v * i * v⁻¹ * i⁻¹) * u⁻¹) * (u * i * u⁻¹ * i⁻¹) by group]
    exact Subgroup.mul_mem _ h2 h3
  · intro w hw
    exact conj_mem_sup hc hu hv hw

end CommutatorMap

theorem pow_mem_centralizer_of_relIndex_le {X : Type*} [Group X] [Finite X] {I : Subgroup X}
    (hI : Sec3.IsElemTwo I) {u v : X} (hu : u ∈ normalizer (I : Set X))
    (hv : v ∈ normalizer (I : Set X)) {a b : ℕ}
    (hua : (centralizer ({u} : Set X)).relIndex I ≤ a)
    (hvb : (centralizer ({v} : Set X)).relIndex I ≤ b) :
    (u * v) ^ (2 * (a * b).factorial) ∈ centralizer (I : Set X) := by
  obtain ⟨U, hUI, hUab, hxU, hxI, -⟩ := exists_subgroup_of_relIndex_le hI hu hv hua hvb
  exact pow_mem_centralizer_of_acts hI hUI (mul_mem hu hv) hxU hxI hUab

section PrimePowerOrbit

variable {U : Type*} [Group U]

private def fixedSubgroup (ρ : MulAut U) : Subgroup U where
  carrier := {w | ρ w = w}
  mul_mem' := fun {a b} (ha : ρ a = a) (hb : ρ b = b) => by
    change ρ (a * b) = a * b
    rw [map_mul, ha, hb]
  one_mem' := map_one ρ
  inv_mem' := fun {a} (ha : ρ a = a) => by
    change ρ a⁻¹ = a⁻¹
    rw [map_inv, ha]

private theorem pow_dvd_ncard_compl_fixedSubgroup [Finite U] {τ : MulAut U} {p k : ℕ}
    (hp : p.Prime) (hτ : orderOf τ = p ^ (k + 1)) :
    p ^ (k + 1) ∣ ((fixedSubgroup (τ ^ p ^ k) : Set U)ᶜ).ncard := by
  have : Fact p.Prime := ⟨hp⟩
  set ρ : MulAut U := τ ^ p ^ k with hρ
  have hρord : orderOf ρ = p := by
    rw [hρ, orderOf_pow_of_dvd (pow_ne_zero _ hp.ne_zero)
      (by rw [hτ]; exact pow_dvd_pow p (Nat.le_succ k)), hτ, pow_succ,
      Nat.mul_div_cancel_left _ (pow_pos hp.pos k)]
  set G : Subgroup (MulAut U) := Subgroup.zpowers τ with hG
  have hGcard : Nat.card G = p ^ (k + 1) := by rw [hG, Nat.card_zpowers, hτ]
  have hcomm : ∀ g ∈ G, Commute g ρ := by
    intro g hg
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
    exact ((Commute.refl τ).zpow_left i).pow_right _
  let T : SubMulAction G U :=
    { carrier := (fixedSubgroup ρ : Set U)ᶜ
      smul_mem' := by
        intro g w hw hgw
        apply hw
        have h1 : ρ ((g : MulAut U) w) = (g : MulAut U) w := hgw
        have h2 : ρ ((g : MulAut U) w) = (g : MulAut U) (ρ w) :=
          congrArg (fun f : MulAut U => f w) (hcomm g g.2).symm.eq
        exact (g : MulAut U).injective (h2.symm.trans h1) }
  have hfree : ∀ x : T, MulAction.stabilizer G x = ⊥ := by
    intro x
    by_contra hne
    have hdvd : Nat.card (MulAction.stabilizer G x) ∣ p ^ (k + 1) :=
      hGcard ▸ Subgroup.card_subgroup_dvd_card _
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).1 hdvd
    have hj0 : j ≠ 0 := by
      rintro rfl
      exact hne (Subgroup.card_eq_one.1 (by simpa using hj))
    obtain ⟨h, hh⟩ := exists_prime_orderOf_dvd_card' (G := MulAction.stabilizer G x) p
      (hj ▸ dvd_pow_self p hj0)
    have hh2 : orderOf ((h : G) : MulAut U) = p := by
      rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hh]
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 (h : G).2
    have hp1 : ((h : G) : MulAut U) ^ p = 1 := by
      rw [← hh2]
      exact pow_orderOf_eq_one _
    have h3 : τ ^ (i * (p : ℤ)) = 1 := by
      rw [zpow_mul, hi, zpow_natCast]
      exact hp1
    have h4 : ((p ^ (k + 1) : ℕ) : ℤ) ∣ i * p := by
      rw [← hτ]
      exact orderOf_dvd_iff_zpow_eq_one.2 h3
    have h5 : ((p ^ k : ℕ) : ℤ) ∣ i := by
      have e : ((p ^ (k + 1) : ℕ) : ℤ) = ((p ^ k : ℕ) : ℤ) * p := by push_cast; ring
      rw [e] at h4
      exact (mul_dvd_mul_iff_right (by exact_mod_cast hp.ne_zero)).1 h4
    obtain ⟨m, hm⟩ := h5
    have h6 : ((h : G) : MulAut U) = ρ ^ m := by
      rw [← hi, hm, zpow_mul, hρ, zpow_natCast]
    have h7 : Subgroup.zpowers ((h : G) : MulAut U) = Subgroup.zpowers ρ := by
      apply Subgroup.eq_of_le_of_card_ge
      · rw [Subgroup.zpowers_le]
        exact Subgroup.mem_zpowers_iff.2 ⟨m, h6.symm⟩
      · rw [Nat.card_zpowers, Nat.card_zpowers, hh2, hρord]
    have h8 : ρ ∈ Subgroup.zpowers ((h : G) : MulAut U) := by
      rw [h7]
      exact Subgroup.mem_zpowers ρ
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 h8
    have h9 : ((h ^ n : MulAction.stabilizer G x) : G) • x = x := (h ^ n).2
    have h10 : ρ (x : U) = x := by
      have h11 := congrArg Subtype.val h9
      have h12 : (((h ^ n : MulAction.stabilizer G x) : G) : MulAut U) = ρ := by
        rw [← hn]
        simp
      rw [← h12]
      exact h11
    exact x.2 h10
  have hmain : ∀ y : T, Nat.card (MulAction.orbit G y) = p ^ (k + 1) := by
    intro y
    have h1 := MulAction.index_stabilizer G y
    rw [hfree y, Subgroup.index_bot, hGcard] at h1
    rw [Nat.card_coe_set_eq]
    exact h1.symm
  have : Finite T := inferInstance
  have : Fintype (Quotient (MulAction.orbitRel G T)) := Fintype.ofFinite _
  have hcard : Nat.card T =
      ∑ ω : Quotient (MulAction.orbitRel G T), Nat.card (MulAction.orbit G ω.out) := by
    rw [Nat.card_congr (MulAction.selfEquivSigmaOrbits G T), Nat.card_sigma]
  have hdvdT : p ^ (k + 1) ∣ Nat.card T := by
    rw [hcard]
    exact Finset.dvd_sum fun ω _ => (hmain ω.out) ▸ dvd_rfl
  rw [← Nat.card_coe_set_eq]
  exact hdvdT

end PrimePowerOrbit

theorem prime_pow_dvd_two_pow_sub_one_of_dvd_orderOf {U : Type*} [Group U] [Finite U] {d : ℕ}
    (hU : Nat.card U = 2 ^ d) (σ : MulAut U) {p k : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hk : 1 ≤ k) (hdvd : p ^ k ∣ orderOf σ) : ∃ e, 1 ≤ e ∧ e ≤ d ∧ p ^ k ∣ 2 ^ e - 1 := by
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have hτ : orderOf (σ ^ (orderOf σ / p ^ (k + 1))) = p ^ (k + 1) :=
    orderOf_pow_orderOf_div (orderOf_pos σ).ne' hdvd
  set τ : MulAut U := σ ^ (orderOf σ / p ^ (k + 1))
  have hne : τ ^ p ^ k ≠ 1 :=
    pow_ne_one_of_lt_orderOf (pow_ne_zero _ hp.ne_zero)
      (by rw [hτ]; exact Nat.pow_lt_pow_right hp.one_lt (Nat.lt_succ_self k))
  set F : Subgroup U := fixedSubgroup (τ ^ p ^ k)
  have hFtop : F ≠ ⊤ := by
    intro h
    apply hne
    ext w
    have hw : w ∈ F := by
      rw [h]
      exact Subgroup.mem_top w
    exact hw
  have hFd : Nat.card F ∣ 2 ^ d := by
    rw [← hU]
    exact Subgroup.card_subgroup_dvd_card F
  obtain ⟨c, hcd, hcF⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hFd
  have hlt : c < d := by
    refine lt_of_le_of_ne hcd ?_
    rintro rfl
    exact hFtop (Subgroup.eq_top_of_card_eq F (by rw [hcF, hU]))
  have hFn : (F : Set U).ncard = 2 ^ c := by
    rw [← Nat.card_coe_set_eq]
    exact hcF
  have hsum := Set.ncard_add_ncard_compl (F : Set U)
  rw [hFn, hU] at hsum
  have hcompl : ((F : Set U)ᶜ).ncard = 2 ^ c * (2 ^ (d - c) - 1) := by
    rw [Nat.mul_sub_one, ← pow_add, Nat.add_sub_cancel' hlt.le]
    omega
  have hcop : Nat.Coprime (p ^ (k + 1)) (2 ^ c) :=
    Nat.Coprime.pow _ _ ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
  refine ⟨d - c, by omega, by omega, ?_⟩
  exact hcop.dvd_of_dvd_mul_left (hcompl ▸ pow_dvd_ncard_compl_fixedSubgroup hp hτ)

theorem exists_pow_mem_centralizer_prime_pow {X : Type*} [Group X] [Finite X] {I : Subgroup X}
    (hI : Sec3.IsElemTwo I) {u v : X} (hu : u ∈ normalizer (I : Set X))
    (hv : v ∈ normalizer (I : Set X)) {a b : ℕ}
    (hua : (centralizer ({u} : Set X)).relIndex I ≤ a)
    (hvb : (centralizer ({v} : Set X)).relIndex I ≤ b) :
    ∃ N : ℕ, 0 < N ∧ (u * v) ^ (2 * N) ∈ centralizer (I : Set X) ∧
      ∀ p k : ℕ, p.Prime → p ≠ 2 → 1 ≤ k → p ^ k ∣ N →
        ∃ e, 1 ≤ e ∧ 2 ^ e ≤ a * b ∧ p ^ k ∣ 2 ^ e - 1 := by
  obtain ⟨U, hUI, hUab, hxU, hxI, -⟩ := exists_subgroup_of_relIndex_le hI hu hv hua hvb
  have hU2 : IsPGroup 2 U := fun g => ⟨1, Subtype.ext (by simpa [pow_two] using hI.2 _ (hUI g.2))⟩
  obtain ⟨d, hd⟩ := IsPGroup.iff_card.1 hU2
  refine ⟨orderOf (conjRestrict hxU), orderOf_pos _,
    pow_two_mul_mem_centralizer hI hUI (mul_mem hu hv) hxI fun w hw =>
      pow_orderOf_conjRestrict_conj_eq hxU hw, ?_⟩
  intro p k hp hp2 hk hdvd
  obtain ⟨e, he1, hed, hdvd'⟩ :=
    prime_pow_dvd_two_pow_sub_one_of_dvd_orderOf hd (conjRestrict hxU) hp hp2 hk hdvd
  exact ⟨e, he1, (Nat.pow_le_pow_right two_pos hed).trans (hd.symm.trans_le hUab), hdvd'⟩

theorem exists_pow_mem_centralizer_odd_dvd_105 {X : Type*} [Group X] [Finite X]
    {I : Subgroup X} (hI : Sec3.IsElemTwo I) {u v : X} (hu : u ∈ normalizer (I : Set X))
    (hv : v ∈ normalizer (I : Set X))
    (hu4 : (centralizer ({u} : Set X)).relIndex I ≤ 4)
    (hv4 : (centralizer ({v} : Set X)).relIndex I ≤ 4) :
    ∃ N : ℕ, 0 < N ∧ (u * v) ^ (2 * N) ∈ centralizer (I : Set X) ∧
      ∀ m : ℕ, Odd m → m ∣ N → m ∣ 105 := by
  obtain ⟨N, hN, hpow, hprime⟩ := exists_pow_mem_centralizer_prime_pow hI hu hv hu4 hv4
  refine ⟨N, hN, hpow, fun m hm hmN => ?_⟩
  refine (Nat.dvd_iff_prime_pow_dvd_dvd 105 m).2 fun p k hp hpk => ?_
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.2 hm) (even_iff_two_dvd.2 ((dvd_pow_self 2 hk.ne').trans hpk))
  obtain ⟨e, he1, he, hdvd⟩ := hprime p k hp hp2 hk (hpk.trans hmN)
  have he4 : e ≤ 4 := by
    by_contra h
    have h5 : 2 ^ 5 ≤ 2 ^ e := Nat.pow_le_pow_right two_pos (by omega)
    omega
  obtain rfl | rfl | rfl | rfl : e = 1 ∨ e = 2 ∨ e = 3 ∨ e = 4 := by omega
  all_goals exact hdvd.trans (by norm_num)

section DihedralSeven

private theorem card_eq_eight {W : Type*} [CommGroup W] [Finite W] [Nontrivial W]
    (hW2 : ∀ w : W, w * w = 1) (hW16 : Nat.card W ≤ 16) {ρ : MulAut W} (hρ : orderOf ρ = 7)
    (hfix : ∀ w : W, ρ w = w → w = 1) : Nat.card W = 8 := by
  have h1 := pow_dvd_ncard_compl_fixedSubgroup (τ := ρ) (p := 7) (k := 0) Nat.prime_seven
    (by simpa using hρ)
  have hF : (fixedSubgroup (ρ ^ 7 ^ 0) : Set W) = {1} := by
    ext w
    simp only [pow_zero, pow_one]
    refine ⟨fun hw => hfix w hw, ?_⟩
    rintro rfl
    exact map_one ρ
  rw [hF, Set.ncard_compl, Set.ncard_singleton] at h1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP : IsPGroup 2 W := fun g => ⟨1, by simpa [pow_two] using hW2 g⟩
  obtain ⟨d, hd⟩ := IsPGroup.iff_card.1 hP
  have hnt : 1 < Nat.card W := Finite.one_lt_card
  rw [hd] at h1 hW16 hnt ⊢
  have hd4 : d ≤ 4 := by
    by_contra h
    have h5 : 2 ^ 5 ≤ 2 ^ d := Nat.pow_le_pow_right two_pos (by omega)
    omega
  interval_cases d <;> simp_all

private theorem exists_two_fixed {W : Type*} [CommGroup W] [Finite W] (hW2 : ∀ w : W, w * w = 1)
    (hW : Nat.card W = 8) {τ : MulAut W} (hτ : ∀ w, τ (τ w) = w) :
    ∃ p q : W, p ≠ 1 ∧ q ≠ 1 ∧ p ≠ q ∧ τ p = p ∧ τ q = q := by
  let ψ : W →* W := MonoidHom.mk' (fun w => τ w * w) fun a b => by
    rw [map_mul]
    exact mul_mul_mul_comm _ _ _ _
  have hker : ψ.ker = fixedSubgroup τ := by
    ext w
    rw [MonoidHom.mem_ker]
    change τ w * w = 1 ↔ τ w = w
    refine ⟨fun h => ?_, fun h => by rw [h]; exact hW2 w⟩
    exact (mul_eq_one_iff_eq_inv.1 h).trans (inv_eq_of_mul_eq_one_right (hW2 w))
  have hrange : ψ.range ≤ fixedSubgroup τ := by
    rintro _ ⟨w, rfl⟩
    change τ (τ w * w) = τ w * w
    rw [map_mul, hτ, mul_comm]
  have h1 := Subgroup.card_mul_index ψ.ker
  rw [Subgroup.index_ker, hker, hW] at h1
  have h2 := Subgroup.card_le_of_le hrange
  have h3 : 2 < Nat.card (fixedSubgroup τ) := by
    by_contra h
    have h4 : Nat.card (fixedSubgroup τ) ≤ 2 := not_lt.1 h
    have h5 := Nat.mul_le_mul h4 (h2.trans h4)
    omega
  have h4 : 2 < ((fixedSubgroup τ : Subgroup W) : Set W).ncard := by
    rw [← Nat.card_coe_set_eq]
    exact h3
  obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ := (Set.two_lt_ncard_iff (Set.toFinite _)).1 h4
  by_cases ha1 : a = 1
  · exact ⟨b, c, fun h => hab (ha1.trans h.symm), fun h => hac (ha1.trans h.symm), hbc, hb, hc⟩
  by_cases hb1 : b = 1
  · exact ⟨a, c, ha1, fun h => hbc (hb1.trans h.symm), hac, ha, hc⟩
  · exact ⟨a, b, ha1, hb1, hab, ha, hb⟩

private theorem pow_mul_mul_pow_eq {G : Type*} [Group G] {ρ τ : G} (h : ρ * τ * ρ = τ) (j : ℕ) :
    ρ ^ j * τ * ρ ^ j = τ := by
  induction j with
  | zero => simp
  | succ j ih =>
    have e1 : ρ ^ (j + 1) = ρ ^ j * ρ := pow_succ ρ j
    have e2 : ρ ^ (j + 1) = ρ * ρ ^ j := pow_succ' ρ j
    calc ρ ^ (j + 1) * τ * ρ ^ (j + 1) = ρ ^ j * ρ * τ * (ρ * ρ ^ j) := by rw [← e1, ← e2]
      _ = ρ ^ j * (ρ * τ * ρ) * ρ ^ j := by simp only [mul_assoc]
      _ = τ := by rw [h, ih]

private theorem false_of_dihedral_seven {W : Type*} [CommGroup W] [Finite W] [Nontrivial W]
    (hW2 : ∀ w : W, w * w = 1) (hW16 : Nat.card W ≤ 16) {ρ τ : MulAut W} (hρ : orderOf ρ = 7)
    (hfix : ∀ w : W, ρ w = w → w = 1) (hτ : ∀ w, τ (τ w) = w) (hρτ : ∀ w, ρ (τ (ρ w)) = τ w) :
    False := by
  have hW : Nat.card W = 8 := card_eq_eight hW2 hW16 hρ hfix
  obtain ⟨p, q, hp1, hq1, hpq, hp, hq⟩ := exists_two_fixed hW2 hW hτ
  have := Fintype.ofFinite W
  have hσ : orderOf (MulAut.toPerm W ρ) = 7 := by
    rw [orderOf_injective (MulAut.toPerm W) (fun f g h => MulEquiv.ext fun u => congr($h u))]
    exact hρ
  have hcyc : (MulAut.toPerm W ρ).IsCycle := by
    refine Equiv.Perm.isCycle_of_prime_order' (by rw [hσ]; exact Nat.prime_seven) ?_
    rw [hσ, ← Nat.card_eq_fintype_card, hW]
    norm_num
  have hmov : ∀ x : W, x ≠ 1 → MulAut.toPerm W ρ x ≠ x := fun x hx h => hx (hfix x h)
  obtain ⟨j, -, hj⟩ := (hcyc.sameCycle (hmov p hp1) (hmov q hq1)).exists_pow_eq'
  rw [← map_pow] at hj
  have h1 : (ρ ^ j * τ * ρ ^ j) p = τ p := by rw [pow_mul_mul_pow_eq (MulEquiv.ext hρτ) j]
  simp only [MulAut.mul_apply] at h1
  rw [show (ρ ^ j) p = q from hj, hq, hp] at h1
  have h2 : (ρ ^ (j + j)) p = p := by
    rw [pow_add, MulAut.mul_apply, show (ρ ^ j) p = q from hj, h1]
  have h3 : MulAut.toPerm W ρ ^ (j + j) = 1 :=
    (hcyc.pow_eq_one_iff' (hmov p hp1)).2 (by rw [← map_pow]; exact h2)
  have h4 : 7 ∣ j + j := hσ ▸ orderOf_dvd_of_pow_eq_one h3
  obtain ⟨k, hk⟩ : 7 ∣ j := by omega
  have hρ7 : ρ ^ 7 = 1 := by rw [← hρ]; exact pow_orderOf_eq_one ρ
  rw [hk, pow_mul, hρ7, one_pow] at hj
  exact hpq (by simpa using hj)

private noncomputable def restrictAut {G : Type*} [Group G] (W : Subgroup G) [Finite W]
    (f : MulAut G) (hf : ∀ w ∈ W, f w ∈ W) : MulAut W :=
  MulEquiv.ofBijective ((f.toMonoidHom.comp W.subtype).codRestrict W fun w => hf w w.2)
    (Finite.injective_iff_bijective.1 fun _ _ h =>
      Subtype.ext (f.injective (congrArg Subtype.val h)))

private theorem coe_restrictAut {G : Type*} [Group G] {W : Subgroup G} [Finite W]
    {f : MulAut G} (hf : ∀ w ∈ W, f w ∈ W) (w : W) :
    ((restrictAut W f hf w : W) : G) = f w := rfl

private theorem coe_restrictAut_pow {G : Type*} [Group G] {W : Subgroup G} [Finite W]
    {f : MulAut G} (hf : ∀ w ∈ W, f w ∈ W) (n : ℕ) (w : W) :
    ((((restrictAut W f hf) ^ n) w : W) : G) = (f ^ n) w := by
  induction n generalizing w with
  | zero => simp
  | succ n ih =>
    rw [pow_succ (restrictAut W f hf) n, MulAut.mul_apply, ih, coe_restrictAut, pow_succ f n,
      MulAut.mul_apply]

private theorem false_of_dihedral_seven_of_card_le {U : Type*} [CommGroup U] [Finite U]
    (hU2 : ∀ w : U, w * w = 1) (hU16 : Nat.card U ≤ 16) {ρ τ : MulAut U} (hρ : orderOf ρ = 7)
    (hτ : ∀ w, τ (τ w) = w) (hρτ : ∀ w, ρ (τ (ρ w)) = τ w) : False := by
  have hρ7 : ρ ^ 7 = 1 := by rw [← hρ]; exact pow_orderOf_eq_one ρ
  let φ : U →* U := MonoidHom.mk' (fun w => ρ w * w) fun a b => by
    rw [map_mul]
    exact mul_mul_mul_comm _ _ _ _
  have hφ : ∀ w, φ w = ρ w * w := fun w => rfl
  have hρW : ∀ w ∈ φ.range, ρ w ∈ φ.range := by
    rintro _ ⟨z, rfl⟩
    exact ⟨ρ z, by rw [hφ, hφ, map_mul]⟩
  have hτW : ∀ w ∈ φ.range, τ w ∈ φ.range := by
    rintro _ ⟨z, rfl⟩
    exact ⟨τ (ρ z), by rw [hφ, hφ, hρτ, map_mul, mul_comm]⟩
  have hfixW : ∀ w ∈ φ.range, ρ w = w → w = 1 := by
    rintro _ ⟨z, rfl⟩ hw
    have h1 : ρ z = φ z * z := by rw [hφ, mul_assoc, hU2, mul_one]
    have h2 : ∀ n : ℕ, (ρ ^ n) z = φ z ^ n * z := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        rw [pow_succ', MulAut.mul_apply, ih, map_mul, map_pow, hw, h1, pow_succ, mul_assoc]
    have h3 : (ρ ^ 7) z = z := by rw [hρ7]; rfl
    rw [h2] at h3
    have h4 : φ z ^ 7 = 1 := mul_right_cancel (h3.trans (one_mul z).symm)
    have h5 : φ z ^ 7 = φ z := by
      have e : φ z ^ 2 = 1 := by rw [pow_two]; exact hU2 _
      rw [show 7 = 2 * 3 + 1 from rfl, pow_succ, pow_mul, e, one_pow, one_mul]
    exact h5.symm.trans h4
  have hnt : Nontrivial φ.range := by
    by_contra hnt
    rw [not_nontrivial_iff_subsingleton] at hnt
    have hρ1 : ρ = 1 := by
      ext z
      have h1 : φ z = 1 := congrArg Subtype.val (Subsingleton.elim (⟨φ z, z, rfl⟩ : φ.range) 1)
      rw [hφ] at h1
      exact (mul_eq_one_iff_eq_inv.1 h1).trans (inv_eq_of_mul_eq_one_right (hU2 z))
    rw [hρ1, orderOf_one] at hρ
    exact absurd hρ (by norm_num)
  have hfixW' : ∀ w : φ.range, restrictAut φ.range ρ hρW w = w → w = 1 := fun w hw =>
    Subtype.ext (hfixW w w.2 (congrArg Subtype.val hw))
  have hρW7 : orderOf (restrictAut φ.range ρ hρW) = 7 := by
    have : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
    refine orderOf_eq_prime (MulEquiv.ext fun w => Subtype.ext
      (by rw [coe_restrictAut_pow, hρ7]; rfl)) fun h => ?_
    obtain ⟨w, hw⟩ := exists_ne (1 : φ.range)
    exact hw (hfixW' w (congrArg (· w) h))
  exact false_of_dihedral_seven (W := φ.range) (fun w => Subtype.ext (hU2 w))
    ((Subgroup.card_le_card_group _).trans hU16)
    (ρ := restrictAut φ.range ρ hρW) (τ := restrictAut φ.range τ hτW) hρW7 hfixW'
    (fun w => Subtype.ext (hτ w)) fun w => Subtype.ext (hρτ w)

private theorem not_seven_dvd_orderOf_conjRestrict {X : Type*} [Group X] {I U : Subgroup X}
    [Finite U] (hI : Sec3.IsElemTwo I) (hUI : U ≤ I) (hU16 : Nat.card U ≤ 16) {u v : X}
    (huu : u * u = 1) (hvv : v * v = 1) (hxU : ∀ w ∈ U, u * v * w * (u * v)⁻¹ ∈ U)
    (huU : ∀ w ∈ U, u * w * u⁻¹ ∈ U) : ¬ 7 ∣ orderOf (conjRestrict hxU) := by
  intro h7
  let _ : CommGroup U :=
    { (inferInstance : Group U) with
      mul_comm := fun a b => Subtype.ext (hI.1 a (hUI a.2) b (hUI b.2)) }
  obtain ⟨m, hm⟩ : ∃ m, orderOf (conjRestrict hxU ^ m) = 7 :=
    ⟨orderOf (conjRestrict hxU) / 7, orderOf_pow_orderOf_div (orderOf_pos _).ne' h7⟩
  have hxux : u * v * u * (u * v) = u := by
    calc u * v * u * (u * v) = u * v * (u * u) * v := by simp only [mul_assoc]
      _ = u := by rw [huu, mul_one, mul_assoc, hvv, mul_one]
  have hy := pow_mul_mul_pow_eq hxux m
  have hU2 : ∀ w : U, w * w = 1 := fun w => Subtype.ext (by simpa using hI.2 _ (hUI w.2))
  refine false_of_dihedral_seven_of_card_le hU2 hU16 hm (τ := conjRestrict huU)
    (fun w => Subtype.ext ?_) fun w => Subtype.ext ?_
  · rw [coe_conjRestrict, coe_conjRestrict]
    calc u * (u * w * u⁻¹) * u⁻¹ = (u * u) * w * (u * u)⁻¹ := by group
      _ = w := by rw [huu]; group
  · rw [coe_conjRestrict_pow, coe_conjRestrict, coe_conjRestrict_pow, coe_conjRestrict]
    generalize (u * v) ^ m = y at hy ⊢
    calc y * (u * (y * w * y⁻¹) * u⁻¹) * y⁻¹ = (y * u * y) * w * (y * u * y)⁻¹ := by group
      _ = u * w * u⁻¹ := by rw [hy]

end DihedralSeven

theorem exists_pow_mem_centralizer_odd_dvd_15 {X : Type*} [Group X] [Finite X]
    {I : Subgroup X} (hI : Sec3.IsElemTwo I) {u v : X} (hu : u ∈ normalizer (I : Set X))
    (hv : v ∈ normalizer (I : Set X)) (huu : u * u = 1) (hvv : v * v = 1)
    (hu4 : (centralizer ({u} : Set X)).relIndex I ≤ 4)
    (hv4 : (centralizer ({v} : Set X)).relIndex I ≤ 4) :
    ∃ N : ℕ, 0 < N ∧ (u * v) ^ (2 * N) ∈ centralizer (I : Set X) ∧
      ∀ m : ℕ, Odd m → m ∣ N → m ∣ 15 := by
  obtain ⟨U, hUI, hUab, hxU, hxI, huU⟩ := exists_subgroup_of_relIndex_le hI hu hv hu4 hv4
  have hU2 : IsPGroup 2 U := fun g => ⟨1, Subtype.ext (by simpa [pow_two] using hI.2 _ (hUI g.2))⟩
  obtain ⟨d, hd⟩ := IsPGroup.iff_card.1 hU2
  have h7 : ¬ 7 ∣ orderOf (conjRestrict hxU) :=
    not_seven_dvd_orderOf_conjRestrict hI hUI (by omega) huu hvv hxU huU
  refine ⟨orderOf (conjRestrict hxU), orderOf_pos _,
    pow_two_mul_mem_centralizer hI hUI (mul_mem hu hv) hxI fun w hw =>
      pow_orderOf_conjRestrict_conj_eq hxU hw, ?_⟩
  intro m hm hmN
  refine (Nat.dvd_iff_prime_pow_dvd_dvd 15 m).2 fun p k hp hpk => ?_
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.2 hm) (even_iff_two_dvd.2 ((dvd_pow_self 2 hk.ne').trans hpk))
  obtain ⟨e, he1, hed, hdvd⟩ :=
    prime_pow_dvd_two_pow_sub_one_of_dvd_orderOf hd (conjRestrict hxU) hp hp2 hk (hpk.trans hmN)
  have he4 : e ≤ 4 := by
    by_contra h
    have h5 : 2 ^ 5 ≤ 2 ^ d := Nat.pow_le_pow_right two_pos (by omega)
    omega
  by_cases he3 : e = 3
  · subst he3
    exfalso
    have hp7 : p = 7 :=
      (Nat.prime_dvd_prime_iff_eq hp Nat.prime_seven).1
        ((dvd_pow_self p hk.ne').trans (by simpa using hdvd))
    subst hp7
    exact h7 (((dvd_pow_self 7 hk.ne').trans hpk).trans hmN)
  · obtain rfl | rfl | rfl : e = 1 ∨ e = 2 ∨ e = 4 := by omega
    all_goals exact hdvd.trans (by norm_num)


section Closure

variable {X : Type*} [Group X] {I : Subgroup X}

private theorem mem_normalizer_of_range_commMap_le (hI : ∀ a ∈ I, ∀ b ∈ I, a * b = b * a)
    {g : X} (hg : g ∈ normalizer (I : Set X)) {U : Subgroup X} (hUI : U ≤ I)
    (hgU : (commMap hI hg).range ≤ U) : g ∈ normalizer (U : Set X) := by
  rw [mem_normalizer_iff]
  intro w
  constructor
  · intro hw
    have h1 : g * w * g⁻¹ = commMap hI hg ⟨w, hUI hw⟩ * w := by
      rw [commMap_apply]
      group
    rw [h1]
    exact U.mul_mem (hgU ⟨_, rfl⟩) hw
  · intro hw
    have hwI : w ∈ I := (mem_normalizer_iff.1 hg w).2 (hUI hw)
    have h1 : w = (commMap hI hg ⟨w, hwI⟩)⁻¹ * (g * w * g⁻¹) := by
      rw [commMap_apply]
      group
    rw [h1]
    exact U.mul_mem (U.inv_mem (hgU ⟨_, rfl⟩)) hw

variable (I) in
private def trivialMod (U : Subgroup X) : Subgroup X where
  carrier := {g | g ∈ normalizer (I : Set X) ∧ g ∈ normalizer (U : Set X) ∧
    ∀ x ∈ I, g * x * g⁻¹ * x⁻¹ ∈ U}
  mul_mem' := by
    rintro g h ⟨hgI, hgU, hg⟩ ⟨hhI, hhU, hh⟩
    refine ⟨mul_mem hgI hhI, mul_mem hgU hhU, fun x hx => ?_⟩
    rw [show g * h * x * (g * h)⁻¹ * x⁻¹ =
      g * (h * x * h⁻¹ * x⁻¹) * g⁻¹ * (g * x * g⁻¹ * x⁻¹) by group]
    exact U.mul_mem ((mem_normalizer_iff.1 hgU _).1 (hh x hx)) (hg x hx)
  one_mem' := ⟨one_mem _, one_mem _, fun x _ => by simp⟩
  inv_mem' := by
    rintro g ⟨hgI, hgU, hg⟩
    refine ⟨inv_mem hgI, inv_mem hgU, fun x hx => ?_⟩
    have hx' : g⁻¹ * x * g ∈ I := by
      have := (mem_normalizer_iff.1 (inv_mem hgI) x).1 hx
      rwa [inv_inv] at this
    rw [show g⁻¹ * x * g⁻¹⁻¹ * x⁻¹ = (g * (g⁻¹ * x * g) * g⁻¹ * (g⁻¹ * x * g)⁻¹)⁻¹ by group]
    exact U.inv_mem (hg _ hx')

private theorem natCard_finset_sup_le (hI : ∀ a ∈ I, ∀ b ∈ I, a * b = b * a) {ι : Type*}
    [DecidableEq ι] (s : Finset ι) (R : ι → Subgroup X) (hR : ∀ i ∈ s, R i ≤ I) :
    Nat.card ↥(s.sup R) ≤ ∏ i ∈ s, Nat.card (R i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.sup_insert, Finset.prod_insert hj]
    have hs : s.sup R ≤ I := Finset.sup_le fun i hi => hR i (Finset.mem_insert_of_mem hi)
    refine (natCard_sup_le fun p hp q hq =>
      hI p (hR j (Finset.mem_insert_self j s) hp) q (hs hq)).trans ?_
    exact Nat.mul_le_mul_left _ (ih fun i hi => hR i (Finset.mem_insert_of_mem hi))

end Closure

theorem exists_pow_mem_centralizer_closure_prime_pow {X : Type*} [Group X] [Finite X]
    {I : Subgroup X} (hI : Sec3.IsElemTwo I) {ι : Type*} [Fintype ι] (u : ι → X)
    (hu : ∀ i, u i ∈ normalizer (I : Set X)) (a : ι → ℕ)
    (hua : ∀ i, (centralizer ({u i} : Set X)).relIndex I ≤ a i) {y : X}
    (hy : y ∈ closure (Set.range u)) :
    ∃ N : ℕ, 0 < N ∧ y ^ (2 * N) ∈ centralizer (I : Set X) ∧
      ∀ p k : ℕ, p.Prime → p ≠ 2 → 1 ≤ k → p ^ k ∣ N →
        ∃ e, 1 ≤ e ∧ 2 ^ e ≤ ∏ i, a i ∧ p ^ k ∣ 2 ^ e - 1 := by
  classical
  have hc := hI.1
  set U : Subgroup X := Finset.univ.sup fun i => (commMap hc (hu i)).range with hUdef
  have hRU : ∀ i, (commMap hc (hu i)).range ≤ U := fun i =>
    Finset.le_sup (f := fun i => (commMap hc (hu i)).range) (Finset.mem_univ i)
  have hUI : U ≤ I := Finset.sup_le fun i _ => range_commMap_le hc (hu i)
  have hUcard : Nat.card U ≤ ∏ i, a i := by
    refine (natCard_finset_sup_le hc Finset.univ _ fun i _ => range_commMap_le hc (hu i)).trans ?_
    refine Finset.prod_le_prod' fun i _ => ?_
    rw [natCard_range_commMap]
    exact hua i
  have hle : closure (Set.range u) ≤ trivialMod I U := by
    rw [closure_le]
    rintro _ ⟨i, rfl⟩
    exact ⟨hu i, mem_normalizer_of_range_commMap_le hc (hu i) hUI (hRU i),
      fun x hx => hRU i ⟨⟨x, hx⟩, rfl⟩⟩
  obtain ⟨hyI, hyU, hyx⟩ := hle hy
  have hxU : ∀ w ∈ U, y * w * y⁻¹ ∈ U := fun w hw => (mem_normalizer_iff.1 hyU w).1 hw
  have hU2 : IsPGroup 2 U := fun g => ⟨1, Subtype.ext (by simpa [pow_two] using hI.2 _ (hUI g.2))⟩
  obtain ⟨d, hd⟩ := IsPGroup.iff_card.1 hU2
  refine ⟨orderOf (conjRestrict hxU), orderOf_pos _,
    pow_two_mul_mem_centralizer hI hUI hyI hyx fun w hw =>
      pow_orderOf_conjRestrict_conj_eq hxU hw, ?_⟩
  intro p k hp hp2 hk hdvd
  obtain ⟨e, he1, hed, hdvd'⟩ :=
    prime_pow_dvd_two_pow_sub_one_of_dvd_orderOf hd (conjRestrict hxU) hp hp2 hk hdvd
  exact ⟨e, he1, (Nat.pow_le_pow_right two_pos hed).trans (hd.symm.trans_le hUcard), hdvd'⟩

theorem exists_pow_mem_centralizer_closure_le_four {X : Type*} [Group X] [Finite X]
    {I : Subgroup X} (hI : Sec3.IsElemTwo I) {d : ℕ} (u : Fin d → X)
    (hu : ∀ i, u i ∈ normalizer (I : Set X))
    (hu4 : ∀ i, (centralizer ({u i} : Set X)).relIndex I ≤ 4) {y : X}
    (hy : y ∈ closure (Set.range u)) :
    ∃ N : ℕ, 0 < N ∧ y ^ (2 * N) ∈ centralizer (I : Set X) ∧
      ∀ p k : ℕ, p.Prime → p ≠ 2 → 1 ≤ k → p ^ k ∣ N →
        ∃ e, 1 ≤ e ∧ e ≤ 2 * d ∧ p ^ k ∣ 2 ^ e - 1 := by
  obtain ⟨N, hN, hpow, hprime⟩ :=
    exists_pow_mem_centralizer_closure_prime_pow hI u hu (fun _ => 4) hu4 hy
  refine ⟨N, hN, hpow, fun p k hp hp2 hk hdvd => ?_⟩
  obtain ⟨e, he1, he, hdvd'⟩ := hprime p k hp hp2 hk hdvd
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul] at he
  exact ⟨e, he1, (Nat.pow_le_pow_iff_right (by norm_num)).1 he, hdvd'⟩


theorem exists_subgroup_normalized_closure {X : Type*} [Group X] [Finite X] {I : Subgroup X}
    (hI : Sec3.IsElemTwo I) {ι : Type*} [Fintype ι] (u : ι → X)
    (hu : ∀ i, u i ∈ normalizer (I : Set X)) (a : ι → ℕ)
    (hua : ∀ i, (centralizer ({u i} : Set X)).relIndex I ≤ a i) :
    ∃ U : Subgroup X, U ≤ I ∧ Nat.card U ≤ ∏ i, a i ∧
      ∀ y ∈ closure (Set.range u), y ∈ normalizer (I : Set X) ∧ y ∈ normalizer (U : Set X) ∧
        ∀ x ∈ I, y * x * y⁻¹ * x⁻¹ ∈ U := by
  classical
  have hc := hI.1
  set U : Subgroup X := Finset.univ.sup fun i => (commMap hc (hu i)).range with hUdef
  have hRU : ∀ i, (commMap hc (hu i)).range ≤ U := fun i =>
    Finset.le_sup (f := fun i => (commMap hc (hu i)).range) (Finset.mem_univ i)
  have hUI : U ≤ I := Finset.sup_le fun i _ => range_commMap_le hc (hu i)
  have hUcard : Nat.card U ≤ ∏ i, a i := by
    refine (natCard_finset_sup_le hc Finset.univ _ fun i _ => range_commMap_le hc (hu i)).trans ?_
    refine Finset.prod_le_prod' fun i _ => ?_
    rw [natCard_range_commMap]
    exact hua i
  have hle : closure (Set.range u) ≤ trivialMod I U := by
    rw [closure_le]
    rintro _ ⟨i, rfl⟩
    exact ⟨hu i, mem_normalizer_of_range_commMap_le hc (hu i) hUI (hRU i),
      fun x hx => hRU i ⟨⟨x, hx⟩, rfl⟩⟩
  exact ⟨U, hUI, hUcard, fun y hy => hle hy⟩

theorem sq_mem_centralizer_of_centralizes {X : Type*} [Group X] {I U : Subgroup X}
    (hI : Sec3.IsElemTwo I) (hUI : U ≤ I) {y : X} (hy : y ∈ normalizer (I : Set X))
    (hyU : ∀ x ∈ I, y * x * y⁻¹ * x⁻¹ ∈ U) (hc : ∀ w ∈ U, y * w * y⁻¹ = w) :
    y ^ 2 ∈ centralizer (I : Set X) := by
  have h := pow_two_mul_mem_centralizer hI hUI hy hyU (n := 1) fun w hw => by
    rw [pow_one]
    exact hc w hw
  rwa [mul_one] at h

theorem exists_card_fixed_of_orderOf_eq_prime {U : Type*} [Group U] [Finite U] {d : ℕ}
    (hU : Nat.card U = 2 ^ d) (σ : MulAut U) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hσ : orderOf σ = p) :
    ∃ c, c < d ∧ Nat.card {u : U // σ u = u} = 2 ^ c ∧ p ∣ 2 ^ (d - c) - 1 := by
  have hτ : orderOf σ = p ^ (0 + 1) := by rw [hσ, zero_add, pow_one]
  have hne : σ ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hσ
    exact hp.one_lt.ne hσ
  set F : Subgroup U := fixedSubgroup σ with hFdef
  have hFtop : F ≠ ⊤ := by
    intro h
    apply hne
    ext w
    have hw : w ∈ F := by
      rw [h]
      exact Subgroup.mem_top w
    exact hw
  have hFd : Nat.card F ∣ 2 ^ d := by
    rw [← hU]
    exact Subgroup.card_subgroup_dvd_card F
  obtain ⟨c, hcd, hcF⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hFd
  have hlt : c < d := by
    refine lt_of_le_of_ne hcd ?_
    rintro rfl
    exact hFtop (Subgroup.eq_top_of_card_eq F (by rw [hcF, hU]))
  have hFn : (F : Set U).ncard = 2 ^ c := by
    rw [← Nat.card_coe_set_eq]
    exact hcF
  have hsum := Set.ncard_add_ncard_compl (F : Set U)
  rw [hFn, hU] at hsum
  have hcompl : ((F : Set U)ᶜ).ncard = 2 ^ c * (2 ^ (d - c) - 1) := by
    rw [Nat.mul_sub_one, ← pow_add, Nat.add_sub_cancel' hlt.le]
    omega
  have hcop : Nat.Coprime p (2 ^ c) :=
    Nat.Coprime.pow_right _ ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
  have hdvd := pow_dvd_ncard_compl_fixedSubgroup hp hτ
  rw [pow_zero, pow_one] at hdvd
  simp only [zero_add, pow_one] at hdvd
  rw [← hFdef, hcompl] at hdvd
  refine ⟨c, hlt, ?_, hcop.dvd_of_dvd_mul_left hdvd⟩
  rw [← hcF]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun _ => Iff.rfl)

end CFSG.RankThree.PartTwo.Sec20
