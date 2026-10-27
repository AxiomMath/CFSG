module

public import Mathlib.GroupTheory.Transfer
import CFSG.RankThree.Coprime.PrimeCubeTorsionExtension
public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.RankThree.PartTwo.Sec13

open Subgroup

section Transfer

variable {X : Type*} [Group X]

theorem conj_pow_eq_of_commute {g x : X} (h : Commute (g * x * g⁻¹) x) (j : ℕ) :
    g * x ^ j * g⁻¹ = (g * x * g⁻¹ * x⁻¹) ^ j * x ^ j := by
  have h1 : g * x ^ j * g⁻¹ = (g * x * g⁻¹) ^ j := by
    rw [← MulAut.conj_apply, map_pow, MulAut.conj_apply]
  have h2 : Commute (g * x * g⁻¹) x⁻¹ := h.inv_right
  rw [h1, h2.mul_pow, inv_pow, inv_mul_cancel_right]

theorem conj_eq_of_coprime_pow {p : ℕ} [hp : Fact p.Prime] {P : Subgroup X}
    (hP : IsPGroup p P) (hcomm : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x) {g : X}
    (hg : g ∈ normalizer (P : Set X)) {n : ℕ} (hn : ¬ p ∣ n)
    (hgn : ∀ x ∈ P, g ^ n * x * (g ^ n)⁻¹ = x)
    (hfix : ∀ x ∈ P, x ^ p = 1 → g * x * g⁻¹ = x) {x : X} (hx : x ∈ P) :
    g * x * g⁻¹ = x := by
  by_contra hne
  have hgx : g * x * g⁻¹ ∈ P := (mem_normalizer_iff.mp hg x).mp hx
  set y := g * x * g⁻¹ * x⁻¹ with hy
  have hyP : y ∈ P := mul_mem hgx (inv_mem hx)
  have hy1 : y ≠ 1 := fun h => hne (mul_inv_eq_one.mp h)
  obtain ⟨m, hm⟩ := (IsPGroup.iff_orderOf.mp hP) ⟨y, hyP⟩
  rw [Subgroup.orderOf_mk] at hm
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [pow_zero, orderOf_eq_one_iff] at hm
    exact hy1 hm
  set w := y ^ p ^ (m - 1) with hw
  have hwp : w ^ p = 1 := by
    rw [hw, ← pow_mul, ← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hm0), ← hm,
      pow_orderOf_eq_one]
  have hw1 : w ≠ 1 := by
    refine pow_ne_one_of_lt_orderOf (pow_ne_zero _ hp.out.ne_zero) ?_
    rw [hm]
    exact Nat.pow_lt_pow_right hp.out.one_lt (by omega)
  have hwP : w ∈ P := pow_mem hyP _
  have hgw : g * w * g⁻¹ = w := hfix w hwP hwp
  set x' := x ^ p ^ (m - 1) with hx'
  have hcx : Commute (g * x * g⁻¹) x := hcomm _ hgx _ hx
  have hgx' : g * x' * g⁻¹ = w * x' := by
    rw [hx', conj_pow_eq_of_commute hcx]
  have hind : ∀ i : ℕ, g ^ i * x' * (g ^ i)⁻¹ = w ^ i * x' := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      calc g ^ (i + 1) * x' * (g ^ (i + 1))⁻¹ = g * (g ^ i * x' * (g ^ i)⁻¹) * g⁻¹ := by
            rw [pow_succ', mul_inv_rev]; group
        _ = g * (w ^ i * x') * g⁻¹ := by rw [ih]
        _ = (g * w * g⁻¹) ^ i * (g * x' * g⁻¹) := by
            rw [← MulAut.conj_apply, map_mul, map_pow, MulAut.conj_apply, MulAut.conj_apply]
        _ = w ^ (i + 1) * x' := by rw [hgw, hgx', pow_succ, mul_assoc]
  have hwn : w ^ n = 1 := by
    have h := hind n
    rw [hgn x' (pow_mem hx _)] at h
    exact (mul_eq_right.mp h.symm)
  have hcop : Nat.Coprime p n := (Nat.Prime.coprime_iff_not_dvd hp.out).mpr hn
  have : w ^ (Nat.gcd p n) = 1 := pow_gcd_eq_one.mpr ⟨hwp, hwn⟩
  rw [hcop, pow_one] at this
  exact hw1 this


theorem mul_comm_of_isCyclic {P : Subgroup X} [IsCyclic P] {x y : X} (hx : x ∈ P)
    (hy : y ∈ P) : x * y = y * x := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := P)
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨x, hx⟩)
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨y, hy⟩)
  have : (⟨x, hx⟩ : P) * ⟨y, hy⟩ = ⟨y, hy⟩ * ⟨x, hx⟩ := by
    rw [← hi, ← hj]
    exact zpow_mul_comm g i j
  exact congrArg Subtype.val this

theorem not_three_dvd_card_of_forall_pow_three_mem [Finite X] (hX : Group.IsPerfect X)
    (Z : Subgroup X) (hZc : Z ≤ center X) (hZ : Nat.card Z ≤ 3)
    (h : ∀ x : X, x ^ 3 = 1 → x ∈ Z) : ¬ 3 ∣ Nat.card X := by
  intro h3
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P⟩ : Nonempty (Sylow 3 X) := inferInstance
  have hcyc : IsCyclic (⊤ : Subgroup (P : Subgroup X)) := by
    refine CFSG.RankThree.Coprime.isCyclic_of_forall_pow_eq_one_mem (by norm_num) P.isPGroup' ⊤
      (Z.subgroupOf P) ?_ ?_
    · calc Nat.card (Z.subgroupOf (P : Subgroup X)) ≤ Nat.card Z :=
            Nat.card_le_card_of_injective (fun z => (⟨(z : P), z.2⟩ : Z))
              (fun a b hab => Subtype.ext (Subtype.ext (congrArg Subtype.val hab :)))
        _ ≤ 3 := hZ
    · intro x _ hx
      rw [mem_subgroupOf]
      refine h x ?_
      rw [← Subgroup.coe_pow, hx, Subgroup.coe_one]
  have : IsCyclic (P : Subgroup X) :=
    isCyclic_of_surjective Subgroup.topEquiv.toMonoidHom Subgroup.topEquiv.surjective
  have hcomm : ∀ x ∈ (P : Subgroup X), ∀ y ∈ (P : Subgroup X), x * y = y * x :=
    fun x hx y hy => mul_comm_of_isCyclic hx hy
  have hNC : normalizer (P : Set X) ≤ centralizer (P : Set X) := by
    intro g hg
    rw [mem_centralizer_iff]
    intro x hx
    set N := normalizer (P : Set X)
    set n := (P : Subgroup X).relIndex N
    have hn : ¬ 3 ∣ n := fun hd => P.not_dvd_index (hd.trans
      (Subgroup.relIndex_dvd_index_of_le Subgroup.le_normalizer))
    have hgn : g ^ n ∈ (P : Subgroup X) := by
      have : ((P : Subgroup X).subgroupOf N).Normal := Subgroup.normal_in_normalizer
      have h1 := Subgroup.pow_index_mem ((P : Subgroup X).subgroupOf N) (⟨g, hg⟩ : N)
      rw [mem_subgroupOf] at h1
      exact h1
    have key := conj_eq_of_coprime_pow P.isPGroup' hcomm hg hn
      (fun y hy => by rw [hcomm _ hgn y hy, mul_inv_cancel_right])
      (fun y _ hy3 => by
        have hyc := Subgroup.mem_center_iff.mp (hZc (h y hy3)) g
        rw [hyc, mul_inv_cancel_right]) hx
    rw [mul_inv_eq_iff_eq_mul] at key
    exact key.symm
  have hcompl := MonoidHom.ker_transferSylow_isComplement' P hNC
  have hker : (MonoidHom.transferSylow P hNC).ker = ⊤ := by
    rw [eq_top_iff, ← hX.commutator_eq_top, _root_.commutator_def, Subgroup.commutator_le]
    intro a _ b _
    simp only [MonoidHom.mem_ker, commutatorElement_def, map_mul, map_inv]
    have hab : MonoidHom.transferSylow P hNC a * MonoidHom.transferSylow P hNC b =
        MonoidHom.transferSylow P hNC b * MonoidHom.transferSylow P hNC a :=
      Subtype.ext (hcomm _ (MonoidHom.transferSylow P hNC a).2 _
        (MonoidHom.transferSylow P hNC b).2)
    rw [hab]
    group
  rw [hker] at hcompl
  have hcard := hcompl.card_mul_card
  rw [Subgroup.card_top] at hcard
  have hP1 : Nat.card (P : Subgroup X) = 1 := by
    have hpos : 0 < Nat.card X := Nat.card_pos
    nlinarith
  exact P.ne_bot_of_dvd_card h3 (Subgroup.eq_bot_of_card_eq _ hP1)

end Transfer

end CFSG.RankThree.PartTwo.Sec13
