module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Suzuki.V.proposition_1_2
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Suzuki.V.theorem_2_10
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Suzuki.V.theorem_2_27
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Suzuki.VI.formula_1_7
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Suzuki.VI.theorem_1_8
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection1.PFsection1_7_Core
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Suzuki.VI.formula_1_15
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Suzuki.VI.definition_2_7
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Suzuki.VI.proposition_2_8
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Suzuki.VI.proposition_2_9
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.Defs
public import Mathlib.GroupTheory.SpecificGroups.Quaternion
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.Basic
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.PLengthLemmas
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection1.PFsection1_9
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection3.PFsection3_5
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection5.PFsection5_9
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

attribute [local simp] Representation.isTrivial_def

/-!
# Suzuki Chapter 6, Section 2.2, Example 3

The Brauer--Suzuki theorem in the strong form proved in the example.
-/

namespace CFSG.BenderSuzuki
namespace External
namespace Suzuki
namespace VI

universe u

open IsCyclotomicExtension
open scoped Cyclotomic
open scoped Pointwise
open PFAppendixIII

private lemma quaternionGroup_isInvolution_a_parameter
    (m : ℕ) [NeZero m] :
    IsInvolution
      (QuaternionGroup.a (m : ZMod (2 * m)) : QuaternionGroup m) := by
  have hm_pos : 0 < m := NeZero.pos m
  have hm_lt : m < 2 * m := by omega
  constructor
  · intro h_one
    rw [QuaternionGroup.one_def] at h_one
    have hm_zero : (m : ZMod (2 * m)) = 0 := QuaternionGroup.a.inj h_one
    have hm_val_zero := congrArg ZMod.val hm_zero
    simp [ZMod.val_natCast, Nat.mod_eq_of_lt hm_lt] at hm_val_zero
    exact (NeZero.ne m) hm_val_zero
  · rw [sq, QuaternionGroup.a_mul_a, QuaternionGroup.one_def]
    congr 1
    calc
      (m : ZMod (2 * m)) + m = ((2 * m : ℕ) : ZMod (2 * m)) := by
        norm_num [two_mul]
      _ = 0 := ZMod.natCast_self (2 * m)

private lemma quaternionGroup_eq_a_parameter_of_isInvolution
    (m : ℕ) [NeZero m] {q : QuaternionGroup m} (hq : IsInvolution q) :
    q = QuaternionGroup.a (m : ZMod (2 * m)) := by
  have hm_pos : 0 < m := NeZero.pos m
  have hm_lt : m < 2 * m := by omega
  cases q with
  | xa i =>
      have horder_two : orderOf (QuaternionGroup.xa i : QuaternionGroup m) = 2 :=
        orderOf_eq_prime hq.sq_eq_one hq.ne_one
      rw [QuaternionGroup.orderOf_xa] at horder_two
      omega
  | a i =>
      have horder_two : orderOf (QuaternionGroup.a i : QuaternionGroup m) = 2 :=
        orderOf_eq_prime hq.sq_eq_one hq.ne_one
      rw [QuaternionGroup.orderOf_a] at horder_two
      have hdiv_mul :=
        Nat.div_mul_cancel (Nat.gcd_dvd_left (2 * m) i.val)
      rw [horder_two] at hdiv_mul
      have hgcd : Nat.gcd (2 * m) i.val = m := by omega
      have hm_dvd_i : m ∣ i.val := by
        obtain ⟨k, hk⟩ := Nat.gcd_dvd_right (2 * m) i.val
        refine ⟨k, ?_⟩
        calc
          i.val = Nat.gcd (2 * m) i.val * k := hk
          _ = m * k := by rw [hgcd]
      obtain ⟨k, hk⟩ := hm_dvd_i
      have hi_lt : i.val < 2 * m := ZMod.val_lt i
      have hi_ne_zero : i.val ≠ 0 := by
        intro hi_zero
        apply hq.ne_one
        rw [QuaternionGroup.one_def]
        congr 1
        exact (ZMod.val_eq_zero i).mp hi_zero
      have hk_ne_zero : k ≠ 0 := by
        intro hk_zero
        apply hi_ne_zero
        simp [hk, hk_zero]
      have hk_lt_two : k < 2 := by
        apply (Nat.mul_lt_mul_right hm_pos).mp
        simpa [Nat.mul_comm, hk] using hi_lt
      have hk_eq : k = 1 := by omega
      congr 1
      apply ZMod.val_injective
      simp [hk, hk_eq, ZMod.val_natCast, Nat.mod_eq_of_lt hm_lt]

private lemma quaternionGroup_center_eq_zpowers_a_parameter
    (m : ℕ) [NeZero m] (hm : 2 ≤ m) :
    Subgroup.center (QuaternionGroup m) =
      Subgroup.zpowers
        (QuaternionGroup.a (m : ZMod (2 * m)) : QuaternionGroup m) := by
  let t : QuaternionGroup m := QuaternionGroup.a (m : ZMod (2 * m))
  have ht : IsInvolution t := quaternionGroup_isInvolution_a_parameter m
  apply le_antisymm
  · intro q hq
    cases q with
    | a i =>
        by_cases h_one : (QuaternionGroup.a i : QuaternionGroup m) = 1
        · rw [h_one]
          exact Subgroup.one_mem (Subgroup.zpowers t)
        · have hcomm :=
            (Subgroup.mem_center_iff.mp hq)
              (QuaternionGroup.xa 0 : QuaternionGroup m)
          simp only [QuaternionGroup.xa_mul_a, QuaternionGroup.a_mul_xa] at hcomm
          have hi : i = -i := by
            simpa using QuaternionGroup.xa.inj hcomm
          have hi_sq : i + i = 0 := by linear_combination hi
          have hsq : (QuaternionGroup.a i : QuaternionGroup m) ^ 2 = 1 := by
            rw [sq, QuaternionGroup.a_mul_a, QuaternionGroup.one_def]
            congr 1
          have h_inv : IsInvolution (QuaternionGroup.a i : QuaternionGroup m) :=
            ⟨h_one, hsq⟩
          have h_eq : (QuaternionGroup.a i : QuaternionGroup m) = t :=
            quaternionGroup_eq_a_parameter_of_isInvolution m h_inv
          rw [h_eq]
          exact Subgroup.mem_zpowers t
    | xa i =>
        have hcomm :=
          (Subgroup.mem_center_iff.mp hq)
            (QuaternionGroup.a 1 : QuaternionGroup m)
        simp only [QuaternionGroup.a_mul_xa, QuaternionGroup.xa_mul_a] at hcomm
        have hi : i - 1 = i + 1 := QuaternionGroup.xa.inj hcomm
        have hneg_one : -(1 : ZMod (2 * m)) = 1 := by
          have hi' := congrArg (fun z : ZMod (2 * m) => z - i) hi
          simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hi'
        have htwo : (2 : ZMod (2 * m)) = 0 := by
          calc
            (2 : ZMod (2 * m)) = 1 + 1 := by norm_num
            _ = -(1 : ZMod (2 * m)) + 1 :=
              congrArg (fun z : ZMod (2 * m) => z + 1) hneg_one.symm
            _ = 0 := neg_add_cancel 1
        have htwo_lt : 2 < 2 * m := by omega
        have hval_two : ZMod.val (2 : ZMod (2 * m)) = 2 := by
          exact ZMod.val_natCast_of_lt htwo_lt
        have hval := congrArg ZMod.val htwo
        rw [hval_two] at hval
        simp at hval
  · apply Subgroup.zpowers_le.mpr
    rw [Subgroup.mem_center_iff]
    intro q
    cases q with
    | a i =>
        simp only [QuaternionGroup.a_mul_a]
        congr 1
        exact add_comm i (m : ZMod (2 * m))
    | xa i =>
        simp only [QuaternionGroup.xa_mul_a, QuaternionGroup.a_mul_xa]
        congr 1
        have hm_cast : (2 : ZMod (2 * m)) * m = 0 := by
          have hm_cast_nat := ZMod.natCast_self (2 * m)
          rw [Nat.cast_mul] at hm_cast_nat
          exact hm_cast_nat
        linear_combination hm_cast

private lemma quaternionGroup_orderOf_a_one_pow_half_parameter
    (k : ℕ) [NeZero k] :
    orderOf
        ((QuaternionGroup.a 1 : QuaternionGroup (2 * k)) ^ k) = 4 := by
  have hk_pos : 0 < k := NeZero.pos k
  have hk_dvd :
      k ∣ orderOf (QuaternionGroup.a 1 : QuaternionGroup (2 * k)) := by
    rw [QuaternionGroup.orderOf_a_one]
    refine ⟨4, ?_⟩
    omega
  rw [orderOf_pow_of_dvd (NeZero.ne k) hk_dvd,
    QuaternionGroup.orderOf_a_one]
  have hfactor : 2 * (2 * k) = 4 * k := by omega
  rw [hfactor]
  simpa [Nat.mul_comm] using Nat.mul_div_right 4 hk_pos

private lemma quaternionGroup_orderFourSubgroup_le_a_one
    (k : ℕ) [NeZero k] :
    Subgroup.zpowers
        ((QuaternionGroup.a 1 : QuaternionGroup (2 * k)) ^ k) ≤
      Subgroup.zpowers (QuaternionGroup.a 1 : QuaternionGroup (2 * k)) := by
  apply Subgroup.zpowers_le.mpr
  exact (Subgroup.zpowers (QuaternionGroup.a 1 : QuaternionGroup (2 * k))).pow_mem
    (Subgroup.mem_zpowers _) k

private lemma quaternionGroup_orderFourSubgroup_eq_of_le_a_one
    (k : ℕ) [NeZero k] (V : Subgroup (QuaternionGroup (2 * k)))
    (hV_le : V ≤ Subgroup.zpowers
      (QuaternionGroup.a 1 : QuaternionGroup (2 * k)))
    (hVcard : Nat.card V = 4) :
    V = Subgroup.zpowers
      ((QuaternionGroup.a 1 : QuaternionGroup (2 * k)) ^ k) := by
  let a1 : QuaternionGroup (2 * k) := QuaternionGroup.a 1
  let U0 : Subgroup (QuaternionGroup (2 * k)) := Subgroup.zpowers (a1 ^ k)
  have hV_le_U0 : V ≤ U0 := by
    intro v hv
    have hvX : v ∈ Subgroup.zpowers a1 := hV_le hv
    rw [mem_zpowers_iff_mem_range_orderOf] at hvX
    rcases Finset.mem_image.mp hvX with ⟨i, _hi, hiv⟩
    have hvord : orderOf v ∣ 4 := by
      rw [← hVcard]
      exact V.orderOf_dvd_natCard hv
    have hvpow : v ^ 4 = 1 := orderOf_dvd_iff_pow_eq_one.mp hvord
    have hgenpow : a1 ^ (i * 4) = 1 := by
      rw [pow_mul, hiv]
      exact hvpow
    have hdvd : 2 * (2 * k) ∣ i * 4 := by
      rw [← QuaternionGroup.orderOf_a_one]
      exact orderOf_dvd_iff_pow_eq_one.mpr hgenpow
    rcases hdvd with ⟨d, hd⟩
    have hmul : i * 4 = (k * d) * 4 := by
      calc
        i * 4 = 2 * (2 * k) * d := hd
        _ = (k * d) * 4 := by ring
    have hi : i = k * d :=
      Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 4) hmul
    change v ∈ Subgroup.zpowers (a1 ^ k)
    rw [← hiv]
    have hpowmem : (a1 ^ k) ^ d ∈ Subgroup.zpowers (a1 ^ k) :=
      (Subgroup.zpowers (a1 ^ k)).pow_mem (Subgroup.mem_zpowers _) d
    simp [pow_mul, hi] at hpowmem ⊢
  change V = U0
  apply Subgroup.eq_of_le_of_card_ge hV_le_U0
  rw [hVcard, Nat.card_zpowers,
    quaternionGroup_orderOf_a_one_pow_half_parameter]

private lemma quaternionGroup_orderFourSubgroup_normal
    (k : ℕ) [NeZero k] :
    (Subgroup.zpowers
      ((QuaternionGroup.a 1 : QuaternionGroup (2 * k)) ^ k)).Normal := by
  let u : QuaternionGroup (2 * k) :=
    (QuaternionGroup.a 1 : QuaternionGroup (2 * k)) ^ k
  constructor
  intro z hz q
  rcases Subgroup.mem_zpowers_iff.mp hz with ⟨r, rfl⟩
  have hgen : q * u * q⁻¹ ∈ Subgroup.zpowers u := by
    cases q with
    | a i =>
        have hcomm : Commute (QuaternionGroup.a i : QuaternionGroup (2 * k)) u := by
          rw [show u = QuaternionGroup.a
            (k : ZMod (2 * (2 * k))) by
              simp [u, QuaternionGroup.a_one_pow], commute_iff_eq]
          simp only [QuaternionGroup.a_mul_a]
          congr 1
          exact add_comm _ _
        have hconj :
            (QuaternionGroup.a i : QuaternionGroup (2 * k)) * u *
                (QuaternionGroup.a i : QuaternionGroup (2 * k))⁻¹ = u := by
          calc
            (QuaternionGroup.a i : QuaternionGroup (2 * k)) * u *
                (QuaternionGroup.a i : QuaternionGroup (2 * k))⁻¹ =
              u * (QuaternionGroup.a i : QuaternionGroup (2 * k)) *
                (QuaternionGroup.a i : QuaternionGroup (2 * k))⁻¹ := by
                  rw [hcomm.eq]
            _ = u := by simp
        rw [hconj]
        exact Subgroup.mem_zpowers u
    | xa i =>
        have hrel :
            (QuaternionGroup.xa i : QuaternionGroup (2 * k)) * u =
              u⁻¹ * QuaternionGroup.xa i := by
          rw [show u = QuaternionGroup.a
            (k : ZMod (2 * (2 * k))) by
              simp [u, QuaternionGroup.a_one_pow]]
          simp only [QuaternionGroup.xa_mul_a]
          congr 1
          ring
        have hconj :
            (QuaternionGroup.xa i : QuaternionGroup (2 * k)) * u *
                (QuaternionGroup.xa i : QuaternionGroup (2 * k))⁻¹ = u⁻¹ := by
          calc
            (QuaternionGroup.xa i : QuaternionGroup (2 * k)) * u *
                (QuaternionGroup.xa i : QuaternionGroup (2 * k))⁻¹ =
              u⁻¹ * (QuaternionGroup.xa i : QuaternionGroup (2 * k)) *
                (QuaternionGroup.xa i : QuaternionGroup (2 * k))⁻¹ := by
                  rw [hrel]
            _ = u⁻¹ := by simp
        rw [hconj]
        exact (Subgroup.zpowers u).inv_mem (Subgroup.mem_zpowers u)
  change (MulAut.conj q) (u ^ r) ∈ Subgroup.zpowers u
  rw [map_zpow]
  exact (Subgroup.zpowers u).zpow_mem hgen r

private lemma quaternionGroup_conj_eq_inv_of_not_mem_a_one
    (m : ℕ) [NeZero m] (y : QuaternionGroup m)
    (hy : y ∉ Subgroup.zpowers
      (QuaternionGroup.a 1 : QuaternionGroup m))
    {x : QuaternionGroup m}
    (hx : x ∈ Subgroup.zpowers
      (QuaternionGroup.a 1 : QuaternionGroup m)) :
    y * x * y⁻¹ = x⁻¹ := by
  rcases Subgroup.mem_zpowers_iff.mp hx with ⟨r, rfl⟩
  cases y with
  | a i =>
      exfalso
      apply hy
      have hi :
          (QuaternionGroup.a i : QuaternionGroup m) =
            (QuaternionGroup.a 1 : QuaternionGroup m) ^ i.val := by
        rw [QuaternionGroup.a_one_pow]
        congr 1
        exact (ZMod.natCast_zmod_val i).symm
      rw [hi]
      exact (Subgroup.zpowers _).pow_mem (Subgroup.mem_zpowers _) i.val
  | xa i =>
      have hrel :
          (QuaternionGroup.xa i : QuaternionGroup m) *
              (QuaternionGroup.a 1 : QuaternionGroup m) =
            (QuaternionGroup.a 1 : QuaternionGroup m)⁻¹ *
              QuaternionGroup.xa i := by
        simp only [QuaternionGroup.xa_mul_a]
        congr 1
        ring
      have hgen :
          (QuaternionGroup.xa i : QuaternionGroup m) *
              (QuaternionGroup.a 1 : QuaternionGroup m) *
              (QuaternionGroup.xa i : QuaternionGroup m)⁻¹ =
            (QuaternionGroup.a 1 : QuaternionGroup m)⁻¹ := by
        calc
          _ = (QuaternionGroup.a 1 : QuaternionGroup m)⁻¹ *
                (QuaternionGroup.xa i : QuaternionGroup m) *
                (QuaternionGroup.xa i : QuaternionGroup m)⁻¹ := by rw [hrel]
          _ = _ := by simp
      change (MulAut.conj (QuaternionGroup.xa i : QuaternionGroup m))
          ((QuaternionGroup.a 1 : QuaternionGroup m) ^ r) =
        ((QuaternionGroup.a 1 : QuaternionGroup m) ^ r)⁻¹
      have hgen'':
          (MulAut.conj (QuaternionGroup.xa i : QuaternionGroup m))
              (QuaternionGroup.a 1 : QuaternionGroup m) =
            (QuaternionGroup.a 1 : QuaternionGroup m)⁻¹ := hgen
      rw [map_zpow, hgen'', inv_zpow]

private lemma quaternionGroup_center_le_orderFourSubgroup
    (k : ℕ) [NeZero k] :
    Subgroup.center (QuaternionGroup (2 * k)) ≤
      Subgroup.zpowers
        ((QuaternionGroup.a 1 : QuaternionGroup (2 * k)) ^ k) := by
  have hk_pos : 0 < k := NeZero.pos k
  rw [quaternionGroup_center_eq_zpowers_a_parameter (2 * k) (by omega)]
  apply Subgroup.zpowers_le.mpr
  have ht :
      (QuaternionGroup.a ((2 * k : ℕ) : ZMod (2 * (2 * k))) :
          QuaternionGroup (2 * k)) =
        (QuaternionGroup.a 1 : QuaternionGroup (2 * k)) ^ (2 * k) := by
    rw [QuaternionGroup.a_one_pow]
  rw [ht]
  have hpow :
      (QuaternionGroup.a 1 : QuaternionGroup (2 * k)) ^ (2 * k) =
        ((QuaternionGroup.a 1 : QuaternionGroup (2 * k)) ^ k) ^ 2 := by
    calc
      (QuaternionGroup.a 1 : QuaternionGroup (2 * k)) ^ (2 * k) =
          (QuaternionGroup.a 1 : QuaternionGroup (2 * k)) ^ (k * 2) := by
            exact congrArg
              (fun e : ℕ =>
                (QuaternionGroup.a 1 : QuaternionGroup (2 * k)) ^ e)
              (Nat.mul_comm 2 k)
      _ = ((QuaternionGroup.a 1 : QuaternionGroup (2 * k)) ^ k) ^ 2 :=
        pow_mul _ k 2
  rw [hpow]
  exact (Subgroup.zpowers
      ((QuaternionGroup.a 1 : QuaternionGroup (2 * k)) ^ k)).pow_mem
    (Subgroup.mem_zpowers _) 2

private lemma generalizedQuaternion_source_subgroups
    {P : Type u} [Group P] [Finite P]
    {n : ℕ} (hn : 3 ≤ n)
    (e : P ≃* QuaternionGroup (2 ^ (n - 2))) :
    ∃ X U T : Subgroup P,
      IsCyclic X ∧ U.Normal ∧ U ≤ X ∧ T ≤ U ∧
      Nat.card U = 4 ∧ Nat.card T = 2 ∧
      Nat.card P = 2 * Nat.card X ∧ Subgroup.center P = T ∧
      (∀ V : Subgroup P, V ≤ X → Nat.card V = 4 → V = U) ∧
      (∀ y : P, y ∉ X → ∀ x : P, x ∈ X → y * x * y⁻¹ = x⁻¹) ∧
      ∀ t : P, orderOf t = 2 → t ∈ T := by
  let k : ℕ := 2 ^ (n - 3)
  have hk_pos : 0 < k := by positivity
  let : NeZero k := ⟨hk_pos.ne'⟩
  have hm : 2 ^ (n - 2) = 2 * k := by
    have hsub : n - 2 = (n - 3) + 1 := by omega
    rw [hsub, pow_succ]
    simp [k, Nat.mul_comm]
  rw [hm] at e
  let X0 : Subgroup (QuaternionGroup (2 * k)) :=
    Subgroup.zpowers (QuaternionGroup.a 1 : QuaternionGroup (2 * k))
  let U0 : Subgroup (QuaternionGroup (2 * k)) :=
    Subgroup.zpowers
      ((QuaternionGroup.a 1 : QuaternionGroup (2 * k)) ^ k)
  let T0 : Subgroup (QuaternionGroup (2 * k)) :=
    Subgroup.center (QuaternionGroup (2 * k))
  let X : Subgroup P := X0.map e.symm.toMonoidHom
  let U : Subgroup P := U0.map e.symm.toMonoidHom
  let T : Subgroup P := T0.map e.symm.toMonoidHom
  refine ⟨X, U, T, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact isCyclic_of_surjective (e.symm.subgroupMap X0)
      (e.symm.subgroupMap X0).surjective
  · exact (quaternionGroup_orderFourSubgroup_normal k).map
      e.symm.toMonoidHom e.symm.surjective
  · exact Subgroup.map_mono (quaternionGroup_orderFourSubgroup_le_a_one k)
  · exact Subgroup.map_mono (quaternionGroup_center_le_orderFourSubgroup k)
  · have hcard0 : Nat.card U0 = 4 := by
      rw [Nat.card_zpowers]
      exact quaternionGroup_orderOf_a_one_pow_half_parameter k
    calc
      Nat.card U = Nat.card U0 :=
        (Nat.card_congr (e.symm.subgroupMap U0).toEquiv).symm
      _ = 4 := hcard0
  · have ht : IsInvolution
        (QuaternionGroup.a ((2 * k : ℕ) : ZMod (2 * (2 * k))) :
          QuaternionGroup (2 * k)) :=
      quaternionGroup_isInvolution_a_parameter (2 * k)
    have ht_order : orderOf
        (QuaternionGroup.a ((2 * k : ℕ) : ZMod (2 * (2 * k))) :
          QuaternionGroup (2 * k)) = 2 :=
      orderOf_eq_prime ht.sq_eq_one ht.ne_one
    have hcard0 : Nat.card T0 = 2 := by
      change Nat.card (Subgroup.center (QuaternionGroup (2 * k))) = 2
      rw [quaternionGroup_center_eq_zpowers_a_parameter (2 * k) (by omega),
        Nat.card_zpowers, ht_order]
    calc
      Nat.card T = Nat.card T0 :=
        (Nat.card_congr (e.symm.subgroupMap T0).toEquiv).symm
      _ = 2 := hcard0
  · have hPcard : Nat.card P = Nat.card (QuaternionGroup (2 * k)) :=
      Nat.card_congr e.toEquiv
    have hXcard0 : Nat.card X0 = 2 * (2 * k) := by
      change Nat.card
          (Subgroup.zpowers
            (QuaternionGroup.a 1 : QuaternionGroup (2 * k))) = 2 * (2 * k)
      rw [Nat.card_zpowers, QuaternionGroup.orderOf_a_one]
    have hXcard : Nat.card X = 2 * (2 * k) := by
      calc
        Nat.card X = Nat.card X0 :=
          (Nat.card_congr (e.symm.subgroupMap X0).toEquiv).symm
        _ = 2 * (2 * k) := hXcard0
    rw [hPcard, show Nat.card (QuaternionGroup (2 * k)) = 4 * (2 * k) by
      rw [Nat.card_eq_fintype_card, QuaternionGroup.card], hXcard]
    ring
  · ext p
    constructor
    · intro hp
      refine ⟨e p, ?_, e.symm_apply_apply p⟩
      exact (MulEquivClass.apply_mem_center_iff e).2 hp
    · rintro ⟨q, hq, rfl⟩
      apply (MulEquivClass.apply_mem_center_iff e).1
      change e (e.symm q) ∈ Set.center (QuaternionGroup (2 * k))
      rw [e.apply_symm_apply]
      change q ∈ Subgroup.center (QuaternionGroup (2 * k)) at hq
      rw [← Subgroup.coe_center]
      exact hq
  · intro V hV_le hVcard
    let V0 : Subgroup (QuaternionGroup (2 * k)) := V.map e.toMonoidHom
    have hV0_le : V0 ≤ X0 := by
      intro v hv
      rcases hv with ⟨p, hp, rfl⟩
      have hpX : p ∈ X := hV_le hp
      rcases hpX with ⟨x, hx, hxp⟩
      have heq : e p = x := by
        rw [← hxp]
        simp
      simpa [heq] using hx
    have hV0card : Nat.card V0 = 4 := by
      calc
        Nat.card V0 = Nat.card V := Subgroup.card_map_of_injective e.injective
        _ = 4 := hVcard
    have hV0eq : V0 = U0 :=
      quaternionGroup_orderFourSubgroup_eq_of_le_a_one k V0 hV0_le hV0card
    apply (Subgroup.map_injective (f := e.toMonoidHom) e.injective)
    calc
      V.map e.toMonoidHom = V0 := rfl
      _ = U0 := hV0eq
      _ = U.map e.toMonoidHom := by
        symm
        ext x
        constructor
        · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
          simpa using hz
        · intro hx
          refine ⟨e.symm x, ⟨x, hx, by simp⟩, by simp⟩
  · intro y hy x hx
    have hey_not : e y ∉ X0 := by
      intro hey
      apply hy
      exact ⟨e y, hey, e.symm_apply_apply y⟩
    have hex : e x ∈ X0 := by
      rcases hx with ⟨z, hz, hzx⟩
      have heq : e x = z := by
        rw [← hzx]
        simp
      simpa [heq] using hz
    have hconj : e y * e x * (e y)⁻¹ = (e x)⁻¹ :=
      quaternionGroup_conj_eq_inv_of_not_mem_a_one
        (2 * k) (e y) hey_not hex
    apply e.injective
    simpa using hconj
  · intro t htorder
    have hetorder : orderOf (e t) = 2 := by
      rw [e.orderOf_eq t, htorder]
    have hetI : IsInvolution (e t) := by
      have hpow_ne :=
        (orderOf_eq_prime_iff (x := e t) (p := 2)).mp hetorder
      exact ⟨hpow_ne.2, hpow_ne.1⟩
    have heteq := quaternionGroup_eq_a_parameter_of_isInvolution
      (2 * k) hetI
    have hetT0 : e t ∈ T0 := by
      change e t ∈ Subgroup.center (QuaternionGroup (2 * k))
      rw [quaternionGroup_center_eq_zpowers_a_parameter (2 * k) (by
        have hkpos := NeZero.pos k
        omega)]
      rw [heteq]
      exact Subgroup.mem_zpowers _
    exact ⟨e t, hetT0, e.symm_apply_apply t⟩


private lemma example3_isPGroup_zpowers_of_involution
    {G : Type u} [Group G] [Finite G] {x : G} (hx : IsInvolution x) :
    IsPGroup 2 (Subgroup.zpowers x) := by
  have horder : orderOf x = 2 := (orderOf_eq_prime_iff).2 ⟨hx.2, hx.1⟩
  have hcard : Nat.card (Subgroup.zpowers x) = 2 := by
    simp [Nat.card_zpowers, horder]
  exact IsPGroup.of_card (p := 2) (G := Subgroup.zpowers x) (n := 1) (by
    simp [hcard])

public lemma example3_sylow_involution_unique
    {G : Type u} [Group G] [Finite G]
    (Q : Sylow 2 G) {n : ℕ}
    (hQ : Nonempty (Q ≃* QuaternionGroup (2 ^ (n - 2)))) :
    ∀ x y : Q, IsInvolution x → IsInvolution y → x = y := by
  let eqv : Q ≃* QuaternionGroup (2 ^ (n - 2)) := Classical.choice hQ
  intro x y hx hy
  have hex : IsInvolution (eqv x) := by
    constructor
    · intro h
      apply hx.ne_one
      apply eqv.injective
      simpa using h
    · simpa using congrArg eqv hx.sq_eq_one
  have hey : IsInvolution (eqv y) := by
    constructor
    · intro h
      apply hy.ne_one
      apply eqv.injective
      simpa using h
    · simpa using congrArg eqv hy.sq_eq_one
  apply eqv.injective
  exact (quaternionGroup_eq_a_parameter_of_isInvolution
    (2 ^ (n - 2)) hex).trans
      (quaternionGroup_eq_a_parameter_of_isInvolution
        (2 ^ (n - 2)) hey).symm

public lemma example3_commuting_involutions_eq
    {G : Type u} [Group G] [Finite G]
    (Q : Sylow 2 G)
    (hunique : ∀ x y : Q, IsInvolution x → IsInvolution y → x = y)
    {u v : G} (hu : IsInvolution u) (hv : IsInvolution v) (huv : Commute u v) :
    u = v := by
  have huP : IsPGroup 2 (Subgroup.zpowers u) :=
    example3_isPGroup_zpowers_of_involution hu
  have hvP : IsPGroup 2 (Subgroup.zpowers v) :=
    example3_isPGroup_zpowers_of_involution hv
  have hnorm : Subgroup.zpowers u ≤ Subgroup.normalizer (Subgroup.zpowers v) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor <;> intro hy
    · rcases hx with ⟨m, rfl⟩
      rcases hy with ⟨n, rfl⟩
      exact ⟨n, by rw [huv.zpow_zpow m n, mul_inv_cancel_right]⟩
    · rcases hx with ⟨m, rfl⟩
      rcases hy with ⟨n, hn⟩
      refine ⟨n, ?_⟩
      change v ^ n = u ^ m * y * (u ^ m)⁻¹ at hn
      have hcomm := huv.zpow_zpow m n
      calc
        v ^ n = (u ^ m)⁻¹ * (u ^ m * v ^ n) := by group
        _ = (u ^ m)⁻¹ * (v ^ n * u ^ m) := by rw [hcomm.eq]
        _ = (u ^ m)⁻¹ * ((u ^ m * y * (u ^ m)⁻¹) * u ^ m) := by rw [hn]
        _ = y := by group
  have hsupP : IsPGroup 2
      (Subgroup.zpowers u ⊔ Subgroup.zpowers v : Subgroup G) :=
    IsPGroup.to_sup_of_normal_right' huP hvP hnorm
  obtain ⟨S, hsup_le_S⟩ :=
    IsPGroup.exists_le_sylow (G := G) (p := 2) hsupP
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S Q
  have huS : u ∈ (S : Subgroup G) :=
    hsup_le_S ((le_sup_left :
      Subgroup.zpowers u ≤ Subgroup.zpowers u ⊔ Subgroup.zpowers v)
        (Subgroup.mem_zpowers u))
  have hvS : v ∈ (S : Subgroup G) :=
    hsup_le_S ((le_sup_right :
      Subgroup.zpowers v ≤ Subgroup.zpowers u ⊔ Subgroup.zpowers v)
        (Subgroup.mem_zpowers v))
  have hcoe : ((g • S : Sylow 2 G) : Subgroup G) = (Q : Subgroup G) :=
    congrArg (fun P : Sylow 2 G => (P : Subgroup G)) hg
  let ug : Q := ⟨g * u * g⁻¹, by
    have hmem : g * u * g⁻¹ ∈ ((g • S : Sylow 2 G) : Subgroup G) := by
      rw [Sylow.coe_subgroup_smul]
      exact Set.mem_smul_set.mpr ⟨u, huS, rfl⟩
    change g * u * g⁻¹ ∈ (Q : Subgroup G)
    rw [← hcoe]
    exact hmem⟩
  let vg : Q := ⟨g * v * g⁻¹, by
    have hmem : g * v * g⁻¹ ∈ ((g • S : Sylow 2 G) : Subgroup G) := by
      rw [Sylow.coe_subgroup_smul]
      exact Set.mem_smul_set.mpr ⟨v, hvS, rfl⟩
    change g * v * g⁻¹ ∈ (Q : Subgroup G)
    rw [← hcoe]
    exact hmem⟩
  have hugAmbient : IsInvolution (g * u * g⁻¹) := by
    simpa [rightConjugateElem] using
      isInvolution_rightConjugateElem (g := g⁻¹) hu
  have hvgAmbient : IsInvolution (g * v * g⁻¹) := by
    simpa [rightConjugateElem] using
      isInvolution_rightConjugateElem (g := g⁻¹) hv
  have hug : IsInvolution ug := by
    constructor
    · intro h
      apply hugAmbient.1
      simpa [ug] using congrArg Subtype.val h
    · apply Subtype.ext
      simpa [ug] using hugAmbient.2
  have hvg : IsInvolution vg := by
    constructor
    · intro h
      apply hvgAmbient.1
      simpa [vg] using congrArg Subtype.val h
    · apply Subtype.ext
      simpa [vg] using hvgAmbient.2
  have heq : ug = vg := hunique ug vg hug hvg
  have hcoe' : g * u * g⁻¹ = g * v * g⁻¹ := congrArg Subtype.val heq
  simpa using (mul_left_cancel (mul_right_cancel hcoe'))

private lemma example3_not_stronglyReal_of_four_dvd_order
    {G : Type u} [Group G] [Finite G]
    (Q : Sylow 2 G)
    (hunique : ∀ x y : Q, IsInvolution x → IsInvolution y → x = y)
    {x : G} (hfour : 4 ∣ orderOf x) :
    ¬ IsStronglyReal x := by
  rintro ⟨u, v, hu, hv, rfl⟩
  have huv : u ≠ v := by
    intro huv
    subst v
    have hprod : u * u = 1 := by
      simpa [pow_two] using hu.sq_eq_one
    have horder_one : orderOf (u * u) = 1 := by
      rw [hprod, orderOf_one]
    rw [horder_one] at hfour
    norm_num at hfour
  have htwo : 2 ∣ orderOf (u * v) := dvd_trans (by norm_num) hfour
  let m : ℕ := orderOf (u * v) / 2
  have horder : orderOf (u * v) = 2 * m := by
    exact (Nat.mul_div_cancel' htwo).symm
  obtain ⟨hw, hwu, hwv⟩ :=
    BenderSuzuki.External.Suzuki.V.suzuki_ch5_proposition_1_2_iii
      hu hv huv horder
  have heq_u : (u * v) ^ m = u :=
    example3_commuting_involutions_eq Q hunique hw hu hwu
  have heq_v : (u * v) ^ m = v :=
    example3_commuting_involutions_eq Q hunique hw hv hwv
  exact huv (heq_u.symm.trans heq_v)


private lemma example3_exists_involution_of_generalizedQuaternionSylow
    {G : Type u} [Group G] [Finite G]
    (Q : Sylow 2 G) {n : ℕ}
    (hQ : Nonempty (Q ≃* QuaternionGroup (2 ^ (n - 2)))) :
    ∃ t : G, IsInvolution t := by
  let m : ℕ := 2 ^ (n - 2)
  let : NeZero m := ⟨by simp [m]⟩
  let eqv : Q ≃* QuaternionGroup m := Classical.choice hQ
  let q0 : QuaternionGroup m :=
    QuaternionGroup.a (m : ZMod (2 * m))
  have hq0 : IsInvolution q0 :=
    quaternionGroup_isInvolution_a_parameter m
  let tq : Q := eqv.symm q0
  have htq : IsInvolution tq := by
    constructor
    · intro h
      apply hq0.ne_one
      have := congrArg eqv h
      simpa [tq, q0] using this
    · apply eqv.injective
      simpa [tq, q0] using hq0.sq_eq_one
  refine ⟨(tq : G), ?_⟩
  constructor
  · intro h
    apply htq.ne_one
    exact Subtype.ext h
  · exact congrArg Subtype.val htq.sq_eq_one

private lemma example3_inducedCF_vanishes_at_involution
    {G : Type u} [Group G] [Finite G]
    (H : Subgroup G) (eta : Section1.ClassFunction H)
    (K : Set G)
    (hKfour : ∀ k : G, k ∈ K → 4 ∣ orderOf k)
    (hetaSupport : ∀ h : H, (h : G) ∉ K → eta h = 0)
    {t : G} (ht : IsInvolution t) :
    Section1.inducedCF H eta t = 0 := by
  unfold Section1.inducedCF Section1.inducedClassFunction
  apply mul_eq_zero_of_right
  apply Finset.sum_eq_zero
  intro x _hx
  split
  next hmem =>
    apply hetaSupport
    intro hK
    have hfour := hKfour (x * t * x⁻¹) (by simpa using hK)
    have hord : orderOf (x * t * x⁻¹) = 2 := by
      rw [show orderOf (x * t * x⁻¹) = orderOf t by
        simpa using (MulAut.conj x).orderOf_eq t]
      exact orderOf_eq_prime ht.sq_eq_one ht.ne_one
    rw [hord] at hfour
    norm_num at hfour
  next hnot =>
    rfl


section StageEStructure

private lemma example3_stage_e_structure_constant_identity
    {G : Type u} [Group G] [Finite G]
    (Q : Sylow 2 G) {n : ℕ}
    (hQ : Nonempty (Q ≃* QuaternionGroup (2 ^ (n - 2))))
    (H : Subgroup G) (eta : Section1.ClassFunction H)
    (K : Set G)
    (hKfour : ∀ k : G, k ∈ K → 4 ∣ orderOf k)
    (hetaSupport : ∀ h : H, (h : G) ∉ K → eta h = 0)
    (zeta : Section1.ClassFunction G)
    (hzeta_def : zeta = Section1.inducedCF H eta)
    {r : ℕ} (chi : Fin r → Section1.ClassFunction G)
    (epsilon : Fin r → ℂ)
    (hchi_irreducible :
      ∀ i, Section1.IsIrreducibleCharacterOnGroup (chi i))
    (hzeta_decomposition :
      zeta = Section1.principalCharacter G +
        Section1.weightedFamilySum epsilon chi)
    {t : G} (ht : IsInvolution t) :
    1 + ∑ i, epsilon i * chi i t ^ 2 / chi i 1 = 0 := by
  classical
  let : Fintype G := Fintype.ofFinite G
  rcases Theory.Character.irreducible_characters_form_basis (G := G) with
    ⟨ι, hι, xi, hxi, _b, _hb⟩
  let : Fintype ι := hι
  let : DecidableEq ι := Classical.decEq ι
  let mu : ι → Section1.ClassFunction G :=
    fun j => Section1.ofConjClassFunction (xi j)
  let Ct : ConjClasses G := ConjClasses.mk t
  let C1 : ConjClasses G := ConjClasses.mk (1 : G)
  let a : ι → ℂ := fun j => xi j Ct * xi j Ct / xi j C1
  let omega : Section1.ClassFunction G :=
    Section1.weightedFamilySum (fun j => star (a j)) mu
  have hmuClass : ∀ j, Section1.IsClassFunction (mu j) := by
    intro j
    exact Section1.ofConjClassFunction_isClassFunction (xi j)
  have homegaClass : Section1.IsClassFunction omega := by
    intro x g
    unfold omega Section1.weightedFamilySum
    refine Finset.sum_congr rfl ?_
    intro j _hj
    simp [hmuClass j x g]
  have hunique := example3_sylow_involution_unique Q hQ
  have homega_zero : ∀ k : G, k ∈ K → omega k = 0 := by
    intro k hk
    have hnotStrong : ¬ IsStronglyReal k :=
      example3_not_stronglyReal_of_four_dvd_order Q hunique (hKfour k hk)
    let PairType :=
      {p : Ct.carrier × Ct.carrier // p.1.1 * p.2.1 = k}
    have hPairEmpty : IsEmpty PairType := by
      refine ⟨?_⟩
      intro p
      have hp1Conj : IsConj p.1.1.1 t := by
        apply ConjClasses.mk_eq_mk_iff_isConj.mp
        have hp1mk := ConjClasses.mem_carrier_iff_mk_eq.mp p.1.1.2
        simpa [Ct] using hp1mk
      have hp2Conj : IsConj p.1.2.1 t := by
        apply ConjClasses.mk_eq_mk_iff_isConj.mp
        have hp2mk := ConjClasses.mem_carrier_iff_mk_eq.mp p.1.2.2
        simpa [Ct] using hp2mk
      have hp1I : IsInvolution p.1.1.1 := by
        rcases isConj_iff.mp hp1Conj with ⟨c, hc⟩
        have heq : p.1.1.1 = rightConjugateElem t c := by
          calc
            p.1.1.1 = c⁻¹ * (c * p.1.1.1 * c⁻¹) * c := by group
            _ = c⁻¹ * t * c := by rw [hc]
            _ = rightConjugateElem t c := rfl
        rw [heq]
        exact isInvolution_rightConjugateElem ht
      have hp2I : IsInvolution p.1.2.1 := by
        rcases isConj_iff.mp hp2Conj with ⟨c, hc⟩
        have heq : p.1.2.1 = rightConjugateElem t c := by
          calc
            p.1.2.1 = c⁻¹ * (c * p.1.2.1 * c⁻¹) * c := by group
            _ = c⁻¹ * t * c := by rw [hc]
            _ = rightConjugateElem t c := rfl
        rw [heq]
        exact isInvolution_rightConjugateElem ht
      exact hnotStrong ⟨p.1.1.1, p.1.2.1, hp1I, hp2I, p.2.symm⟩
    have hcount : Nat.card PairType = 0 :=
      (Nat.card_eq_zero).2 (Or.inl hPairEmpty)
    have hformula := suzuki_ch6_formula_1_15 xi hxi Ct Ct
      (ConjClasses.mk k) k
      ((ConjClasses.mem_carrier_iff_mk_eq).2 rfl)
    have hCtNonempty : Nonempty Ct.carrier :=
      ⟨⟨t, (ConjClasses.mem_carrier_iff_mk_eq).2 (by simp [Ct])⟩⟩
    let : Nonempty Ct.carrier := hCtNonempty
    have hCtCard : (Nat.card Ct.carrier : ℂ) ≠ 0 := by
      exact_mod_cast (Nat.card_pos (α := Ct.carrier)).ne'
    have hGCard : (Nat.card G : ℂ) ≠ 0 := by
      exact_mod_cast (Nat.card_pos (α := G)).ne'
    have hfactor :
        (Nat.card Ct.carrier : ℂ) * (Nat.card Ct.carrier : ℂ) /
            (Nat.card G : ℂ) ≠ 0 :=
      div_ne_zero (mul_ne_zero hCtCard hCtCard) hGCard
    have hcharSum :
        (∑ j : ι,
          xi j Ct * xi j Ct * star (xi j (ConjClasses.mk k)) /
            xi j C1) = 0 := by
      have hzeroProduct :
          ((Nat.card Ct.carrier : ℂ) * (Nat.card Ct.carrier : ℂ) /
              (Nat.card G : ℂ)) *
            (∑ j : ι,
              xi j Ct * xi j Ct * star (xi j (ConjClasses.mk k)) /
                xi j C1) = 0 := by
        simpa [PairType, hcount, C1] using hformula.symm
      exact (mul_eq_zero.mp hzeroProduct).resolve_left hfactor
    apply star_eq_zero.mp
    calc
      star (omega k) =
          ∑ j : ι,
            xi j Ct * xi j Ct * star (xi j (ConjClasses.mk k)) /
              xi j C1 := by
        simp [omega, Section1.weightedFamilySum, a, mu, mul_assoc]
        rw [show @Finset.univ ι (Fintype.ofFinite ι) =
          @Finset.univ ι hι by ext; simp]
        apply Finset.sum_congr rfl
        intro j _hj
        change xi j Ct * xi j Ct / xi j C1 *
            star (xi j (ConjClasses.mk k)) =
          xi j Ct * (xi j Ct * star (xi j (ConjClasses.mk k))) / xi j C1
        ring
      _ = 0 := hcharSum
  have hmuOrth : ∀ i j : ι,
      Section1.scalarProduct G (mu i) (mu j) =
        if i = j then 1 else 0 := by
    intro i j
    calc
      Section1.scalarProduct G (mu i) (mu j) =
          Theory.Character.classFunctionInner (xi i) (xi j) := by
        symm
        simpa [mu, Section1.toConjClassFunction_ofConjClassFunction] using
          (Section1.classFunctionInner_toConjClassFunction
            (mu i) (mu j) (hmuClass i) (hmuClass j))
      _ = if i = j then 1 else 0 :=
        Section1.representation_completeFamily_orthonormal hxi i j
  have hspMu : ∀ j : ι,
      Section1.scalarProduct G (mu j) omega = a j := by
    intro j
    unfold omega
    rw [Section1.scalarProduct_weightedFamilySum_right]
    simp [hmuOrth, a]
  rcases Section1.exists_principal_index_of_completeFamily (G := G) hxi with
    ⟨i0, hi0⟩
  have hxi0t : xi i0 Ct = 1 := by
    change Section1.ofConjClassFunction (xi i0) t = 1
    rw [hi0]
    simp [Section1.principalCharacter]
  have hxi0one : xi i0 C1 = 1 := by
    change Section1.ofConjClassFunction (xi i0) 1 = 1
    rw [hi0]
    simp [Section1.principalCharacter]
  have hspPrincipal :
      Section1.scalarProduct G (Section1.principalCharacter G) omega = 1 := by
    rw [← hi0, hspMu]
    simp [a, hxi0t, hxi0one]
  have hchiClass : ∀ i, Section1.IsClassFunction (chi i) := by
    intro i
    exact Section1.isCharacter_isClassFunction (chi i)
      (Section1.isCharacter_of_isIrreducibleCharacterOnGroup
        (hchi_irreducible i))
  have hchiIndex : ∀ i : Fin r, ∃ j : ι, mu j = chi i := by
    intro i
    have hirr :=
      Section1.toConjClassFunction_isIrreducibleCharacter_of_isIrreducibleCharacterOnGroup
        (hchiClass i) (hchi_irreducible i)
    rcases hxi.2.1 (Section1.toConjClassFunction (chi i) (hchiClass i)) hirr with
      ⟨j, hj⟩
    refine ⟨j, ?_⟩
    ext g
    have hg := congrFun hj (ConjClasses.mk g)
    change xi j (ConjClasses.mk g) = chi i g
    exact hg
  choose kappa hkappa using hchiIndex
  have hspChi : ∀ i : Fin r,
      Section1.scalarProduct G (chi i) omega =
        chi i t ^ 2 / chi i 1 := by
    intro i
    have hkt : xi (kappa i) Ct = chi i t := by
      change mu (kappa i) t = chi i t
      rw [hkappa i]
    have hkone : xi (kappa i) C1 = chi i 1 := by
      change mu (kappa i) 1 = chi i 1
      rw [hkappa i]
    calc
      Section1.scalarProduct G (chi i) omega =
          Section1.scalarProduct G (mu (kappa i)) omega := by rw [hkappa i]
      _ = a (kappa i) := hspMu (kappa i)
      _ = chi i t ^ 2 / chi i 1 := by
        simp [a, hkt, hkone, pow_two]
  have hspZeta : Section1.scalarProduct G zeta omega = 0 := by
    rw [hzeta_def, Section1.scalarProduct_inducedCF_left H eta omega homegaClass]
    unfold Section1.scalarProduct Section1.subgroupRestriction
    apply mul_eq_zero_of_right
    apply Finset.sum_eq_zero
    intro h _hh
    by_cases hhK : (h : G) ∈ K
    · rw [homega_zero h hhK]
      simp
    · rw [hetaSupport h hhK]
      simp
  rw [hzeta_decomposition, Section1.scalarProduct_add_left,
    Section1.scalarProduct_weightedFamilySum_left] at hspZeta
  rw [show @Finset.univ (Fin r) (Fintype.ofFinite (Fin r)) =
    @Finset.univ (Fin r) (Fin.fintype r) by ext; simp] at hspZeta
  have hspZeta' :
      1 + ∑ i, epsilon i * (chi i t ^ 2 / chi i 1) = 0 := by
    simpa [hspPrincipal, hspChi] using hspZeta
  calc
    1 + ∑ i, epsilon i * chi i t ^ 2 / chi i 1 =
        1 + ∑ i, epsilon i * (chi i t ^ 2 / chi i 1) := by
      congr 1
      apply Finset.sum_congr rfl
      intro i _hi
      ring
    _ = 0 := hspZeta'

end StageEStructure

private lemma example3_low_norm_virtual_character_decomposition
    {G : Type u} [Group G] [Finite G]
    (zeta : Section1.ClassFunction G) (r : ℕ)
    (hr : r = 2 ∨ r = 3)
    (hzetaVirtual : Theory.Character.IsVirtualCharacter zeta)
    (hzetaPrincipal :
      Section1.scalarProduct G zeta (Section1.principalCharacter G) = 1)
    (hzetaNorm :
      Section1.scalarProduct G zeta zeta = (r : ℂ) + 1) :
    ∃ (chi : Fin r → Section1.ClassFunction G)
        (epsilon : Fin r → ℂ),
      (∀ i, Section1.IsIrreducibleCharacterOnGroup (chi i)) ∧
      Function.Injective chi ∧
      (∀ i, chi i ≠ Section1.principalCharacter G) ∧
      (∀ i, epsilon i = 1 ∨ epsilon i = -1) ∧
      zeta = Section1.principalCharacter G +
        Section1.weightedFamilySum epsilon chi := by
  classical
  let : Fintype (Fin r) := Fintype.ofFinite (Fin r)
  rcases Theory.Character.irreducible_characters_form_basis (G := G) with
    ⟨ι, hι, xi, hxi, b, hb⟩
  let : Fintype ι := hι
  let : DecidableEq ι := Classical.decEq ι
  let mu : ι → Section1.ClassFunction G :=
    fun i => Section1.ofConjClassFunction (xi i)
  have hmuIrreducible : ∀ i,
      Section1.IsIrreducibleCharacterOnGroup (mu i) := by
    intro i
    exact Section3.ofConjClassFunction_isIrreducibleCharacterOnGroup (hxi.1 i)
  have hmuVirtual : ∀ i, Theory.Character.IsVirtualCharacter (mu i) := by
    intro i
    exact Section3.isVirtualCharacter_of_irreducibleCharacterOnGroup
      (hmuIrreducible i)
  have hint : ∀ i : ι, ∃ z : ℤ,
      Section1.scalarProduct G zeta (mu i) = (z : ℂ) := by
    intro i
    exact Section1.scalarProduct_isVirtualCharacter_eq_int
      hzetaVirtual (hmuVirtual i)
  let a : Section1.CoeffVector ι :=
    Section3.irreducibleBasisCoeff zeta hint
  have haSpec : ∀ i : ι,
      Section1.scalarProduct G zeta (mu i) = (a i : ℂ) := by
    intro i
    exact Section3.irreducibleBasisCoeff_spec zeta hint i
  have hzetaClass : Section1.IsClassFunction zeta :=
    Section1.isVirtualCharacter_isClassFunction hzetaVirtual
  have hzetaEval : Section1.evalCoeff mu a = zeta := by
    exact Section3.irreducibleBasis_evalCoeff_coeff hxi b hb zeta hzetaClass hint
  rcases Section1.exists_principal_index_of_completeFamily (G := G) hxi with
    ⟨i0, hi0⟩
  have hai0Complex : (a i0 : ℂ) = 1 := by
    rw [← haSpec i0]
    change Section1.scalarProduct G zeta
      (Section1.ofConjClassFunction (xi i0)) = 1
    rw [hi0, hzetaPrincipal]
  have hai0 : a i0 = 1 := by
    exact_mod_cast hai0Complex
  have hdotComplex : (Section1.coeffDot a a : ℂ) = (r : ℂ) + 1 := by
    rw [← Section3.irreducibleBasis_scalarProduct_evalCoeff hxi a a,
      hzetaEval, hzetaNorm]
  have hdot : Section1.coeffDot a a = (r : ℤ) + 1 := by
    exact_mod_cast hdotComplex
  have hdotSupport : Section1.coeffDot a a =
      ∑ i ∈ Section1.coeffSupport a, a i * a i := by
    rw [Section1.coeffDot]
    symm
    apply Finset.sum_subset
    · intro i _hi
      simp
    · intro i _hi hiNot
      have hai : a i = 0 := Section1.coeff_eq_zero_of_not_mem_support a hiNot
      simp [hai]
  have hi0Support : i0 ∈ Section1.coeffSupport a := by
    rw [Section1.mem_coeffSupport]
    omega
  let S : Finset ι := (Section1.coeffSupport a).erase i0
  have hsumS : ∑ i ∈ S, a i * a i = (r : ℤ) := by
    have hsplit := Finset.sum_erase_add (Section1.coeffSupport a)
      (fun i => a i * a i) hi0Support
    rw [← hdotSupport, hdot] at hsplit
    simp only [hai0, one_mul] at hsplit
    change (∑ i ∈ (Section1.coeffSupport a).erase i0, a i * a i) = (r : ℤ)
    omega
  have hrle : r ≤ 3 := by omega
  have hsign : ∀ i ∈ S, a i = 1 ∨ a i = -1 := by
    intro i hiS
    have hai_ne : a i ≠ 0 := by
      have hiSupport : i ∈ Section1.coeffSupport a := by
        exact Finset.mem_of_mem_erase hiS
      simpa using (Section1.mem_coeffSupport a i).1 hiSupport
    have hterm_le : a i * a i ≤ ∑ j ∈ S, a j * a j := by
      refine Finset.single_le_sum (N := ℤ) (s := S)
        (f := fun j => a j * a j) ?_ hiS
      intro j _hj
      nlinarith [sq_nonneg (a j)]
    have hsqle : (a i) ^ 2 ≤ 3 := by
      rw [hsumS] at hterm_le
      have hrleInt : (r : ℤ) ≤ 3 := by exact_mod_cast hrle
      nlinarith
    have hsqeq : (a i) ^ 2 = 1 :=
      Int.sq_eq_one_of_sq_le_three hsqle hai_ne
    simpa using (sq_eq_one_iff.mp hsqeq)
  have hcardInt : (S.card : ℤ) = (r : ℤ) := by
    calc
      (S.card : ℤ) = ∑ _i ∈ S, (1 : ℤ) := by simp
      _ = ∑ i ∈ S, a i * a i := by
        refine Finset.sum_congr rfl ?_
        intro i hiS
        rcases hsign i hiS with hi | hi <;> simp [hi]
      _ = (r : ℤ) := hsumS
  have hcard : S.card = r := by exact_mod_cast hcardInt
  let e : Fin r ≃ {i // i ∈ S} :=
    (finCongr hcard.symm).trans S.equivFin.symm
  let chi : Fin r → Section1.ClassFunction G := fun j => mu (e j)
  let epsilon : Fin r → ℂ := fun j => (a (e j) : ℂ)
  refine ⟨chi, epsilon, ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    exact hmuIrreducible (e j)
  · intro i j hij
    apply e.injective
    apply Subtype.ext
    apply hxi.2.2
    ext c
    rcases ConjClasses.exists_rep c with ⟨g, rfl⟩
    exact congrFun hij g
  · intro j hj
    have hmuEq : mu (e j) = mu i0 := hj.trans hi0.symm
    have heq : (e j : ι) = i0 := by
      apply hxi.2.2
      ext c
      rcases ConjClasses.exists_rep c with ⟨g, rfl⟩
      exact congrFun hmuEq g
    exact (Finset.ne_of_mem_erase (e j).property) heq
  · intro j
    rcases hsign (e j) (e j).property with h | h
    · left
      change (a (e j) : ℂ) = 1
      exact_mod_cast h
    · right
      change (a (e j) : ℂ) = -1
      exact_mod_cast h
  · ext g
    have hsumSupport :
        (∑ i : ι, (a i : ℂ) * mu i g) =
          ∑ i ∈ Section1.coeffSupport a, (a i : ℂ) * mu i g := by
      symm
      apply Finset.sum_subset
      · intro i _hi
        simp
      · intro i _hi hiNot
        have hai : a i = 0 := Section1.coeff_eq_zero_of_not_mem_support a hiNot
        simp [hai]
    calc
      zeta g = Section1.evalCoeff mu a g := congrFun hzetaEval.symm g
      _ = ∑ i : ι, (a i : ℂ) * mu i g := by
        simp [Section1.evalCoeff]
      _ = ∑ i ∈ Section1.coeffSupport a, (a i : ℂ) * mu i g := hsumSupport
      _ = (∑ i ∈ S, (a i : ℂ) * mu i g) +
          (a i0 : ℂ) * mu i0 g := by
        simpa [S] using (Finset.sum_erase_add (Section1.coeffSupport a)
          (fun i => (a i : ℂ) * mu i g) hi0Support).symm
      _ = Section1.principalCharacter G g +
          ∑ i ∈ S, (a i : ℂ) * mu i g := by
        rw [hai0]
        simp only [mu]
        rw [hi0]
        simp [add_comm]
      _ = Section1.principalCharacter G g +
          ∑ j : Fin r, epsilon j * chi j g := by
        congr 1
        rw [← S.sum_attach]
        simpa [chi, epsilon] using
          (Equiv.sum_comp e
            (fun i : {i // i ∈ S} => (a i : ℂ) * mu i g)).symm
      _ = (Section1.principalCharacter G +
          Section1.weightedFamilySum epsilon chi) g := by
        rfl


private lemma example3_quaternion_card_eq_eight_or_ge_sixteen
    {P : Type*} [Group P] [Finite P]
    {n : ℕ} (hn : 3 ≤ n)
    (hP : Nonempty (P ≃* QuaternionGroup (2 ^ (n - 2)))) :
    Nat.card P = 8 ∨ 16 ≤ Nat.card P := by
  let e : P ≃* QuaternionGroup (2 ^ (n - 2)) := Classical.choice hP
  have hcard : Nat.card P = 2 ^ n := by
    calc
      Nat.card P = Nat.card (QuaternionGroup (2 ^ (n - 2))) :=
        Nat.card_congr e.toEquiv
      _ = 4 * 2 ^ (n - 2) := by
        rw [Nat.card_eq_fintype_card, QuaternionGroup.card]
      _ = 2 ^ n := by
        rw [show n = 2 + (n - 2) by omega, pow_add]
        norm_num
  by_cases hn3 : n = 3
  · left
    rw [hcard, hn3]
    norm_num
  · right
    rw [hcard]
    calc
      16 = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) (by omega)

private lemma example3_simple_kernel_contradiction
    {G : Type u} [Group G] [Finite G]
    (hG : IsSimpleGroup G)
    (chi : Section1.ClassFunction G)
    (hchi : Section1.IsIrreducibleCharacterOnGroup chi)
    (hchi_nonprincipal : chi ≠ Section1.principalCharacter G)
    (t : G) (ht_order : orderOf t = 2)
    (m : ℕ) (rho : Representation ℂ G (Fin m → ℂ))
    (hirr : Representation.IsIrreducible rho)
    (hchar : chi = rho.character)
    (htker : t ∈ rho.ker) : False := by
  have htne : t ≠ 1 := by
    intro ht
    rw [ht, orderOf_one] at ht_order
    norm_num at ht_order
  have hker_ne_bot : rho.ker ≠ ⊥ := by
    intro hbot
    have : t = 1 := by
      simpa [hbot] using htker
    exact htne this
  have hker_top : rho.ker = ⊤ := by
    rcases Subgroup.IsSubnormal.eq_bot_or_top_of_isSimpleGroup hG
        (MonoidHom.normal_ker rho).isSubnormal with hbot | htop
    · exact (hker_ne_bot hbot).elim
    · exact htop
  have hrho : rho = 1 := MonoidHom.ker_eq_top_iff.mp hker_top
  have hzero :=
    Section1.scalarProduct_irreducibleCharacter_principal_eq_zero_of_ne
      hchi hchi_nonprincipal
  have hmpos : 0 < m := by
    let : Representation.IsIrreducible rho := hirr
    have hpos : 0 < Module.finrank ℂ (Fin m → ℂ) :=
      (Module.finrank_pos_iff (R := ℂ) (M := Fin m → ℂ)).2
        (Theory.Character.irreducible_nontrivial (ρ := rho))
    simpa using hpos
  rw [hchar, hrho] at hzero
  unfold Section1.scalarProduct at hzero
  simp [Representation.character, Section1.principalCharacter] at hzero
  rcases hzero with hGzero | hmzero
  · exact (Nat.card_pos.ne' hGzero).elim
  · exact (hmpos.ne' hmzero).elim
private lemma example3_simple_nonprincipal_degree_gt_one
    {G : Type u} [Group G] [Finite G]
    (hG : IsSimpleGroup G)
    (Q : Sylow 2 G) (hQeight : Nat.card Q = 8)
    (chi : Section1.ClassFunction G)
    (hchi : Section1.IsIrreducibleCharacterOnGroup chi)
    (hchi_nonprincipal : chi ≠ Section1.principalCharacter G)
    (m : ℕ) (rho : Representation ℂ G (Fin m → ℂ))
    (hirr : Representation.IsIrreducible rho)
    (hchar : chi = rho.character) :
    1 < m := by
  have hmpos : 0 < m := by
    let : Representation.IsIrreducible rho := hirr
    have hpos : 0 < Module.finrank ℂ (Fin m → ℂ) :=
      (Module.finrank_pos_iff (R := ℂ) (M := Fin m → ℂ)).2
        (Theory.Character.irreducible_nontrivial (ρ := rho))
    simpa using hpos
  have hmne : m ≠ 1 := by
    intro hm
    have hdegree : Section1.degree chi = 1 := by
      rw [hchar, Section1.degree_representation_character]
      simp [hm]
    obtain ⟨lam, hlamchi⟩ :=
      Section1.exists_linearCharacter_of_irreducible_degree_one hchi hdegree
    have hlamnormal : lam.ker.Normal := MonoidHom.normal_ker lam
    rcases (haveI := hlamnormal; IsSimpleGroup.eq_bot_or_eq_top_of_normal lam.ker) with hbot | htop
    · have hlaminjective : Function.Injective lam :=
        (MonoidHom.ker_eq_bot_iff lam).mp hbot
      let : CommGroup G := MonoidHom.commGroupOfInjective lam hlaminjective
      let : IsSimpleGroup G := hG
      have hp : (Nat.card G).Prime := IsSimpleGroup.prime_card
      have h8dvd : 8 ∣ Nat.card G := by
        rw [← hQeight]
        exact Subgroup.card_subgroup_dvd_card (Q : Subgroup G)
      rcases (Nat.dvd_prime hp).mp h8dvd with h8one | h8card
      · norm_num at h8one
      · rw [← h8card] at hp
        norm_num at hp
    · have hlamone : lam = 1 := MonoidHom.ker_eq_top_iff.mp htop
      apply hchi_nonprincipal
      rw [hlamchi, hlamone]
      funext g
      simp [Section1.principalCharacter]
  omega
private lemma example3_subgroup_pPrimeCore_eq_bot
    {G : Type u} [Group G] [Finite G]
    (hcore : pPrimeCore 2 G = ⊥)
    (M : Subgroup G) (hM : M.Normal) :
    pPrimeCore 2 M = ⊥ := by
  let : M.Normal := hM
  have hmapbot : (pPrimeCore 2 M).map M.subtype = ⊥ := by
    apply le_bot_iff.mp
    simpa [hcore] using
      pPrimeCore_map_subtype_le_pPrimeCore_of_normal
        (G := G) (p := 2) M
  exact (Subgroup.map_eq_bot_iff_of_injective
    (H := pPrimeCore 2 M) (f := M.subtype) M.subtype_injective).mp hmapbot

private lemma example3_center_even_of_cyclic_sylow_corefree
    {M : Type u} [Group M] [Finite M]
    (hcore : pPrimeCore 2 M = ⊥)
    (hMeven : 2 ∣ Nat.card M)
    (S : Sylow 2 M) (hScyclic : IsCyclic S) :
    2 ∣ Nat.card (Subgroup.center M) := by
  let : Nontrivial M :=
    Finite.one_lt_card_iff_nontrivial.mp (by
      have htwo_le : 2 ≤ Nat.card M := Nat.le_of_dvd Nat.card_pos hMeven
      omega)
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hminFac : (Nat.card M).minFac = 2 :=
    (Nat.minFac_eq_two_iff (Nat.card M)).2 hMeven
  have hcomp : HasNormalPComplement 2 M :=
    BenderSuzuki.External.Suzuki.V.suzuki_ch5_theorem_2_10_corollary_1
      S hminFac hScyclic
  have hMp : IsPGroup 2 M :=
    BenderSuzuki.External.hkt_isPGroup_of_hasNormalPComplement_of_pPrimeCore_eq_bot
      hcore hcomp
  have hcenter_nontrivial : Nontrivial (Subgroup.center M) :=
    hMp.center_nontrivial
  have hcenterP : IsPGroup 2 (Subgroup.center M) :=
    hMp.to_subgroup (Subgroup.center M)
  exact hcenterP.card_eq_or_dvd.resolve_left
    (ne_of_gt (Finite.one_lt_card_iff_nontrivial.mpr hcenter_nontrivial))

private lemma example3_subgroup_sylow_cyclic_or_quaternion
    {G : Type u} [Group G] [Finite G]
    (Q : Sylow 2 G)
    (huniqueQ : ∀ x y : Q, IsInvolution x → IsInvolution y → x = y)
    (M : Subgroup G) (hMeven : 2 ∣ Nat.card M)
    (S : Sylow 2 M) :
    IsCyclic S ∨
      ∃ m : ℕ, 3 ≤ m ∧
        Nonempty (S ≃* QuaternionGroup (2 ^ (m - 2))) := by
  classical
  let SM : Subgroup G := (S : Subgroup M).map M.subtype
  have hSMp : IsPGroup 2 SM := by
    dsimp [SM]
    exact IsPGroup.map (p := 2) (H := (S : Subgroup M)) S.isPGroup' M.subtype
  obtain ⟨R, hSMleR⟩ := IsPGroup.exists_le_sylow (G := G) (p := 2) hSMp
  let eSM : S ≃* SM :=
    Subgroup.equivMapOfInjective (S : Subgroup M) M.subtype M.subtype_injective
  let eLe : SM ≃* SM.subgroupOf R :=
    (Subgroup.subgroupOfEquivOfLe (H := SM) (K := (R : Subgroup G)) hSMleR).symm
  let eRQ : R ≃* Q := Sylow.equiv R Q
  let f : S →* Q :=
    eRQ.toMonoidHom.comp
      ((SM.subgroupOf R).subtype.comp (eLe.toMonoidHom.comp eSM.toMonoidHom))
  have hf : Function.Injective f := by
    exact eRQ.injective.comp
      ((SM.subgroupOf R).subtype_injective.comp (eLe.injective.comp eSM.injective))
  have huniqueI : ∀ x y : S,
      IsInvolution x → IsInvolution y → x = y := by
    intro x y hx hy
    have hfx : IsInvolution (f x) := by
      constructor
      · intro h
        apply hx.ne_one
        apply hf
        simpa using h
      · simpa using congrArg f hx.sq_eq_one
    have hfy : IsInvolution (f y) := by
      constructor
      · intro h
        apply hy.ne_one
        apply hf
        simpa using h
      · simpa using congrArg f hy.sq_eq_one
    exact hf (huniqueQ (f x) (f y) hfx hfy)
  have htwoS : 2 ∣ Nat.card S := Sylow.dvd_card_of_dvd_card S hMeven
  obtain ⟨z, hzorder⟩ := exists_prime_orderOf_dvd_card' (G := S) 2 htwoS
  have hzI : IsInvolution z := by
    have hz := orderOf_eq_prime_iff.mp hzorder
    exact ⟨hz.2, by simpa [pow_two] using hz.1⟩
  let U : Subgroup S := Subgroup.zpowers z
  have hUcard : Nat.card U = 2 := by
    simp [U, Nat.card_zpowers, hzorder]
  have huniqueU : ∀ V : Subgroup S, Nat.card V = 2 → V = U := by
    intro V hVcard
    have htwoV : 2 ∣ Nat.card V := by simp [hVcard]
    obtain ⟨v, hvorder⟩ := exists_prime_orderOf_dvd_card' (G := V) 2 htwoV
    have hvorderS : orderOf (v : S) = 2 := by
      rw [Subgroup.orderOf_coe]
      exact hvorder
    have hvI : IsInvolution (v : S) := by
      have hv := orderOf_eq_prime_iff.mp hvorderS
      exact ⟨hv.2, by simpa [pow_two] using hv.1⟩
    have hzv : z = (v : S) := huniqueI z (v : S) hzI hvI
    have hzp_le : Subgroup.zpowers (v : S) ≤ V :=
      Subgroup.zpowers_le.mpr v.property
    rw [← hzv] at hzp_le
    exact (Subgroup.eq_of_le_of_card_ge hzp_le (by rw [hUcard, hVcard])).symm
  have hclass :=
    BenderSuzuki.External.huppert_III_8_2_pgroup_unique_order_prime_subgroup
      (G := S) (p := 2) Nat.prime_two S.isPGroup' ⟨U, hUcard, huniqueU⟩
  exact hclass.2 rfl

public lemma example3_quotient_sylow
    {G : Type u} [Group G] [Finite G]
    (Q : Sylow 2 G) {n : ℕ}
    (hQ : Nonempty (Q ≃* QuaternionGroup (2 ^ (n - 2)))) :
    ∃ Qbar : Sylow 2 (G ⧸ pPrimeCore 2 G),
      Nonempty (Qbar ≃* QuaternionGroup (2 ^ (n - 2))) := by
  classical
  let N : Subgroup G := pPrimeCore 2 G
  let q : G →* G ⧸ N := QuotientGroup.mk' N
  let Qbar : Sylow 2 (G ⧸ N) :=
    Q.mapSurjective (f := q) (QuotientGroup.mk'_surjective N)
  have hqinj : Function.Injective (q.comp (Q : Subgroup G).subtype) := by
    simpa [q, N] using
      quotient_pPrimeCore_subgroupMap_injective
        (G := G) (p := 2) (H := (Q : Subgroup G)) Q.isPGroup'
  let f : Q →* Qbar :=
    (q.comp (Q : Subgroup G).subtype).codRestrict Qbar (by
      intro x
      change q (x : G) ∈ (Qbar : Subgroup (G ⧸ N))
      rw [show (Qbar : Subgroup (G ⧸ N)) = (Q : Subgroup G).map q by
        simp [Qbar, Sylow.coe_mapSurjective]]
      exact Subgroup.mem_map_of_mem q x.2)
  have hfbij : Function.Bijective f := by
    constructor
    · intro x y hxy
      apply Subtype.ext
      exact congrArg Subtype.val (hqinj (congrArg Subtype.val hxy))
    · intro y
      have hy : (y : G ⧸ N) ∈ (Q : Subgroup G).map q := by
        let y0 : G ⧸ N := y
        have hy0 : y0 ∈ (Qbar : Subgroup (G ⧸ N)) := y.property
        have hQbar : (Qbar : Subgroup (G ⧸ N)) =
            (Q : Subgroup G).map q := by
          simp [Qbar, Sylow.coe_mapSurjective]
        rw [hQbar] at hy0
        exact hy0
      rcases Subgroup.mem_map.mp hy with ⟨x, hx, hxy⟩
      refine ⟨⟨x, hx⟩, ?_⟩
      apply Subtype.ext
      exact hxy
  let eQbar : Q ≃* Qbar := MulEquiv.ofBijective f hfbij
  refine ⟨Qbar, ?_⟩
  exact ⟨eQbar.symm.trans (Classical.choice hQ)⟩

private lemma example3_center_even_of_quotient_center_even_corefree
    {M : Type u} [Group M] [Finite M]
    (hcore : pPrimeCore 2 M = ⊥)
    (hquot : 2 ∣ Nat.card (Subgroup.center (M ⧸ pPrimeCore 2 M))) :
    2 ∣ Nat.card (Subgroup.center M) := by
  let e : (M ⧸ pPrimeCore 2 M) ≃* M :=
    (QuotientGroup.quotientMulEquivOfEq hcore).trans
      (QuotientGroup.quotientBot (G := M))
  rw [Nat.card_congr (Subgroup.centerCongr e).toEquiv] at hquot
  exact hquot
private lemma example3_corefree_target_of_normal_center_even
    {G : Type u} [Group G] [Finite G]
    (hcore : pPrimeCore 2 G = ⊥)
    (M : Subgroup G) (hM : M.Normal)
    (hcenterEven : 2 ∣ Nat.card (Subgroup.center M))
    (hcommuting_unique : ∀ a b : G,
      IsInvolution a → IsInvolution b → Commute a b → a = b) :
    2 ∣ Nat.card (Subgroup.center (G ⧸ pPrimeCore 2 G)) := by
  classical
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : M.Normal := hM
  let ZM : Subgroup G := (Subgroup.center M).map M.subtype
  have hZMnormal : ZM.Normal := by
    dsimp [ZM]
    let : (Subgroup.center M).Characteristic := Subgroup.centerCharacteristic
    exact ConjAct.normal_of_characteristic_of_normal
  let : ZM.Normal := hZMnormal
  let : IsMulCommutative ZM := by
    dsimp [ZM]
    exact Subgroup.map_isMulCommutative (Subgroup.center M) M.subtype
  have hcardZM : Nat.card ZM = Nat.card (Subgroup.center M) := by
    dsimp [ZM]
    exact Subgroup.card_map_of_injective (Subgroup.subtype_injective M)
  have hZMtwo : 2 ∣ Nat.card ZM := by
    rw [hcardZM]
    exact hcenterEven
  let : Fintype ZM := Fintype.ofFinite ZM
  have hZMtwo' : 2 ∣ Fintype.card ZM := by
    simpa [← Nat.card_eq_fintype_card] using hZMtwo
  obtain ⟨z, hzorder⟩ := exists_prime_orderOf_dvd_card 2 hZMtwo'
  have hzorderG : orderOf (z : G) = 2 := by
    rw [Subgroup.orderOf_coe]
    exact hzorder
  have hzI : IsInvolution (z : G) := by
    have hz := orderOf_eq_prime_iff.mp hzorderG
    exact ⟨hz.2, by simpa [pow_two] using hz.1⟩
  have hzcenter : (z : G) ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro g
    have hwmem : g * (z : G) * g⁻¹ ∈ ZM :=
      hZMnormal.conj_mem (z : G) z.property g
    let w : ZM := ⟨g * (z : G) * g⁻¹, hwmem⟩
    have hworderG : orderOf (w : G) = 2 := by
      change orderOf ((MulAut.conj g) (z : G)) = 2
      have hconjOrder :=
        orderOf_injective (MulAut.conj g).toMonoidHom
          (MulAut.conj g).injective (z : G)
      exact hconjOrder.trans hzorderG
    have hwI : IsInvolution (w : G) := by
      have hw := orderOf_eq_prime_iff.mp hworderG
      exact ⟨hw.2, by simpa [pow_two] using hw.1⟩
    have hcomm : Commute (z : G) (w : G) := by
      rw [commute_iff_eq]
      exact setLike_mul_comm z.property w.property
    have hwz : (w : G) = (z : G) :=
      (hcommuting_unique (z : G) (w : G) hzI hwI hcomm).symm
    have hconj : g * (z : G) * g⁻¹ = (z : G) := hwz
    calc
      g * (z : G) = (g * (z : G) * g⁻¹) * g := by simp [mul_assoc]
      _ = (z : G) * g := by rw [hconj]
  let N : Subgroup G := pPrimeCore 2 G
  let q : G →* G ⧸ N := QuotientGroup.mk' N
  have hqker : q.ker = ⊥ := by
    change (QuotientGroup.mk' N).ker = ⊥
    rw [QuotientGroup.ker_mk']
    simpa [N] using hcore
  have hqinj : Function.Injective q :=
    (MonoidHom.ker_eq_bot_iff q).mp hqker
  have hqzcenter : q (z : G) ∈ Subgroup.center (G ⧸ N) := by
    rw [Subgroup.mem_center_iff]
    intro x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N x
    change q g * q (z : G) = q (z : G) * q g
    exact congrArg q (Subgroup.mem_center_iff.mp hzcenter g)
  let zbar : Subgroup.center (G ⧸ N) := ⟨q (z : G), hqzcenter⟩
  have hqorder : orderOf (q (z : G)) = 2 := by
    rw [orderOf_injective q hqinj]
    exact hzorderG
  have hzbarorder : orderOf zbar = 2 := by
    rw [← Subgroup.orderOf_coe zbar]
    exact hqorder
  simpa [N, hzbarorder] using orderOf_dvd_natCard zbar

private lemma example3_corefree_nonsimple_target
    {G : Type u} [Group G] [Finite G]
    (Q : Sylow 2 G) {n : ℕ}
    (hQ : Nonempty (Q ≃* QuaternionGroup (2 ^ (n - 2))))
    (hGnontrivial : Nontrivial G)
    (hcore : pPrimeCore 2 G = ⊥)
    (hnotSimple : ¬ IsSimpleGroup G)
    (hind : ∀ (M : Type u) [Group M] [Finite M],
      Nat.card M < Nat.card G →
      ∀ (S : Sylow 2 M) {m : ℕ}, 3 ≤ m →
        Nonempty (S ≃* QuaternionGroup (2 ^ (m - 2))) →
        2 ∣ Nat.card (Subgroup.center (M ⧸ pPrimeCore 2 M))) :
    2 ∣ Nat.card (Subgroup.center (G ⧸ pPrimeCore 2 G)) := by
  have hnotAll : ¬ ∀ M : Subgroup G,
      M.Normal → M = ⊥ ∨ M = ⊤ := by
    intro hAll
    exact hnotSimple ((isSimpleGroup_iff G).2 ⟨hGnontrivial, hAll⟩)
  push Not at hnotAll
  obtain ⟨M, hMnormal, hMnebot, hMnetop⟩ := hnotAll
  have hMeven : 2 ∣ Nat.card M := by
    by_contra hodd
    have hcop : Nat.Coprime 2 (Nat.card M) :=
      Nat.prime_two.coprime_iff_not_dvd.mpr hodd
    have hMle : M ≤ pPrimeCore 2 G := le_sSup ⟨hMnormal, hcop⟩
    have hMbot : M = ⊥ := by
      apply le_bot_iff.mp
      simpa [hcore] using hMle
    exact hMnebot hMbot
  let S : Sylow 2 M := default
  have hcoreM : pPrimeCore 2 M = ⊥ :=
    example3_subgroup_pPrimeCore_eq_bot hcore M hMnormal
  have hcenterEven : 2 ∣ Nat.card (Subgroup.center M) := by
    rcases example3_subgroup_sylow_cyclic_or_quaternion Q
        (example3_sylow_involution_unique Q hQ) M hMeven S with
      hScyclic | ⟨m, hm, hSquat⟩
    · exact example3_center_even_of_cyclic_sylow_corefree
        hcoreM hMeven S hScyclic
    · have hMcard_lt : Nat.card M < Nat.card G := by
        have hle : Nat.card M ≤ Nat.card G :=
          Nat.card_le_card_of_injective M.subtype M.subtype_injective
        exact lt_of_le_of_ne hle (fun hEq =>
          hMnetop ((Subgroup.card_eq_iff_eq_top M).1 hEq))
      exact example3_center_even_of_quotient_center_even_corefree hcoreM
        (hind M hMcard_lt S hm hSquat)
  exact example3_corefree_target_of_normal_center_even
    hcore M hMnormal hcenterEven
      (fun a b ha hb hab =>
        example3_commuting_involutions_eq Q
          (example3_sylow_involution_unique Q hQ) ha hb hab)

private lemma example3_argumentPow_eq_of_integer_valued_virtual
    {G : Type*} [Group G] [Finite G]
    {zeta : Section1.ClassFunction G}
    (hzetaVirtual : Theory.Character.IsVirtualCharacter zeta)
    (hzetaInt : ∀ g : G, ∃ n : ℤ, zeta g = (n : ℂ))
    {e : ℕ} (he : e.Coprime (Nat.card G)) :
    ∀ g : G, zeta (g ^ e) = zeta g := by
  obtain ⟨tau, htauRoot⟩ :=
    Section5.complex_galois_aut_pow_on_roots he
  intro g
  have hgal :
      tau (zeta g) = zeta (g ^ e) :=
    Section1.virtualCharacter_apply_galois_eq_argumentPow
      htauRoot hzetaVirtual dvd_rfl g
  obtain ⟨n, hn⟩ := hzetaInt g
  calc
    zeta (g ^ e) = tau (zeta g) := hgal.symm
    _ = tau (n : ℂ) := by rw [hn]
    _ = (n : ℂ) := by simp
    _ = zeta g := hn.symm
private lemma example3_equal_pair_arithmetic_core
    (d d3 f f3 a b : ℂ)
    (ha : a = 1 ∨ a = -1) (hb : b = 1 ∨ b = -1)
    (hd : d ≠ 0) (hd3 : d3 ≠ 0) (hf : f ≠ 0)
    (hdeg : 1 + 2 * a * d + b * d3 = 0)
    (hlin : 2 * a * f + b * f3 = 0)
    (hsq : 2 * a * f ^ 2 / d + b * f3 ^ 2 / d3 = 0) : False := by
  have hasq : a ^ 2 = 1 := by rcases ha with rfl | rfl <;> norm_num
  have hbsq : b ^ 2 = 1 := by rcases hb with rfl | rfl <;> norm_num
  have hbf : b * f3 = -2 * a * f := by linear_combination hlin
  have hf3sq : f3 ^ 2 = 4 * f ^ 2 := by
    calc
      f3 ^ 2 = b ^ 2 * f3 ^ 2 := by rw [hbsq]; simp
      _ = (b * f3) ^ 2 := by ring
      _ = (-2 * a * f) ^ 2 := by rw [hbf]
      _ = 4 * a ^ 2 * f ^ 2 := by ring
      _ = 4 * f ^ 2 := by rw [hasq]; ring
  field_simp [hd, hd3] at hsq
  rw [hf3sq] at hsq
  have hprod : f ^ 2 * (2 * a * d3 + 4 * b * d) = 0 := by
    linear_combination hsq
  have hf2 : f ^ 2 ≠ 0 := pow_ne_zero 2 hf
  have hrel : 2 * a * d3 + 4 * b * d = 0 :=
    (mul_eq_zero.mp hprod).resolve_left hf2
  have htail : 2 * a * d + b * d3 = 0 := by
    linear_combination (a * b / 2) * hrel -
      (b * d3) * hasq - (2 * a * d) * hbsq
  have hone : (1 : ℂ) = 0 := by linear_combination hdeg - htail
  norm_num at hone

private lemma example3_three_constituent_argumentPow_fixed
    {G : Type*} [Group G] [Finite G]
    (zeta : Section1.ClassFunction G)
    (chi : Fin 3 → Section1.ClassFunction G)
    (epsilon d f : Fin 3 → ℂ)
    (t : G)
    (hchi_irreducible : ∀ i, Section1.IsIrreducibleCharacterOnGroup (chi i))
    (hchi_injective : Function.Injective chi)
    (hchi_nonprincipal : ∀ i, chi i ≠ Section1.principalCharacter G)
    (hepsilon_sign : ∀ i, epsilon i = 1 ∨ epsilon i = -1)
    (hzeta_decomposition : zeta = Section1.principalCharacter G +
      Section1.weightedFamilySum epsilon chi)
    (hd : ∀ i, d i = chi i 1)
    (hf : ∀ i, f i = d i - chi i t)
    (hsum_d : 1 + ∑ i, epsilon i * d i = 0)
    (hsum_f : ∑ i, epsilon i * f i = 0)
    (hsum_f_sq : ∑ i, epsilon i * f i ^ 2 / d i = 0)
    (hd_ne : ∀ i, d i ≠ 0)
    (hf_ne : ∀ i, f i ≠ 0)
    {a : ℕ} (ha : a.Coprime (Nat.card G))
    (hzeta_pow : ∀ g : G, zeta (g ^ a) = zeta g)
    (ht_pow : t ^ a = t) :
    ∀ i g, chi i (g ^ a) = chi i g := by
  classical
  let chipow : Fin 3 → Section1.ClassFunction G := fun i g => chi i (g ^ a)
  have hchipow_irreducible : ∀ i,
      Section1.IsIrreducibleCharacterOnGroup (chipow i) := by
    intro i
    exact Section5.isIrreducibleCharacterOnGroup_argumentPow_pf59
      (hchi_irreducible i) ha
  have hpow_surj : Function.Surjective (fun g : G => g ^ a) :=
    Section5.pow_surjective_of_coprime_natCard_pf59 ha
  have hchipow_injective : Function.Injective chipow := by
    intro i j hij
    apply hchi_injective
    funext g
    obtain ⟨x, rfl⟩ := hpow_surj g
    exact congrFun hij x
  have hchipow_nonprincipal : ∀ i,
      chipow i ≠ Section1.principalCharacter G := by
    intro i hi
    apply hchi_nonprincipal i
    funext g
    obtain ⟨x, rfl⟩ := hpow_surj g
    simpa [chipow, Section1.principalCharacter] using congrFun hi x
  have hzeta_decomposition_pow : zeta = Section1.principalCharacter G +
      Section1.weightedFamilySum epsilon chipow := by
    funext g
    calc
      zeta g = zeta (g ^ a) := (hzeta_pow g).symm
      _ = (Section1.principalCharacter G +
          Section1.weightedFamilySum epsilon chi) (g ^ a) :=
        congrFun hzeta_decomposition (g ^ a)
      _ = (Section1.principalCharacter G +
          Section1.weightedFamilySum epsilon chipow) g := by
        simp [Section1.principalCharacter, Section1.weightedFamilySum, chipow]
  have hprincipal_chipow : ∀ i,
      Section1.scalarProduct G (Section1.principalCharacter G) (chipow i) = 0 := by
    intro i
    calc
      _ = star (Section1.scalarProduct G (chipow i)
          (Section1.principalCharacter G)) :=
        (Section1.scalarProduct_star_swap _ _).symm
      _ = 0 := by rw [Section1.scalarProduct_irreducibleCharacter_principal_eq_zero_of_ne
        (hchipow_irreducible i) (hchipow_nonprincipal i)]; simp
  have hchipow_orth : ∀ i j,
      Section1.scalarProduct G (chipow i) (chipow j) = if i = j then 1 else 0 := by
    intro i j
    split
    next hij =>
      subst j
      exact Section1.scalarProduct_irreducibleCharacter_self
        (G := G) (hchipow_irreducible i)
    next hij =>
      exact Section1.scalarProduct_irreducibleCharacter_eq_zero_of_ne
        (hchipow_irreducible i) (hchipow_irreducible j)
        (fun h => hij (hchipow_injective h))
  have hsp_pow : ∀ i,
      Section1.scalarProduct G zeta (chipow i) = epsilon i := by
    intro i
    rw [hzeta_decomposition_pow, Section1.scalarProduct_add_left,
      Section1.scalarProduct_weightedFamilySum_left, hprincipal_chipow i]
    simp [hchipow_orth]
  have hprincipal_chi : ∀ i,
      Section1.scalarProduct G (Section1.principalCharacter G) (chi i) = 0 := by
    intro i
    calc
      _ = star (Section1.scalarProduct G (chi i)
          (Section1.principalCharacter G)) :=
        (Section1.scalarProduct_star_swap _ _).symm
      _ = 0 := by rw [Section1.scalarProduct_irreducibleCharacter_principal_eq_zero_of_ne
        (hchi_irreducible i) (hchi_nonprincipal i)]; simp
  have hchi_orth : ∀ i j,
      Section1.scalarProduct G (chi i) (chi j) = if i = j then 1 else 0 := by
    intro i j
    split
    next hij =>
      subst j
      exact Section1.scalarProduct_irreducibleCharacter_self
        (G := G) (hchi_irreducible i)
    next hij =>
      exact Section1.scalarProduct_irreducibleCharacter_eq_zero_of_ne
        (hchi_irreducible i) (hchi_irreducible j)
        (fun h => hij (hchi_injective h))
  have hsp_chi : ∀ i,
      Section1.scalarProduct G zeta (chi i) = epsilon i := by
    intro i
    rw [hzeta_decomposition, Section1.scalarProduct_add_left,
      Section1.scalarProduct_weightedFamilySum_left, hprincipal_chi i]
    simp [hchi_orth]
  have hperm : ∀ i, ∃ j, chi j = chipow i := by
    intro i
    by_contra hnone
    push Not at hnone
    have hzero : Section1.scalarProduct G zeta (chipow i) = 0 := by
      rw [hzeta_decomposition, Section1.scalarProduct_add_left,
        Section1.scalarProduct_weightedFamilySum_left, hprincipal_chipow i]
      simp only [zero_add]
      apply Finset.sum_eq_zero
      intro j _hj
      rw [Section1.scalarProduct_irreducibleCharacter_eq_zero_of_ne
        (hchi_irreducible j) (hchipow_irreducible i) (hnone j)]
      simp
    have hi0 : epsilon i ≠ 0 := by
      rcases hepsilon_sign i with h | h <;> rw [h] <;> norm_num
    exact hi0 ((hsp_pow i).symm.trans hzero)
  intro i g
  obtain ⟨j, hj⟩ := hperm i
  have heps : epsilon i = epsilon j := by
    rw [← hsp_pow i, ← hsp_chi j, hj]
  have hdij : d i = d j := by
    rw [hd i, hd j, hj]
    simp [chipow]
  have hfij : f i = f j := by
    rw [hf i, hf j, hdij, hj]
    simp [chipow, ht_pow]
  have hsum_d_three :
      1 + epsilon 0 * d 0 + epsilon 1 * d 1 + epsilon 2 * d 2 = 0 := by
    simpa [Fin.sum_univ_three, add_assoc] using hsum_d
  have hsum_f_three :
      epsilon 0 * f 0 + epsilon 1 * f 1 + epsilon 2 * f 2 = 0 := by
    simpa [Fin.sum_univ_three, add_assoc] using hsum_f
  have hsum_f_sq_three :
      epsilon 0 * f 0 ^ 2 / d 0 + epsilon 1 * f 1 ^ 2 / d 1 +
          epsilon 2 * f 2 ^ 2 / d 2 = 0 := by
    simpa [Fin.sum_univ_three, add_assoc] using hsum_f_sq
  have hpair (i j k : Fin 3)
      (hepsij : epsilon i = epsilon j)
      (hdij' : d i = d j) (hfij' : f i = f j)
      (hdegijk : 1 + epsilon i * d i + epsilon j * d j +
        epsilon k * d k = 0)
      (hlinijk : epsilon i * f i + epsilon j * f j +
        epsilon k * f k = 0)
      (hsqijk : epsilon i * f i ^ 2 / d i +
        epsilon j * f j ^ 2 / d j + epsilon k * f k ^ 2 / d k = 0) : False := by
    have hdegcore :
        1 + 2 * epsilon i * d i + epsilon k * d k = 0 := by
      rw [← hepsij, ← hdij'] at hdegijk
      linear_combination hdegijk
    have hlincore :
        2 * epsilon i * f i + epsilon k * f k = 0 := by
      rw [← hepsij, ← hfij'] at hlinijk
      linear_combination hlinijk
    have hsqcore :
        2 * epsilon i * f i ^ 2 / d i + epsilon k * f k ^ 2 / d k = 0 := by
      rw [← hepsij, ← hdij', ← hfij'] at hsqijk
      linear_combination hsqijk
    exact example3_equal_pair_arithmetic_core (d i) (d k) (f i) (f k) (epsilon i) (epsilon k)
      (hepsilon_sign i) (hepsilon_sign k) (hd_ne i) (hd_ne k) (hf_ne i)
      hdegcore hlincore hsqcore
  have hij : i = j := by
    by_contra hij
    fin_cases i <;> fin_cases j
    all_goals try { exact hij rfl }
    · exact hpair 0 1 2 heps hdij hfij
        (by linear_combination hsum_d_three)
        (by linear_combination hsum_f_three)
        (by linear_combination hsum_f_sq_three)
    · exact hpair 0 2 1 heps hdij hfij
        (by linear_combination hsum_d_three)
        (by linear_combination hsum_f_three)
        (by linear_combination hsum_f_sq_three)
    · exact hpair 1 0 2 heps hdij hfij
        (by linear_combination hsum_d_three)
        (by linear_combination hsum_f_three)
        (by linear_combination hsum_f_sq_three)
    · exact hpair 1 2 0 heps hdij hfij
        (by linear_combination hsum_d_three)
        (by linear_combination hsum_f_three)
        (by linear_combination hsum_f_sq_three)
    · exact hpair 2 0 1 heps hdij hfij
        (by linear_combination hsum_d_three)
        (by linear_combination hsum_f_three)
        (by linear_combination hsum_f_sq_three)
    · exact hpair 2 1 0 heps hdij hfij
        (by linear_combination hsum_d_three)
        (by linear_combination hsum_f_three)
        (by linear_combination hsum_f_sq_three)
  subst j
  exact congrFun hj.symm g

private lemma example3_character_mul_inv_eq_of_argumentPow_fixed
    {G : Type*} [Group G] [Finite G]
    (Q : Sylow 2 G) (hQcard : Nat.card Q = 8)
    {m : ℕ} (hm : m ∣ Q.index)
    {x u : G} (hxOrder : orderOf x = 4) (hxu : Commute x u)
    (huOrder : orderOf u ∣ m)
    {A : Type*} (chi : G → A)
    (hfixed : ∀ {a : ℕ}, a.Coprime (Nat.card G) →
      ∀ g : G, chi (g ^ a) = chi g) :
    ∃ e : ℕ, e.Coprime (Nat.card G) ∧
      (x * u) ^ e = x * u⁻¹ ∧ chi (x * u) = chi (x * u⁻¹) := by
  have hindexEight : Q.index.Coprime 8 := by
    simpa [hQcard] using (Q.card_coprime_index).symm
  have hk : IsCoprime (-1 : ℤ) (Q.index : ℤ) := by
    exact ⟨-1, 0, by ring⟩
  obtain ⟨w, hwa, hwb⟩ :=
    Section1.zmod_units_crt_exists_of_coprime hindexEight
      (ZMod.unitOfIsCoprime (-1 : ℤ) hk)
  let e : ℕ := (w : ZMod (Q.index * 8)).val
  have hn : Q.index * 8 ≠ 0 :=
    mul_ne_zero Subgroup.index_ne_zero_of_finite (by norm_num)
  have heIndex : (e : ℤ) ≡ (-1 : ℤ) [ZMOD Q.index] :=
    Section1.zmod_units_crt_val_modEq_left_int hn hk hwa
  have heEight : (e : ℤ) ≡ (1 : ℤ) [ZMOD 8] :=
    Section1.zmod_units_crt_val_modEq_right_one hn hwb
  have heCoprimeProduct : e.Coprime (Q.index * 8) := by
    simpa [e] using ZMod.val_coe_unit_coprime w
  have hcardG : Nat.card G = Q.index * 8 := by
    calc
      Nat.card G = Nat.card Q * Q.index := Q.card_mul_index.symm
      _ = 8 * Q.index := by rw [hQcard]
      _ = Q.index * 8 := Nat.mul_comm _ _
  have heCoprime : e.Coprime (Nat.card G) := by
    rw [hcardG]
    exact heCoprimeProduct
  have hxMod : (e : ℤ) ≡ (1 : ℤ) [ZMOD orderOf x] := by
    rw [hxOrder]
    exact Int.ModEq.of_dvd (by norm_num) heEight
  have hxPow : x ^ e = x := by
    simpa only [zpow_natCast, zpow_one] using
      ((zpow_eq_zpow_iff_modEq (x := x)).2 hxMod)
  have huOrderIndex : orderOf u ∣ Q.index := huOrder.trans hm
  have huOrderIndexInt : (orderOf u : ℤ) ∣ (Q.index : ℤ) := by
    exact_mod_cast huOrderIndex
  have huMod : (e : ℤ) ≡ (-1 : ℤ) [ZMOD orderOf u] :=
    Int.ModEq.of_dvd huOrderIndexInt heIndex
  have huPow : u ^ e = u⁻¹ := by
    simpa only [zpow_natCast, zpow_neg_one] using
      ((zpow_eq_zpow_iff_modEq (x := u)).2 huMod)
  have hproductPow : (x * u) ^ e = x * u⁻¹ := by
    rw [hxu.mul_pow, hxPow, huPow]
  refine ⟨e, heCoprime, hproductPow, ?_⟩
  calc
    chi (x * u) = chi ((x * u) ^ e) := (hfixed heCoprime (x * u)).symm
    _ = chi (x * u⁻¹) := congrArg chi hproductPow

private lemma example3_positive_odd_scalar_ge_three
    {N : Type*} [Fintype N]
    (a : N → ℤ) (u0 : N) (epsilon m : ℤ)
    (hepsilon : epsilon = 1 ∨ epsilon = -1)
    (hu0odd : Odd (a u0))
    (hsum : ∑ u, a u = epsilon * Nat.card N)
    (hsq : ∑ u, a u ^ 2 = m * Nat.card N)
    (hmodd : Odd m)
    (hne : a u0 ≠ epsilon) : 3 ≤ m := by
  have hpointwise : ∀ u, epsilon * a u ≤ a u ^ 2 := by
    intro u
    rcases hepsilon with rfl | rfl <;> nlinarith [sq_nonneg (a u)]
  have hu0nezero : a u0 ≠ 0 := by
    obtain ⟨k, hk⟩ := hu0odd
    omega
  have hstrict : epsilon * a u0 < a u0 ^ 2 := by
    have hle := hpointwise u0
    apply lt_of_le_of_ne hle
    intro heq
    apply hne
    rcases hepsilon with rfl | rfl
    · have hfac : a u0 * (a u0 - 1) = 0 := by nlinarith
      rcases mul_eq_zero.mp hfac with hzero | hone
      · exact False.elim (hu0nezero hzero)
      · omega
    · have hfac : a u0 * (a u0 + 1) = 0 := by nlinarith
      rcases mul_eq_zero.mp hfac with hzero | hneg
      · exact False.elim (hu0nezero hzero)
      · omega
  have hsumlt :
      ∑ u, epsilon * a u < ∑ u, a u ^ 2 := by
    exact Finset.sum_lt_sum (fun u _hu => hpointwise u)
      ⟨u0, Finset.mem_univ u0, hstrict⟩
  rw [← Finset.mul_sum, hsum, hsq] at hsumlt
  let : Nonempty N := ⟨u0⟩
  have hcardpos : (0 : ℤ) < Nat.card N := by
    exact_mod_cast Nat.card_pos (α := N)
  have hepssq : epsilon * epsilon = 1 := by
    rcases hepsilon with rfl | rfl <;> norm_num
  rw [← mul_assoc, hepssq, one_mul] at hsumlt
  have hmgt : 1 < m := by
    nlinarith
  obtain ⟨k, hk⟩ := hmodd
  omega
private lemma example3_row_orthogonality_arithmetic_core
    {A : Type*} [Fintype A] [DecidableEq A]
    (S : Finset A) (a : A → ℤ) (u0 : A) (epsilon m : ℤ)
    (hepsilon : epsilon = 1 ∨ epsilon = -1)
    (hu0 : u0 ∉ S)
    (hpointwise : ∀ u ∈ Finset.univ \ S, -epsilon * a u ≤ a u ^ 2)
    (hstrict : -epsilon * a u0 < a u0 ^ 2)
    (hrow : ∑ u, a u ^ 2 = Fintype.card A)
    (hsupportSq : 4 * ∑ u ∈ S, a u ^ 2 = Fintype.card A * m)
    (hsum : ∑ u, a u = 0)
    (hsupportLin : 4 * ∑ u ∈ S, epsilon * a u = Fintype.card A)
    (hm : 3 ≤ m) : False := by
  have hu0mem : u0 ∈ Finset.univ \ S := by simp [hu0]
  have hcompStrict :
      ∑ u ∈ Finset.univ \ S, -epsilon * a u <
        ∑ u ∈ Finset.univ \ S, a u ^ 2 := by
    exact Finset.sum_lt_sum (fun u hu ↦ hpointwise u hu)
      ⟨u0, hu0mem, hstrict⟩
  have hsplitA :
      ∑ u, a u = (∑ u ∈ S, a u) + ∑ u ∈ Finset.univ \ S, a u := by
    rw [← Finset.sum_sdiff (Finset.subset_univ S)]
    simp [add_comm]
  have hcompA :
      ∑ u ∈ Finset.univ \ S, a u = -(∑ u ∈ S, a u) := by
    rw [hsum] at hsplitA
    omega
  have hepsSq : epsilon * epsilon = 1 := by
    rcases hepsilon with rfl | rfl <;> norm_num
  have hsupportLin' :
      4 * (epsilon * ∑ u ∈ S, a u) = Fintype.card A := by
    simpa [Finset.mul_sum] using hsupportLin
  have hcompLin :
      4 * (∑ u ∈ Finset.univ \ S, -epsilon * a u) = Fintype.card A := by
    rw [show Finset.sum (Finset.univ \ S) (fun u => -epsilon * a u) =
        -epsilon * Finset.sum (Finset.univ \ S) a by
          rw [Finset.mul_sum]]
    rw [hcompA]
    have : -epsilon * -(∑ u ∈ S, a u) =
        epsilon * ∑ u ∈ S, a u := by ring
    rw [this]
    exact hsupportLin'
  have hcompSq :
      Fintype.card A < 4 * ∑ u ∈ Finset.univ \ S, a u ^ 2 := by
    nlinarith
  have hsplitSq :
      ∑ u, a u ^ 2 = (∑ u ∈ S, a u ^ 2) +
        ∑ u ∈ Finset.univ \ S, a u ^ 2 := by
    rw [← Finset.sum_sdiff (Finset.subset_univ S)]
    simp [add_comm]
  have hcardNonneg : (0 : ℤ) ≤ Fintype.card A := by positivity
  norm_num at hrow hsupportSq hsupportLin hcompLin hcompSq ⊢
  nlinarith

set_option maxHeartbeats 400000 in
private lemma example3_defect_four_mul_of_order_values
    {G : Type*} [Group G] [Finite G]
    (chi : Section1.ClassFunction G)
    (m : ℕ) (rho : Representation ℂ G (Fin m → ℂ))
    (hchar : chi = rho.character)
    (t x : G) (_ht : orderOf t = 2) (hx : orderOf x = 4)
    (epsilon : ℂ)
    (hfourValue : ∀ y : G, orderOf y = 4 → chi y = epsilon)
    (htwoValue : ∀ y : G, orderOf y = 2 → chi y = chi t) :
    ∃ c : ℕ, chi 1 - chi t = ((4 * c : ℕ) : ℂ) := by
  classical
  let V := Subgroup.zpowers x
  let : Fintype V := Fintype.ofFinite V
  have hVcard : Nat.card V = 4 := by
    change Nat.card (Subgroup.zpowers x) = 4
    rw [Nat.card_zpowers, hx]
  let : NeZero (Nat.card V) := ⟨by rw [hVcard]; norm_num⟩
  let e : Multiplicative (ZMod 4) ≃* V := by
    rw [← hVcard]
    exact zmodCyclicMulEquiv (inferInstance : IsCyclic V)
  let zchar : Multiplicative (ZMod 4) →* ℂˣ :=
    Circle.toUnits.comp (ZMod.toCircle (N := 4)).toMonoidHom
  let lam : V →* ℂˣ := zchar.comp e.symm.toMonoidHom
  let sigma : Representation ℂ V ℂ := {
    toFun y := (lam y : ℂ) • LinearMap.id
    map_one' := by ext; simp
    map_mul' a b := by ext; simp [map_mul, mul_smul, mul_comm]
    }
  let rhoV : Representation ℂ V (Fin m → ℂ) := rho.comp V.subtype
  let c := Module.finrank ℂ (sigma.IntertwiningMap rhoV)
  have hscalar :
      Section1.scalarProduct V rhoV.character sigma.character = (c : ℂ) := by
    simpa [c] using
      (Section1.scalarProduct_representation_char_eq_finrank
        (rho := sigma) (sigma := rhoV))
  have hsigma (a : Multiplicative (ZMod 4)) :
      sigma.character (e a) = (zchar a : ℂ) := by
    simp [sigma, lam, Representation.character]
  have hrhoV (a : Multiplicative (ZMod 4)) :
      rhoV.character (e a) = chi ((e a : V) : G) := by
    simp [rhoV, Representation.character, hchar]
  have horder (a : ZMod 4) :
      orderOf (((e (Multiplicative.ofAdd a) : V) : G)) = addOrderOf a := by
    rw [Subgroup.orderOf_coe, e.orderOf_eq]
    rfl
  have hvalue0 :
      chi (((e (Multiplicative.ofAdd (0 : ZMod 4)) : V) : G)) = chi 1 := by simp
  have hvalue1 :
      chi (((e (Multiplicative.ofAdd (1 : ZMod 4)) : V) : G)) = epsilon := by
    apply hfourValue
    rw [horder]
    change addOrderOf ((1 : ℕ) : ZMod 4) = 4
    rw [ZMod.addOrderOf_coe 1 (by norm_num)]
    norm_num
  have hvalue2 :
      chi (((e (Multiplicative.ofAdd (2 : ZMod 4)) : V) : G)) = chi t := by
    apply htwoValue
    rw [horder]
    change addOrderOf ((2 : ℕ) : ZMod 4) = 2
    rw [ZMod.addOrderOf_coe 2 (by norm_num)]
    norm_num
  have hvalue3 :
      chi (((e (Multiplicative.ofAdd (3 : ZMod 4)) : V) : G)) = epsilon := by
    apply hfourValue
    rw [horder]
    change addOrderOf ((3 : ℕ) : ZMod 4) = 4
    rw [ZMod.addOrderOf_coe 3 (by norm_num)]
    norm_num
  let a1 : Multiplicative (ZMod 4) := Multiplicative.ofAdd 1
  let a2 : Multiplicative (ZMod 4) := Multiplicative.ofAdd 2
  let a3 : Multiplicative (ZMod 4) := Multiplicative.ofAdd 3
  have hzchar_inj : Function.Injective zchar := by
    intro a b hab
    apply Multiplicative.ext
    apply ZMod.injective_toCircle
    apply Subtype.ext
    exact congrArg Units.val hab
  have hz0 : (zchar (Multiplicative.ofAdd (0 : ZMod 4)) : ℂ) = 1 := by simp [zchar]
  have ha2sq : a2 ^ 2 = 1 := by decide
  have hz2sqU : zchar a2 ^ 2 = 1 := by rw [← map_pow, ha2sq, map_one]
  have hz2sq : (zchar a2 : ℂ) ^ 2 = 1 := congrArg Units.val hz2sqU
  have hz2neU : zchar a2 ≠ 1 := by
    intro hz
    have hz' : zchar a2 = zchar 1 := by simpa using hz
    exact (by decide : a2 ≠ 1) (hzchar_inj hz')
  have hz2ne : (zchar a2 : ℂ) ≠ 1 := by
    intro hz
    exact hz2neU (Units.ext hz)
  have hz2 : (zchar a2 : ℂ) = -1 := by
    rcases (sq_eq_one_iff).mp hz2sq with h | h
    · exact (hz2ne h).elim
    · exact h
  have ha1sq : a1 ^ 2 = a2 := by decide
  have hz1sqU : zchar a1 ^ 2 = zchar a2 := by rw [← map_pow, ha1sq]
  have hz1sq : (zchar a1 : ℂ) ^ 2 = -1 := by
    have h := congrArg Units.val hz1sqU
    simpa [hz2] using h
  have hz1ne : (zchar a1 : ℂ) ≠ 0 := Units.ne_zero _
  have hz1inv : (zchar a1 : ℂ)⁻¹ = -(zchar a1 : ℂ) := by
    apply mul_left_cancel₀ hz1ne
    rw [mul_inv_cancel₀ hz1ne]
    calc
      (1 : ℂ) = -((zchar a1 : ℂ) ^ 2) := by rw [hz1sq]; norm_num
      _ = (zchar a1 : ℂ) * (-(zchar a1 : ℂ)) := by ring
  have ha3inv : a3 = a1⁻¹ := by decide
  have hz3 : (zchar a3 : ℂ) = (zchar a1 : ℂ)⁻¹ := by
    rw [ha3inv, map_inv]
    rfl
  have hstar (a : Multiplicative (ZMod 4)) :
      star (zchar a : ℂ) = (zchar a : ℂ)⁻¹ := by
    change star ((ZMod.toCircle a.toAdd : Circle) : ℂ) =
      (((ZMod.toCircle a.toAdd : Circle) : ℂ))⁻¹
    exact (Circle.coe_inv_eq_conj (ZMod.toCircle a.toAdd)).symm
  have hcancel : star (zchar a1 : ℂ) + star (zchar a3 : ℂ) = 0 := by
    rw [hstar, hstar, hz3, inv_inv, hz1inv]
    ring
  have hscalarCalc :
      Section1.scalarProduct V rhoV.character sigma.character =
        (chi 1 - chi t) / 4 := by
    unfold Section1.scalarProduct
    rw [hVcard]
    let eFin : Fin 4 ≃ Multiplicative (ZMod 4) :=
      (ZMod.finEquiv 4).toEquiv.trans Multiplicative.ofAdd
    rw [← Equiv.sum_comp e.toEquiv]
    rw [← Equiv.sum_comp eFin]
    rw [Fin.sum_univ_four]
    change (4 : ℂ)⁻¹ *
      (rhoV.character (e (Multiplicative.ofAdd (0 : ZMod 4))) *
          star (sigma.character (e (Multiplicative.ofAdd (0 : ZMod 4)))) +
       rhoV.character (e (Multiplicative.ofAdd (1 : ZMod 4))) *
          star (sigma.character (e (Multiplicative.ofAdd (1 : ZMod 4)))) +
       rhoV.character (e (Multiplicative.ofAdd (2 : ZMod 4))) *
          star (sigma.character (e (Multiplicative.ofAdd (2 : ZMod 4)))) +
       rhoV.character (e (Multiplicative.ofAdd (3 : ZMod 4))) *
          star (sigma.character (e (Multiplicative.ofAdd (3 : ZMod 4))))) = _
    rw [hrhoV, hrhoV, hrhoV, hrhoV, hsigma, hsigma, hsigma, hsigma]
    rw [hvalue0, hvalue1, hvalue2, hvalue3]
    change (4 : ℂ)⁻¹ *
      (chi 1 * star (zchar (Multiplicative.ofAdd 0) : ℂ) +
       epsilon * star (zchar a1 : ℂ) +
       chi t * star (zchar a2 : ℂ) +
       epsilon * star (zchar a3 : ℂ)) = _
    rw [hz0, hz2]
    simp only [star_one, mul_one, star_neg]
    rw [hstar a1, hstar a3, hz3, inv_inv, hz1inv]
    ring
  refine ⟨c, ?_⟩
  rw [hscalarCalc] at hscalar
  have hfour : (4 : ℂ) ≠ 0 := by norm_num
  field_simp [hfour] at hscalar
  calc
    chi 1 - chi t = 4 * (c : ℂ) := hscalar
    _ = ((4 * c : ℕ) : ℂ) := by push_cast; ring

set_option maxHeartbeats 400000 in
private lemma example3_q8_sum_eq_eight_mul
    {G : Type*} [Group G] [Finite G]
    (chi : Section1.ClassFunction G)
    (m : ℕ) (rho : Representation ℂ G (Fin m → ℂ))
    (hchar : chi = rho.character)
    (Q : Sylow 2 G) (hQcard : Nat.card Q = 8)
    (qeq : Q ≃* QuaternionGroup 2)
    (t : G) (epsilon : ℂ)
    (hfourValue : ∀ y : G, orderOf y = 4 → chi y = epsilon)
    (htwoValue : ∀ y : G, orderOf y = 2 → chi y = chi t) :
    ∃ c : ℕ, chi 1 + chi t + 6 * epsilon = ((8 * c : ℕ) : ℂ) := by
  classical
  let : Fintype Q := Fintype.ofFinite Q
  let rhoQ : Representation ℂ Q (Fin m → ℂ) := rho.comp (Q : Subgroup G).subtype
  let triv : Representation ℂ Q ℂ := Representation.trivial ℂ Q ℂ
  let c := Module.finrank ℂ (triv.IntertwiningMap rhoQ)
  have hscalar :
      Section1.scalarProduct Q rhoQ.character triv.character = (c : ℂ) := by
    simpa [c] using
      (Section1.scalarProduct_representation_char_eq_finrank
        (rho := triv) (sigma := rhoQ))
  have hrhoQ (q : Q) : rhoQ.character q = chi (q : G) := by
    simp [rhoQ, Representation.character, hchar]
  let qsumEquiv : ZMod 4 ⊕ ZMod 4 ≃ QuaternionGroup 2 := {
    toFun
      | Sum.inl z => QuaternionGroup.a z
      | Sum.inr z => QuaternionGroup.xa z
    invFun
      | QuaternionGroup.a z => Sum.inl z
      | QuaternionGroup.xa z => Sum.inr z
    left_inv := by rintro (z | z) <;> rfl
    right_inv := by rintro (z | z) <;> rfl
    }
  have horder (q : QuaternionGroup 2) :
      orderOf (((qeq.symm q : Q) : G)) = orderOf q := by
    rw [Subgroup.orderOf_coe, qeq.symm.orderOf_eq]
  have ha0 : chi (((qeq.symm (QuaternionGroup.a 0) : Q) : G)) = chi 1 := by simp
  have ha1 : chi (((qeq.symm (QuaternionGroup.a 1) : Q) : G)) = epsilon := by
    apply hfourValue
    rw [horder, QuaternionGroup.orderOf_a_one]
  have ha2 : chi (((qeq.symm (QuaternionGroup.a 2) : Q) : G)) = chi t := by
    apply htwoValue
    rw [horder, QuaternionGroup.orderOf_a]
    have hv : ZMod.val (2 : ZMod 4) = 2 := by decide
    rw [hv]
    norm_num
  have ha3 : chi (((qeq.symm (QuaternionGroup.a 3) : Q) : G)) = epsilon := by
    apply hfourValue
    rw [horder, QuaternionGroup.orderOf_a]
    have hv : ZMod.val (3 : ZMod 4) = 3 := by decide
    rw [hv]
    norm_num
  have hxa (z : ZMod 4) :
      chi (((qeq.symm (QuaternionGroup.xa z) : Q) : G)) = epsilon := by
    apply hfourValue
    rw [horder, QuaternionGroup.orderOf_xa]
  have hsum :
      ∑ q : Q, chi (q : G) = chi 1 + chi t + 6 * epsilon := by
    let g : QuaternionGroup 2 → ℂ := fun q => chi ((qeq.symm q : Q) : G)
    calc
      ∑ q : Q, chi (q : G) = ∑ q : QuaternionGroup 2, g q := by
        simpa [g] using (Equiv.sum_comp qeq.toEquiv g)
      _ = ∑ z : ZMod 4 ⊕ ZMod 4, g (qsumEquiv z) := by
        exact (Equiv.sum_comp qsumEquiv g).symm
      _ = (∑ z : ZMod 4, g (QuaternionGroup.a z)) +
          ∑ z : ZMod 4, g (QuaternionGroup.xa z) := by
        rw [Fintype.sum_sum_type]
        rfl
      _ = chi 1 + chi t + 6 * epsilon := by
        let eFin : Fin 4 ≃ ZMod 4 := (ZMod.finEquiv 4).toEquiv
        rw [← Equiv.sum_comp eFin, ← Equiv.sum_comp eFin]
        rw [Fin.sum_univ_four, Fin.sum_univ_four]
        change
          (chi (((qeq.symm (QuaternionGroup.a 0) : Q) : G)) +
           chi (((qeq.symm (QuaternionGroup.a 1) : Q) : G)) +
           chi (((qeq.symm (QuaternionGroup.a 2) : Q) : G)) +
           chi (((qeq.symm (QuaternionGroup.a 3) : Q) : G))) +
          (chi (((qeq.symm (QuaternionGroup.xa 0) : Q) : G)) +
           chi (((qeq.symm (QuaternionGroup.xa 1) : Q) : G)) +
           chi (((qeq.symm (QuaternionGroup.xa 2) : Q) : G)) +
           chi (((qeq.symm (QuaternionGroup.xa 3) : Q) : G))) = _
        rw [ha0, ha1, ha2, ha3, hxa, hxa, hxa, hxa]
        ring
  have hscalarCalc :
      Section1.scalarProduct Q rhoQ.character triv.character =
        (chi 1 + chi t + 6 * epsilon) / 8 := by
    unfold Section1.scalarProduct
    rw [hQcard]
    simp_rw [hrhoQ]
    simp [triv, Representation.character, hsum, div_eq_mul_inv, mul_comm]
  refine ⟨c, ?_⟩
  rw [hscalarCalc] at hscalar
  have height : (8 : ℂ) ≠ 0 := by norm_num
  field_simp [height] at hscalar
  calc
    chi 1 + chi t + 6 * epsilon = 8 * (c : ℂ) := hscalar
    _ = ((8 * c : ℕ) : ℂ) := by push_cast; ring

private lemma example3_stage_k_mod_four
    (D E eps C K : ℤ)
    (hF : D - E = 4 * C)
    (hSum : D + E + 6 * eps = 8 * K)
    (h8 : 8 ∣ D - E) :
    (D : ZMod 4) = (eps : ZMod 4) := by
  rcases h8 with ⟨u, hu⟩
  have hd : D - eps = 4 * (K + u - eps) := by omega
  have hdZ := congrArg (fun z : ℤ => (z : ZMod 4)) hd
  push_cast at hdZ
  have hfour : (4 : ZMod 4) = 0 := by decide
  rw [hfour, zero_mul] at hdZ
  exact sub_eq_zero.mp hdZ

set_option maxHeartbeats 400000 in
private lemma example3_stage_k_positive_four
    {G : Type*} [Group G] [Finite G]
    (chi : Section1.ClassFunction G)
    (m : ℕ) (rho : Representation ℂ G (Fin m → ℂ))
    (hchar : chi = rho.character)
    (t x : G) (ht : orderOf t = 2) (hx : orderOf x = 4)
    (epsilon : ℂ)
    (hfourValue : ∀ y : G, orderOf y = 4 → chi y = epsilon)
    (htwoValue : ∀ y : G, orderOf y = 2 → chi y = chi t)
    (fZ : ℤ) (hfZ : chi 1 - chi t = (fZ : ℂ)) (hfne : fZ ≠ 0) :
    0 < fZ ∧ 4 ∣ fZ := by
  obtain ⟨c, hc⟩ := example3_defect_four_mul_of_order_values
    chi m rho hchar t x ht hx epsilon hfourValue htwoValue
  have hEq : fZ = 4 * (c : ℤ) := by
    exact_mod_cast hfZ.symm.trans hc
  have hcne : c ≠ 0 := by
    intro hc0
    apply hfne
    rw [hEq, hc0]
    norm_num
  have hcpos : 0 < c := Nat.pos_of_ne_zero hcne
  constructor
  · rw [hEq]
    omega
  · exact ⟨(c : ℤ), hEq⟩

set_option maxHeartbeats 400000 in
private lemma example3_stage_k_degree_mod_four
    {G : Type*} [Group G] [Finite G]
    (chi : Section1.ClassFunction G)
    (m : ℕ) (rho : Representation ℂ G (Fin m → ℂ))
    (hchar : chi = rho.character)
    (Q : Sylow 2 G) (hQcard : Nat.card Q = 8)
    (qeq : Q ≃* QuaternionGroup 2)
    (t : G) (epsilon : ℂ)
    (hfourValue : ∀ y : G, orderOf y = 4 → chi y = epsilon)
    (htwoValue : ∀ y : G, orderOf y = 2 → chi y = chi t)
    (dZ eZ fZ epsZ : ℤ)
    (hdchi : chi 1 = (dZ : ℂ))
    (hechi : chi t = (eZ : ℂ))
    (heps : epsilon = (epsZ : ℂ))
    (hf : fZ = dZ - eZ)
    (h8 : 8 ∣ fZ) :
    (dZ : ZMod 4) = (epsZ : ZMod 4) := by
  obtain ⟨c, hc⟩ := example3_q8_sum_eq_eight_mul
    chi m rho hchar Q hQcard qeq t epsilon hfourValue htwoValue
  have hsumC :
      (dZ : ℂ) + (eZ : ℂ) + 6 * (epsZ : ℂ) =
        ((8 * c : ℕ) : ℂ) := by
    rw [← hdchi, ← hechi, ← heps]
    exact hc
  have hsumZ : dZ + eZ + 6 * epsZ = 8 * (c : ℤ) := by
    exact_mod_cast hsumC
  rcases h8 with ⟨u, hu⟩
  apply example3_stage_k_mod_four dZ eZ epsZ (2 * u) (c : ℤ)
  · omega
  · exact hsumZ
  · exact ⟨u, hf.symm.trans hu⟩
private lemma example3_final_arithmetic_core
    (d1 d2 d3 w1 w2 w3 e1 e2 e3 : ℤ)
    (he1 : e1 = 1 ∨ e1 = -1)
    (he2 : e2 = 1 ∨ e2 = -1)
    (he3 : e3 = 1 ∨ e3 = -1)
    (hdeg : 1 + e1 * d1 + e2 * d2 + e3 * d3 = 0)
    (hsq : e1 * w1 ^ 2 * d2 * d3 +
      e2 * w2 ^ 2 * d1 * d3 + e3 * w3 ^ 2 * d1 * d2 = 0)
    (hw1 : ((w1 : ZMod 4) ^ 2) = 0)
    (hw2 : ((w2 : ZMod 4) ^ 2) = 1)
    (hw3 : ((w3 : ZMod 4) ^ 2) = 1)
    (hd1 : (d1 : ZMod 4) = (e1 : ZMod 4)) : False := by
  have he2sq : ((e2 : ZMod 4) ^ 2) = 1 := by
    rcases he2 with rfl | rfl <;> norm_num
  have he3sq : ((e3 : ZMod 4) ^ 2) = 1 := by
    rcases he3 with rfl | rfl <;> norm_num
  have hdegZ := congrArg (fun z : ℤ => (z : ZMod 4)) hdeg
  have hsqZ := congrArg (fun z : ℤ => (z : ZMod 4)) hsq
  norm_num at hdegZ hsqZ
  rw [hw1, hw2, hw3] at hsqZ
  ring_nf at hsqZ
  have hprod :
      (d1 : ZMod 4) * (1 + (e1 : ZMod 4) * d1) = 0 := by
    linear_combination
      (d1 : ZMod 4) * hdegZ -
      ((e2 : ZMod 4) * e3) * hsqZ +
      ((e2 : ZMod 4) * d1 * d2) * he3sq +
      ((e3 : ZMod 4) * d1 * d3) * he2sq
  rw [hd1] at hprod
  rcases he1 with rfl | rfl <;> norm_num at hprod
  all_goals exact (by decide : (2 : ZMod 4) ≠ 0) hprod

private lemma example3_even_sq_zmod_four {z : ℤ} (hz : Even z) :
    ((z : ZMod 4) ^ 2) = 0 := by
  rcases hz with ⟨a, rfl⟩
  push_cast
  calc
    ((a : ZMod 4) + a) ^ 2 = 4 * (a : ZMod 4) ^ 2 := by ring
    _ = 0 := by rw [show (4 : ZMod 4) = 0 by decide]; simp

private lemma example3_odd_sq_zmod_four {z : ℤ} (hz : Odd z) :
    ((z : ZMod 4) ^ 2) = 1 := by
  rcases hz with ⟨a, rfl⟩
  push_cast
  calc
    (2 * (a : ZMod 4) + 1) ^ 2 =
        4 * (a : ZMod 4) ^ 2 + 4 * a + 1 := by ring
    _ = 1 := by rw [show (4 : ZMod 4) = 0 by decide]; simp

private lemma example3_eight_dvd_natCast_mul_of_four_dvd_of_even
    {g : ℕ} {w : ℤ} (hg : 4 ∣ g) (hw : Even w) :
    8 ∣ (g : ℤ) * w := by
  rcases hg with ⟨a, rfl⟩
  rcases hw with ⟨b, rfl⟩
  refine ⟨(a : ℤ) * b, ?_⟩
  push_cast
  ring

private lemma example3_signed_sum_three_parity_patterns
    (e0 e1 e2 w0 w1 w2 : ℤ)
    (he0 : e0 = 1 ∨ e0 = -1)
    (he1 : e1 = 1 ∨ e1 = -1)
    (he2 : e2 = 1 ∨ e2 = -1)
    (hsum : e0 * w0 + e1 * w1 + e2 * w2 = 0)
    (hnotall : ¬(Even w0 ∧ Even w1 ∧ Even w2)) :
    (Even w0 ∧ Odd w1 ∧ Odd w2) ∨
      (Odd w0 ∧ Even w1 ∧ Odd w2) ∨
      (Odd w0 ∧ Odd w1 ∧ Even w2) := by
  rcases Int.even_or_odd w0 with hw0 | hw0 <;>
    rcases Int.even_or_odd w1 with hw1 | hw1 <;>
      rcases Int.even_or_odd w2 with hw2 | hw2
  · exact (hnotall ⟨hw0, hw1, hw2⟩).elim
  · exfalso
    rcases he0 with rfl | rfl <;>
      rcases he1 with rfl | rfl <;>
        rcases he2 with rfl | rfl <;>
          rcases hw0 with ⟨a, rfl⟩ <;>
            rcases hw1 with ⟨b, rfl⟩ <;>
              rcases hw2 with ⟨c, rfl⟩ <;> omega
  · exfalso
    rcases he0 with rfl | rfl <;>
      rcases he1 with rfl | rfl <;>
        rcases he2 with rfl | rfl <;>
          rcases hw0 with ⟨a, rfl⟩ <;>
            rcases hw1 with ⟨b, rfl⟩ <;>
              rcases hw2 with ⟨c, rfl⟩ <;> omega
  · exact Or.inl ⟨hw0, hw1, hw2⟩
  · exfalso
    rcases he0 with rfl | rfl <;>
      rcases he1 with rfl | rfl <;>
        rcases he2 with rfl | rfl <;>
          rcases hw0 with ⟨a, rfl⟩ <;>
            rcases hw1 with ⟨b, rfl⟩ <;>
              rcases hw2 with ⟨c, rfl⟩ <;> omega
  · exact Or.inr (Or.inl ⟨hw0, hw1, hw2⟩)
  · exact Or.inr (Or.inr ⟨hw0, hw1, hw2⟩)
  · exfalso
    rcases he0 with rfl | rfl <;>
      rcases he1 with rfl | rfl <;>
        rcases he2 with rfl | rfl <;>
          rcases hw0 with ⟨a, rfl⟩ <;>
            rcases hw1 with ⟨b, rfl⟩ <;>
              rcases hw2 with ⟨c, rfl⟩ <;> omega

private lemma example3_stage_l_gcd_normalize
    (f e : Fin 3 → ℤ)
    (hpos : ∀ i, 0 < f i)
    (hfour : ∀ i, 4 ∣ f i)
    (he : ∀ i, e i = 1 ∨ e i = -1)
    (hsum : e 0 * f 0 + e 1 * f 1 + e 2 * f 2 = 0) :
    ∃ (sigma : Equiv.Perm (Fin 3)) (g : ℕ) (w : Fin 3 → ℤ),
      0 < g ∧
      (sigma = Equiv.refl _ ∨
        sigma = Equiv.swap 0 1 ∨ sigma = Equiv.swap 0 2) ∧
      (∀ i, f (sigma i) = (g : ℤ) * w i) ∧
      ((w 0 : ZMod 4) ^ 2 = 0) ∧
      ((w 1 : ZMod 4) ^ 2 = 1) ∧
      ((w 2 : ZMod 4) ^ 2 = 1) ∧
      8 ∣ f (sigma 0) := by
  let n : Fin 3 → ℕ := fun i => (f i).toNat
  have hn : ∀ i, (n i : ℤ) = f i := by
    intro i
    exact Int.toNat_of_nonneg (hpos i).le
  have hnpos : ∀ i, 0 < n i := by
    intro i
    have hi := hpos i
    rw [← hn i] at hi
    exact_mod_cast hi
  have hfourN : ∀ i, 4 ∣ n i := by
    intro i
    have hi := hfour i
    rw [← hn i] at hi
    exact_mod_cast hi
  let g := Nat.gcd (Nat.gcd (n 0) (n 1)) (n 2)
  have hgdvd : ∀ i, g ∣ n i := by
    intro i
    fin_cases i
    · exact (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_left _ _)
    · exact (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_right _ _)
    · exact Nat.gcd_dvd_right _ _
  have hgpos : 0 < g :=
    Nat.pos_of_dvd_of_pos (hgdvd 0) (hnpos 0)
  have hfourg : 4 ∣ g := by
    exact Nat.dvd_gcd
      (Nat.dvd_gcd (hfourN 0) (hfourN 1)) (hfourN 2)
  let w : Fin 3 → ℤ := fun i => (n i / g : ℕ)
  have hscale : ∀ i, f i = (g : ℤ) * w i := by
    intro i
    rw [← hn i]
    change (n i : ℤ) = (g : ℤ) * (n i / g : ℕ)
    exact_mod_cast (Nat.mul_div_cancel' (hgdvd i)).symm
  have hnotall : ¬(Even (w 0) ∧ Even (w 1) ∧ Even (w 2)) := by
    rintro ⟨hw0, hw1, hw2⟩
    have htwo : ∀ i, 2 ∣ n i / g := by
      intro i
      fin_cases i
      · have hz : (2 : ℤ) ∣ ((n 0 / g : ℕ) : ℤ) := by
          simpa [w] using (even_iff_two_dvd.mp hw0)
        exact_mod_cast hz
      · have hz : (2 : ℤ) ∣ ((n 1 / g : ℕ) : ℤ) := by
          simpa [w] using (even_iff_two_dvd.mp hw1)
        exact_mod_cast hz
      · have hz : (2 : ℤ) ∣ ((n 2 / g : ℕ) : ℤ) := by
          simpa [w] using (even_iff_two_dvd.mp hw2)
        exact_mod_cast hz
    have htwog : ∀ i, 2 * g ∣ n i := by
      intro i
      rcases htwo i with ⟨a, ha⟩
      refine ⟨a, ?_⟩
      rw [← Nat.mul_div_cancel' (hgdvd i)]
      rw [ha]
      ring
    have hbad : 2 * g ∣ g := by
      exact Nat.dvd_gcd
        (Nat.dvd_gcd (htwog 0) (htwog 1)) (htwog 2)
    have := Nat.le_of_dvd hgpos hbad
    omega
  have hsumw : e 0 * w 0 + e 1 * w 1 + e 2 * w 2 = 0 := by
    have hfac :
        (g : ℤ) * (e 0 * w 0 + e 1 * w 1 + e 2 * w 2) = 0 := by
      calc
        (g : ℤ) * (e 0 * w 0 + e 1 * w 1 + e 2 * w 2) =
            e 0 * f 0 + e 1 * f 1 + e 2 * f 2 := by
              rw [hscale 0, hscale 1, hscale 2]
              ring
        _ = 0 := hsum
    exact (mul_eq_zero.mp hfac).resolve_left (by exact_mod_cast hgpos.ne')
  rcases example3_signed_sum_three_parity_patterns
      (e 0) (e 1) (e 2) (w 0) (w 1) (w 2)
      (he 0) (he 1) (he 2) hsumw hnotall with
    hEOO | hOEO | hOOE
  · refine ⟨Equiv.refl _, g, w, hgpos, Or.inl rfl, ?_,
      example3_even_sq_zmod_four hEOO.1,
      example3_odd_sq_zmod_four hEOO.2.1, example3_odd_sq_zmod_four hEOO.2.2, ?_⟩
    · simpa using hscale
    · change 8 ∣ f 0
      rw [hscale 0]
      exact example3_eight_dvd_natCast_mul_of_four_dvd_of_even hfourg hEOO.1
  · let sigma : Equiv.Perm (Fin 3) := Equiv.swap 0 1
    let w' : Fin 3 → ℤ := fun i => w (sigma i)
    refine ⟨sigma, g, w', hgpos, Or.inr (Or.inl rfl),
      ?_, ?_, ?_, ?_, ?_⟩
    · intro i
      exact hscale (sigma i)
    · change ((w 1 : ℤ) : ZMod 4) ^ 2 = 0
      exact example3_even_sq_zmod_four hOEO.2.1
    · change ((w 0 : ℤ) : ZMod 4) ^ 2 = 1
      exact example3_odd_sq_zmod_four hOEO.1
    · change ((w 2 : ℤ) : ZMod 4) ^ 2 = 1
      exact example3_odd_sq_zmod_four hOEO.2.2
    · change 8 ∣ f 1
      rw [hscale 1]
      exact example3_eight_dvd_natCast_mul_of_four_dvd_of_even hfourg hOEO.2.1
  · let sigma : Equiv.Perm (Fin 3) := Equiv.swap 0 2
    let w' : Fin 3 → ℤ := fun i => w (sigma i)
    refine ⟨sigma, g, w', hgpos, Or.inr (Or.inr rfl),
      ?_, ?_, ?_, ?_, ?_⟩
    · intro i
      exact hscale (sigma i)
    · change ((w 2 : ℤ) : ZMod 4) ^ 2 = 0
      exact example3_even_sq_zmod_four hOOE.2.2
    · change ((w 1 : ℤ) : ZMod 4) ^ 2 = 1
      exact example3_odd_sq_zmod_four hOOE.2.1
    · change ((w 0 : ℤ) : ZMod 4) ^ 2 = 1
      exact example3_odd_sq_zmod_four hOOE.1
    · change 8 ∣ f 2
      rw [hscale 2]
      exact example3_eight_dvd_natCast_mul_of_four_dvd_of_even hfourg hOOE.2.2


private lemma example3_stage_l_final
    (d f e : Fin 3 → ℤ)
    (he : ∀ i, e i = 1 ∨ e i = -1)
    (hpos : ∀ i, 0 < f i)
    (hfour : ∀ i, 4 ∣ f i)
    (hmod : ∀ i, 8 ∣ f i → (d i : ZMod 4) = (e i : ZMod 4))
    (hdeg : 1 + e 0 * d 0 + e 1 * d 1 + e 2 * d 2 = 0)
    (hsum : e 0 * f 0 + e 1 * f 1 + e 2 * f 2 = 0)
    (hsq : e 0 * f 0 ^ 2 * d 1 * d 2 +
      e 1 * f 1 ^ 2 * d 0 * d 2 +
      e 2 * f 2 ^ 2 * d 0 * d 1 = 0) : False := by
  obtain ⟨sigma, g, w, hg, hsigma, hscale, hw0, hw1, hw2, hdivEight⟩ :=
    example3_stage_l_gcd_normalize f e hpos hfour he hsum
  have hdegreePermuted :
      1 + e (sigma 0) * d (sigma 0) +
        e (sigma 1) * d (sigma 1) +
        e (sigma 2) * d (sigma 2) = 0 := by
    rcases hsigma with rfl | rfl | rfl
    · norm_num
      exact hdeg
    · rw [Equiv.swap_apply_left, Equiv.swap_apply_right,
        Equiv.swap_apply_of_ne_of_ne
          (by decide : (2 : Fin 3) ≠ 0) (by decide : (2 : Fin 3) ≠ 1)]
      linear_combination hdeg
    · rw [Equiv.swap_apply_left, Equiv.swap_apply_right,
        Equiv.swap_apply_of_ne_of_ne
          (by decide : (1 : Fin 3) ≠ 0) (by decide : (1 : Fin 3) ≠ 2)]
      linear_combination hdeg
  have hgZ : (g : ℤ) ≠ 0 := by exact_mod_cast hg.ne'
  have hsquarePermuted :
      e (sigma 0) * w 0 ^ 2 * d (sigma 1) * d (sigma 2) +
        e (sigma 1) * w 1 ^ 2 * d (sigma 0) * d (sigma 2) +
        e (sigma 2) * w 2 ^ 2 * d (sigma 0) * d (sigma 1) = 0 := by
    rcases hsigma with rfl | rfl | rfl
    · have hs0 := hscale 0
      have hs1 := hscale 1
      have hs2 := hscale 2
      norm_num at hs0 hs1 hs2 ⊢
      have hfac :
          (g : ℤ) ^ 2 *
            (e 0 * w 0 ^ 2 * d 1 * d 2 +
              e 1 * w 1 ^ 2 * d 0 * d 2 +
              e 2 * w 2 ^ 2 * d 0 * d 1) = 0 := by
        calc
          _ = e 0 * f 0 ^ 2 * d 1 * d 2 +
                e 1 * f 1 ^ 2 * d 0 * d 2 +
                e 2 * f 2 ^ 2 * d 0 * d 1 := by
                  rw [hs0, hs1, hs2]
                  ring
          _ = 0 := hsq
      exact (mul_eq_zero.mp hfac).resolve_left (pow_ne_zero 2 hgZ)
    · have hs0 := hscale 0
      have hs1 := hscale 1
      have hs2 := hscale 2
      norm_num at hs0 hs1 hs2 ⊢
      have hs2' : f 2 = (g : ℤ) * w 2 := by
        simpa only [Equiv.swap_apply_of_ne_of_ne
          (by decide : (2 : Fin 3) ≠ 0) (by decide : (2 : Fin 3) ≠ 1)] using hs2
      have hfac :
          (g : ℤ) ^ 2 *
            (e 1 * w 0 ^ 2 * d 0 * d 2 +
              e 0 * w 1 ^ 2 * d 1 * d 2 +
              e 2 * w 2 ^ 2 * d 1 * d 0) = 0 := by
        calc
          _ = e 0 * f 0 ^ 2 * d 1 * d 2 +
                e 1 * f 1 ^ 2 * d 0 * d 2 +
                e 2 * f 2 ^ 2 * d 0 * d 1 := by
                  rw [hs0, hs1, hs2']
                  ring
          _ = 0 := hsq
      exact (mul_eq_zero.mp hfac).resolve_left (pow_ne_zero 2 hgZ)
    · have hs0 := hscale 0
      have hs1 := hscale 1
      have hs2 := hscale 2
      norm_num at hs0 hs1 hs2 ⊢
      have hs1' : f 1 = (g : ℤ) * w 1 := by
        simpa only [Equiv.swap_apply_of_ne_of_ne
          (by decide : (1 : Fin 3) ≠ 0) (by decide : (1 : Fin 3) ≠ 2)] using hs1
      have hfac :
          (g : ℤ) ^ 2 *
            (e 2 * w 0 ^ 2 * d 1 * d 0 +
              e 1 * w 1 ^ 2 * d 2 * d 0 +
              e 0 * w 2 ^ 2 * d 2 * d 1) = 0 := by
        calc
          _ = e 0 * f 0 ^ 2 * d 1 * d 2 +
                e 1 * f 1 ^ 2 * d 0 * d 2 +
                e 2 * f 2 ^ 2 * d 0 * d 1 := by
                  rw [hs0, hs1', hs2]
                  ring
          _ = 0 := hsq
      exact (mul_eq_zero.mp hfac).resolve_left (pow_ne_zero 2 hgZ)
  exact example3_final_arithmetic_core
    (d (sigma 0)) (d (sigma 1)) (d (sigma 2))
    (w 0) (w 1) (w 2)
    (e (sigma 0)) (e (sigma 1)) (e (sigma 2))
    (he (sigma 0)) (he (sigma 1)) (he (sigma 2))
    hdegreePermuted hsquarePermuted hw0 hw1 hw2
    (hmod (sigma 0) hdivEight)


private lemma example3_clear_three_complex_fractions
    (epsilon f d : Fin 3 → ℂ)
    (hd : ∀ i, d i ≠ 0)
    (h : epsilon 0 * f 0 ^ 2 / d 0 +
      epsilon 1 * f 1 ^ 2 / d 1 +
      epsilon 2 * f 2 ^ 2 / d 2 = 0) :
    epsilon 0 * f 0 ^ 2 * d 1 * d 2 +
      epsilon 1 * f 1 ^ 2 * d 0 * d 2 +
      epsilon 2 * f 2 ^ 2 * d 0 * d 1 = 0 := by
  field_simp [hd 0, hd 1, hd 2] at h
  linear_combination h

private lemma example3_cast_three_data
    (epsilon f d : Fin 3 → ℂ)
    (epsilonZ fZ dZ : Fin 3 → ℤ)
    (hepsilon : ∀ i, epsilon i = (epsilonZ i : ℂ))
    (hf : ∀ i, f i = (fZ i : ℂ))
    (hdcast : ∀ i, d i = (dZ i : ℂ))
    (hd : ∀ i, d i ≠ 0)
    (hsumd : 1 + epsilon 0 * d 0 + epsilon 1 * d 1 +
      epsilon 2 * d 2 = 0)
    (hsumf : epsilon 0 * f 0 + epsilon 1 * f 1 +
      epsilon 2 * f 2 = 0)
    (hsq : epsilon 0 * f 0 ^ 2 / d 0 +
      epsilon 1 * f 1 ^ 2 / d 1 +
      epsilon 2 * f 2 ^ 2 / d 2 = 0) :
    (1 + epsilonZ 0 * dZ 0 + epsilonZ 1 * dZ 1 +
        epsilonZ 2 * dZ 2 = 0) ∧
      (epsilonZ 0 * fZ 0 + epsilonZ 1 * fZ 1 +
        epsilonZ 2 * fZ 2 = 0) ∧
      (epsilonZ 0 * fZ 0 ^ 2 * dZ 1 * dZ 2 +
        epsilonZ 1 * fZ 1 ^ 2 * dZ 0 * dZ 2 +
        epsilonZ 2 * fZ 2 ^ 2 * dZ 0 * dZ 1 = 0) := by
  have hsq' := example3_clear_three_complex_fractions epsilon f d hd hsq
  rw [hepsilon 0, hepsilon 1, hepsilon 2,
    hdcast 0, hdcast 1, hdcast 2] at hsumd
  rw [hepsilon 0, hepsilon 1, hepsilon 2,
    hf 0, hf 1, hf 2] at hsumf
  rw [hepsilon 0, hepsilon 1, hepsilon 2,
    hf 0, hf 1, hf 2, hdcast 0, hdcast 1, hdcast 2] at hsq'
  constructor
  · exact_mod_cast hsumd
  constructor
  · exact_mod_cast hsumf
  · exact_mod_cast hsq'

private lemma example3_inducedCF_restrict_eq_two_mul_of_fixed
    {H : Type*} [Group H] [Finite H]
    (CH : Subgroup H) [CH.Normal]
    (theta : Section1.ClassFunction CH)
    (hquot : Nat.card (H ⧸ CH) = 2)
    (hfix : ∀ x : H, Section1.conjugateOnNormal CH theta x = theta) :
    Section1.subgroupRestriction CH (Section1.inducedCF CH theta) =
      fun c => 2 * theta c := by
  classical
  let : Fintype H := Fintype.ofFinite H
  have hCHnormal : CH.Normal := inferInstance
  funext c
  change Section1.inducedCF CH theta c = 2 * theta c
  unfold Section1.inducedCF Section1.inducedClassFunction
  have hsum :
      (∑ x : H, if hx : x * (c : H) * x⁻¹ ∈ CH then
        theta ⟨x * (c : H) * x⁻¹, hx⟩ else 0) =
        ∑ _x : H, theta c := by
    apply Finset.sum_congr rfl
    intro x _hx
    have hxmem : x * (c : H) * x⁻¹ ∈ CH :=
      hCHnormal.conj_mem (c : H) c.property x
    rw [dif_pos hxmem]
    simpa [Section1.conjugateOnNormal] using congrFun (hfix x) c
  rw [hsum]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hcard : Nat.card H = 2 * Nat.card CH := by
    calc
      Nat.card H = Nat.card (H ⧸ CH) * Nat.card CH :=
        Subgroup.card_eq_card_quotient_mul_card_subgroup CH
      _ = 2 * Nat.card CH := by rw [hquot]
  have hne : (Nat.card CH : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := CH)).ne'
  rw [← Nat.card_eq_fintype_card, hcard, Nat.cast_mul]
  field_simp [hne]
  ring

private lemma example3_inducedCF_eq_four_or_zero_of_ti_constant_four
    {G : Type*} [Group G] [Finite G]
    (H : Subgroup G) (eta : Section1.ClassFunction H)
    (K : Set G) (hTI : IsTISubsetRelative H K)
    (hKfour : ∀ k : G, k ∈ K → 4 ∣ orderOf k)
    (hetaVirtual : Theory.Character.IsVirtualCharacter eta)
    (hetaSupport : ∀ h : H, (h : G) ∉ K → eta h = 0)
    (hetaK : ∀ (k : G) (hk : k ∈ K),
      eta ⟨k, hTI.1 hk⟩ = 4) :
    ∀ g : G,
      ((∃ x : G, x * g * x⁻¹ ∈ K) ∧
        Section1.inducedCF H eta g = 4) ∨
      ((¬ ∃ x : G, x * g * x⁻¹ ∈ K) ∧
        Section1.inducedCF H eta g = 0) := by
  classical
  intro g
  by_cases hconj : ∃ x : G, x * g * x⁻¹ ∈ K
  · left
    refine ⟨hconj, ?_⟩
    obtain ⟨x, hxK⟩ := hconj
    have hxne : x * g * x⁻¹ ≠ 1 := by
      intro hxone
      have hfour := hKfour (x * g * x⁻¹) hxK
      rw [hxone, orderOf_one] at hfour
      norm_num at hfour
    have happ := (suzuki_ch6_proposition_2_9 H K hTI eta
      hetaVirtual hetaSupport).1 (x * g * x⁻¹) hxK hxne
    calc
      Section1.inducedCF H eta g =
          Section1.inducedCF H eta (x * g * x⁻¹) :=
        (Section1.inducedCF_isClassFunction H eta x g).symm
      _ = eta ⟨x * g * x⁻¹, hTI.1 hxK⟩ := happ
      _ = 4 := hetaK (x * g * x⁻¹) hxK
  · right
    refine ⟨hconj, ?_⟩
    unfold Section1.inducedCF Section1.inducedClassFunction
    apply mul_eq_zero_of_right
    apply Finset.sum_eq_zero
    intro x _hx
    split
    next hxH =>
      have hxnotK : x * g * x⁻¹ ∉ K := by
        intro hxK
        exact hconj ⟨x, hxK⟩
      rw [hetaSupport ⟨x * g * x⁻¹, hxH⟩ hxnotK]
    next _hxH => rfl
private lemma example3_induced_integer_of_ti_constant_four
    {G : Type*} [Group G] [Finite G]
    (H : Subgroup G) (eta : Section1.ClassFunction H)
    (K : Set G) (hTI : IsTISubsetRelative H K)
    (hKfour : ∀ k : G, k ∈ K → 4 ∣ orderOf k)
    (hetaVirtual : Theory.Character.IsVirtualCharacter eta)
    (hetaSupport : ∀ h : H, (h : G) ∉ K → eta h = 0)
    (hetaK : ∀ (k : G) (hk : k ∈ K),
      eta ⟨k, hTI.1 hk⟩ = 4) :
    ∀ g : G, ∃ n : ℤ, Section1.inducedCF H eta g = (n : ℂ) := by
  intro g
  rcases example3_inducedCF_eq_four_or_zero_of_ti_constant_four
      H eta K hTI hKfour hetaVirtual hetaSupport hetaK g with
    ⟨_hconj, hfour⟩ | ⟨_hconj, hzero⟩
  · exact ⟨4, by simpa using hfour⟩
  · exact ⟨0, by simpa using hzero⟩
private lemma example3_zmod_four_addOrder_eq_four_eq_one_or_neg_one
    (a : ZMod 4) (ha : addOrderOf a = 4) :
    a = 1 ∨ a = -1 := by
  let n := a.val
  have hformula : addOrderOf a = 4 / Nat.gcd 4 a.val := by
    calc
      addOrderOf a = addOrderOf (n : ZMod 4) := by
        rw [show (n : ZMod 4) = a from ZMod.natCast_zmod_val a]
      _ = 4 / Nat.gcd 4 n := ZMod.addOrderOf_coe n (n := 4) (by norm_num)
      _ = 4 / Nat.gcd 4 a.val := rfl
  rw [ha] at hformula
  have hval : a.val = 1 ∨ a.val = 3 := by
    have hlt := a.val_lt
    interval_cases hv : a.val <;> norm_num [hv] at hformula <;> omega
  rcases hval with h | h
  · left
    apply ZMod.val_injective
    rw [h]
    norm_num [ZMod.val_one_eq_one_mod]
  · right
    apply ZMod.val_injective
    rw [h]
    exact (ZMod.val_neg_one 3).symm

private lemma example3_cyclic_card_four_order_four_eq_or_eq_inv
    {Y : Type*} [Group Y] [Finite Y] [IsCyclic Y]
    (hcard : Nat.card Y = 4) {x y : Y}
    (hx : orderOf x = 4) (hy : orderOf y = 4) :
    y = x ∨ y = x⁻¹ := by
  let : NeZero (Nat.card Y) := ⟨Nat.card_pos.ne'⟩
  let e : Multiplicative (ZMod 4) ≃* Y := by
    rw [← hcard]
    exact zmodCyclicMulEquiv (inferInstance : IsCyclic Y)
  have ex0 : orderOf (e.symm x) = 4 := by rw [e.symm.orderOf_eq, hx]
  have ey0 : orderOf (e.symm y) = 4 := by rw [e.symm.orderOf_eq, hy]
  have ex : addOrderOf (e.symm x).toAdd = 4 := ex0
  have ey : addOrderOf (e.symm y).toAdd = 4 := ey0
  rcases example3_zmod_four_addOrder_eq_four_eq_one_or_neg_one (e.symm x).toAdd ex with hx1 | hx1 <;>
    rcases example3_zmod_four_addOrder_eq_four_eq_one_or_neg_one (e.symm y).toAdd ey with hy1 | hy1
  · left
    apply e.symm.injective
    simpa using congrArg Multiplicative.ofAdd (hy1.trans hx1.symm)
  · right
    apply e.symm.injective
    have hadd : (e.symm y).toAdd = -(e.symm x).toAdd := by simp [hy1, hx1]
    simpa using congrArg Multiplicative.ofAdd hadd
  · right
    apply e.symm.injective
    have hadd : (e.symm y).toAdd = -(e.symm x).toAdd := by simp [hy1, hx1]
    simpa using congrArg Multiplicative.ofAdd hadd
  · left
    apply e.symm.injective
    simpa using congrArg Multiplicative.ofAdd (hy1.trans hx1.symm)

private lemma example3_card_eight_center_two_conj_eq_inv
    {P : Type*} [Group P] [Finite P]
    (hPcard : Nat.card P = 8)
    (hcenter : Nat.card (Subgroup.center P) = 2)
    (b : P) (hb : orderOf b = 4) :
    ∃ q : P, q * b * q⁻¹ = b⁻¹ := by
  let B : Subgroup P := Subgroup.zpowers b
  have hBcard : Nat.card B = 4 := by
    rw [Nat.card_zpowers, hb]
  have hBindex : B.index = 2 := by
    have hmul := B.card_mul_index
    rw [hBcard, hPcard] at hmul
    omega
  have hBnormal : B.Normal := Subgroup.normal_of_index_eq_two hBindex
  have hb_not_center : b ∉ Subgroup.center P := by
    intro hbcenter
    have hle :=
      Subgroup.card_le_of_le (Subgroup.zpowers_le.mpr hbcenter)
    have hle2 : Nat.card (Subgroup.zpowers b) ≤ 2 :=
      hle.trans_eq hcenter
    rw [Nat.card_zpowers, hb] at hle2
    omega
  have hb_not_comm_all : ¬ ∀ q : P, q * b = b * q := by
    intro h
    exact hb_not_center (Subgroup.mem_center_iff.mpr h)
  push Not at hb_not_comm_all
  obtain ⟨q, hnoncomm⟩ := hb_not_comm_all
  have hyB : q * b * q⁻¹ ∈ B :=
    hBnormal.conj_mem b (Subgroup.mem_zpowers b) q
  let y : B := ⟨q * b * q⁻¹, hyB⟩
  let bB : B := ⟨b, Subgroup.mem_zpowers b⟩
  have hbB : orderOf bB = 4 := by
    simpa [bB, Subgroup.orderOf_mk] using hb
  have hy : orderOf y = 4 := by
    rw [Subgroup.orderOf_mk]
    change orderOf ((MulAut.conj q) b) = 4
    rw [(MulAut.conj q).orderOf_eq, hb]
  rcases example3_cyclic_card_four_order_four_eq_or_eq_inv
      hBcard hbB hy with hyb | hyb
  · exfalso
    apply hnoncomm
    have hybP := congrArg (fun z : B => (z : P)) hyb
    exact mul_inv_eq_iff_eq_mul.mp (by simpa [y, bB] using hybP)
  · exact ⟨q, congrArg (fun z : B => (z : P)) hyb⟩


private lemma example3_order_eq_one_two_or_four_of_card_eight_center_two
    {P : Type*} [Group P] [Finite P]
    (hPcard : Nat.card P = 8)
    (hcenter : Nat.card (Subgroup.center P) = 2)
    (a : P) :
    orderOf a = 1 ∨ orderOf a = 2 ∨ orderOf a = 4 := by
  have hdvd : orderOf a ∣ 8 := by
    rw [← hPcard]
    exact orderOf_dvd_natCard a
  have hpos : 0 < orderOf a := orderOf_pos a
  have hne8 : orderOf a ≠ 8 := by
    intro ha8
    have hcyclic : IsCyclic P :=
      isCyclic_iff_exists_orderOf_eq_natCard.mpr
        ⟨a, by rw [ha8, hPcard]⟩
    let : IsCyclic P := hcyclic
    let : CommGroup P := IsCyclic.commGroup
    have hctop := CommGroup.center_eq_top (G := P)
    rw [hctop, Subgroup.card_top, hPcard] at hcenter
    norm_num at hcenter
  have hdvdPow : orderOf a ∣ 2 ^ 3 := by
    norm_num
    exact hdvd
  obtain ⟨k, hk, hord⟩ :=
    (Nat.dvd_prime_pow Nat.prime_two).mp hdvdPow
  interval_cases k
  · left
    simpa using hord
  · right
    left
    simpa using hord
  · right
    right
    simpa using hord
  · exfalso
    apply hne8
    simpa using hord

private lemma example3_card_four_eq_zpowers_of_order_four
    {Y : Type*} [Group Y] [Finite Y]
    (V : Subgroup Y) (hVcard : Nat.card V = 4)
    {x : Y} (hxV : x ∈ V) (hx : orderOf x = 4) :
    V = Subgroup.zpowers x := by
  symm
  exact Subgroup.eq_of_le_of_card_ge
    (Subgroup.zpowers_le.mpr hxV) (by
      rw [Nat.card_zpowers, hx, hVcard])


private def example3_q8Axis : Fin 3 → Subgroup (QuaternionGroup 2)
  | 0 => Subgroup.zpowers (QuaternionGroup.a 1 : (QuaternionGroup 2))
  | 1 => Subgroup.zpowers (QuaternionGroup.xa 0 : (QuaternionGroup 2))
  | 2 => Subgroup.zpowers (QuaternionGroup.xa 1 : (QuaternionGroup 2))

private lemma example3_q8Axis_card (i : Fin 3) :
    Nat.card (example3_q8Axis i) = 4 := by
  fin_cases i
  · change Nat.card (Subgroup.zpowers
      (QuaternionGroup.a 1 : QuaternionGroup 2)) = 4
    rw [Nat.card_zpowers, QuaternionGroup.orderOf_a_one]
  · change Nat.card (Subgroup.zpowers
      (QuaternionGroup.xa 0 : QuaternionGroup 2)) = 4
    rw [Nat.card_zpowers, QuaternionGroup.orderOf_xa]
  · change Nat.card (Subgroup.zpowers
      (QuaternionGroup.xa 1 : QuaternionGroup 2)) = 4
    rw [Nat.card_zpowers, QuaternionGroup.orderOf_xa]


private lemma example3_q8_xa_two_eq_inv :
    (QuaternionGroup.xa 2 : (QuaternionGroup 2)) =
      (QuaternionGroup.xa 0 : (QuaternionGroup 2))⁻¹ := by
  change QuaternionGroup.xa 2 = QuaternionGroup.xa (2 + 0)
  congr 1

private lemma example3_q8_xa_three_eq_inv :
    (QuaternionGroup.xa 3 : (QuaternionGroup 2)) =
      (QuaternionGroup.xa 1 : (QuaternionGroup 2))⁻¹ := by
  change QuaternionGroup.xa 3 = QuaternionGroup.xa (2 + 1)
  congr 1

private lemma example3_q8_a_mem_axis_zero (i : ZMod 4) :
    (QuaternionGroup.a i : (QuaternionGroup 2)) ∈ example3_q8Axis 0 := by
  have hi :
      (QuaternionGroup.a i : (QuaternionGroup 2)) =
        (QuaternionGroup.a 1 : (QuaternionGroup 2)) ^ i.val := by
    rw [QuaternionGroup.a_one_pow]
    congr 1
    exact (ZMod.natCast_zmod_val i).symm
  rw [hi]
  exact (example3_q8Axis 0).pow_mem (Subgroup.mem_zpowers _) i.val

private lemma example3_q8_xa_not_mem_axis_zero (i : ZMod 4) :
    (QuaternionGroup.xa i : (QuaternionGroup 2)) ∉ example3_q8Axis 0 := by
  intro hi
  rw [example3_q8Axis, mem_zpowers_iff_mem_range_orderOf] at hi
  rcases Finset.mem_image.mp hi with ⟨k, hk, heq⟩
  have hklt : k < 4 := by
    simpa using Finset.mem_range.mp hk
  interval_cases k <;>
    simp [QuaternionGroup.a_one_pow, QuaternionGroup.one_def,
      -QuaternionGroup.a_zero] at heq

private lemma example3_q8_mem_axis_zero_or_one_or_two (x : (QuaternionGroup 2)) :
    x ∈ example3_q8Axis 0 ∨
      x ∈ example3_q8Axis 1 ∨
      x ∈ example3_q8Axis 2 := by
  cases x with
  | a i =>
      exact Or.inl (example3_q8_a_mem_axis_zero i)
  | xa i =>
      have hi_lt : i.val < 4 := i.val_lt
      interval_cases hi : i.val
      · have hieq : i = 0 := by
          apply ZMod.val_injective
          rw [hi]
          decide
        subst i
        exact Or.inr (Or.inl (Subgroup.mem_zpowers _))
      · have hieq : i = 1 := by
          apply ZMod.val_injective
          rw [hi]
          decide
        subst i
        exact Or.inr (Or.inr (Subgroup.mem_zpowers _))
      · have hieq : i = 2 := by
          apply ZMod.val_injective
          rw [hi]
          decide
        subst i
        right
        left
        rw [example3_q8_xa_two_eq_inv]
        exact (example3_q8Axis 1).inv_mem (Subgroup.mem_zpowers _)
      · have hieq : i = 3 := by
          apply ZMod.val_injective
          rw [hi]
          decide
        subst i
        right
        right
        rw [example3_q8_xa_three_eq_inv]
        exact (example3_q8Axis 2).inv_mem (Subgroup.mem_zpowers _)

private lemma example3_q8_order_four_of_not_mem_axis_zero
    {x : (QuaternionGroup 2)} (hx : x ∉ example3_q8Axis 0) :
    orderOf x = 4 := by
  cases x with
  | a i => exact False.elim (hx (example3_q8_a_mem_axis_zero i))
  | xa i => exact QuaternionGroup.orderOf_xa i

private lemma example3_q8Axis_surjective
    (V : Subgroup (QuaternionGroup 2)) (hVcard : Nat.card V = 4) :
    ∃ i : Fin 3, example3_q8Axis i = V := by
  by_cases hV0 : V ≤ example3_q8Axis 0
  · refine ⟨0, ?_⟩
    symm
    exact Subgroup.eq_of_le_of_card_ge hV0 (by
      rw [hVcard, example3_q8Axis_card])
  · obtain ⟨v, hvV, hv0⟩ := SetLike.not_le_iff_exists.mp hV0
    have hvorder : orderOf v = 4 :=
      example3_q8_order_four_of_not_mem_axis_zero hv0
    have hVz : V = Subgroup.zpowers v :=
      example3_card_four_eq_zpowers_of_order_four V hVcard hvV hvorder
    rcases example3_q8_mem_axis_zero_or_one_or_two v with hv0' | hv1 | hv2
    · exact False.elim (hv0 hv0')
    · refine ⟨1, ?_⟩
      rw [hVz]
      symm
      exact Subgroup.eq_of_le_of_card_ge
        (Subgroup.zpowers_le.mpr hv1) (by
          rw [Nat.card_zpowers, hvorder, example3_q8Axis_card])
    · refine ⟨2, ?_⟩
      rw [hVz]
      symm
      exact Subgroup.eq_of_le_of_card_ge
        (Subgroup.zpowers_le.mpr hv2) (by
          rw [Nat.card_zpowers, hvorder, example3_q8Axis_card])

private lemma example3_q8Axis_zero_ne_one :
    example3_q8Axis 0 ≠ example3_q8Axis 1 := by
  intro h
  exact example3_q8_xa_not_mem_axis_zero 0
    (h.symm ▸ Subgroup.mem_zpowers (QuaternionGroup.xa 0 : (QuaternionGroup 2)))

private lemma example3_q8Axis_zero_ne_two :
    example3_q8Axis 0 ≠ example3_q8Axis 2 := by
  intro h
  exact example3_q8_xa_not_mem_axis_zero 1
    (h.symm ▸ Subgroup.mem_zpowers (QuaternionGroup.xa 1 : (QuaternionGroup 2)))

private lemma example3_q8_axis_product_relation :
    ((QuaternionGroup.xa 0 : (QuaternionGroup 2)) * QuaternionGroup.xa 1)⁻¹ =
      QuaternionGroup.a 1 := by
  change QuaternionGroup.a (-((2 : ZMod 4) + 1 - 0)) = QuaternionGroup.a 1
  congr 1

private lemma example3_q8Axis_one_ne_two :
    example3_q8Axis 1 ≠ example3_q8Axis 2 := by
  intro h
  have hxa0 : (QuaternionGroup.xa 0 : (QuaternionGroup 2)) ∈ example3_q8Axis 1 :=
    Subgroup.mem_zpowers _
  have hxa1 : (QuaternionGroup.xa 1 : (QuaternionGroup 2)) ∈ example3_q8Axis 1 := by
    rw [h]
    exact Subgroup.mem_zpowers _
  have ha1 : (QuaternionGroup.a 1 : (QuaternionGroup 2)) ∈ example3_q8Axis 1 := by
    rw [← example3_q8_axis_product_relation]
    exact (example3_q8Axis 1).inv_mem
      ((example3_q8Axis 1).mul_mem hxa0 hxa1)
  have h01 : example3_q8Axis 0 = example3_q8Axis 1 :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr ha1) (by
      rw [example3_q8Axis_card, example3_q8Axis_card])
  exact example3_q8Axis_zero_ne_one h01

private lemma example3_q8Axis_injective :
    Function.Injective example3_q8Axis := by
  intro i j hij
  fin_cases i <;> fin_cases j
  all_goals simp only at hij ⊢
  · exact False.elim (example3_q8Axis_zero_ne_one hij)
  · exact False.elim (example3_q8Axis_zero_ne_two hij)
  · exact False.elim (example3_q8Axis_zero_ne_one hij.symm)
  · exact False.elim (example3_q8Axis_one_ne_two hij)
  · exact False.elim (example3_q8Axis_zero_ne_two hij.symm)
  · exact False.elim (example3_q8Axis_one_ne_two hij.symm)

private lemma example3_quaternion_eight_order_four_axes_card :
    Nat.card {V : Subgroup (QuaternionGroup 2) // Nat.card V = 4} = 3 := by
  let f : Fin 3 →
      {V : Subgroup (QuaternionGroup 2) // Nat.card V = 4} :=
    fun i => ⟨example3_q8Axis i, example3_q8Axis_card i⟩
  have hf_inj : Function.Injective f := by
    intro i j hij
    exact example3_q8Axis_injective (congrArg Subtype.val hij)
  have hf_surj : Function.Surjective f := by
    intro V
    obtain ⟨i, hi⟩ := example3_q8Axis_surjective V V.property
    refine ⟨i, ?_⟩
    exact Subtype.ext hi
  simpa using Nat.card_congr (Equiv.ofBijective f ⟨hf_inj, hf_surj⟩).symm

private lemma example3_generalized_quaternion_eight_equiv_q8
    {P : Type*} [Group P] [Finite P] {n : ℕ} (hn : 3 ≤ n)
    (hP : Nonempty (P ≃* QuaternionGroup (2 ^ (n - 2))))
    (hPcard : Nat.card P = 8) :
    Nonempty (P ≃* QuaternionGroup 2) := by
  let e : P ≃* QuaternionGroup (2 ^ (n - 2)) := Classical.choice hP
  have hcard : Nat.card P = 2 ^ n := by
    calc
      Nat.card P = Nat.card (QuaternionGroup (2 ^ (n - 2))) :=
        Nat.card_congr e.toEquiv
      _ = 4 * 2 ^ (n - 2) := by
        rw [Nat.card_eq_fintype_card, QuaternionGroup.card]
      _ = 2 ^ n := by
        rw [show n = 2 + (n - 2) by omega, pow_add]
        norm_num
  have hn3 : n = 3 := by
    apply Nat.pow_right_injective (by norm_num : 2 ≤ 2)
    change 2 ^ n = 2 ^ 3
    rw [← hcard, hPcard]
  subst n
  exact ⟨by simpa using e⟩
private lemma example3_generalized_quaternion_eight_order_four_axes_card
    {P : Type*} [Group P] [Finite P] {n : ℕ} (hn : 3 ≤ n)
    (hP : Nonempty (P ≃* QuaternionGroup (2 ^ (n - 2))))
    (hPcard : Nat.card P = 8) :
    Nat.card {V : Subgroup P // Nat.card V = 4} = 3 := by
  let e : P ≃* QuaternionGroup (2 ^ (n - 2)) := Classical.choice hP
  have hcard : Nat.card P = 2 ^ n := by
    calc
      Nat.card P = Nat.card (QuaternionGroup (2 ^ (n - 2))) :=
        Nat.card_congr e.toEquiv
      _ = 4 * 2 ^ (n - 2) := by
        rw [Nat.card_eq_fintype_card, QuaternionGroup.card]
      _ = 2 ^ n := by
        rw [show n = 2 + (n - 2) by omega, pow_add]
        norm_num
  have hn3 : n = 3 := by
    apply Nat.pow_right_injective (by norm_num : 2 ≤ 2)
    change 2 ^ n = 2 ^ 3
    rw [← hcard, hPcard]
  subst n
  let e8 : P ≃* QuaternionGroup 2 := by simpa using e
  let eSub : Subgroup P ≃ Subgroup (QuaternionGroup 2) :=
    e8.mapSubgroup.toEquiv
  let eAxis :
      {V : Subgroup P // Nat.card V = 4} ≃
        {V : Subgroup (QuaternionGroup 2) // Nat.card V = 4} :=
    eSub.subtypeEquiv (by
      intro V
      change Nat.card V = 4 ↔
        Nat.card (V.map e8.toMonoidHom) = 4
      rw [Subgroup.card_map_of_injective e8.injective])
  calc
    Nat.card {V : Subgroup P // Nat.card V = 4} =
        Nat.card {V : Subgroup (QuaternionGroup 2) // Nat.card V = 4} :=
      Nat.card_congr eAxis
    _ = 3 := example3_quaternion_eight_order_four_axes_card

private def example3_subgroup_map_perm {Q : Type*} [Group Q]
    (e : MulAut Q) : Equiv.Perm (Subgroup Q) where
  toFun V := V.map e.toMonoidHom
  invFun V := V.map e.symm.toMonoidHom
  left_inv V := by
    change (V.map e.toMonoidHom).map e.symm.toMonoidHom = V
    rw [Subgroup.map_map]
    ext x
    simp
  right_inv V := by
    change (V.map e.symm.toMonoidHom).map e.toMonoidHom = V
    rw [Subgroup.map_map]
    ext x
    simp

private def example3_subgroup_card_perm {Q : Type*} [Group Q] [Finite Q]
    (e : MulAut Q) : Equiv.Perm {V : Subgroup Q // Nat.card V = 4} :=
  (example3_subgroup_map_perm e).subtypePerm (by
    intro V
    change Nat.card (V.map e.toMonoidHom) = 4 ↔ Nat.card V = 4
    rw [Subgroup.card_map_of_injective e.injective])

set_option backward.isDefEq.respectTransparency false in
private def example3_subgroup_card_perm_hom {Q : Type*} [Group Q] [Finite Q] :
    MulAut Q →* Equiv.Perm {V : Subgroup Q // Nat.card V = 4} where
  toFun := example3_subgroup_card_perm
  map_one' := by
    ext V x
    simp [example3_subgroup_card_perm, example3_subgroup_map_perm, Subgroup.mem_map]
  map_mul' e f := by
    ext V x
    simp [example3_subgroup_card_perm, example3_subgroup_map_perm, Subgroup.mem_map]

private lemma example3_perm_order_eq_one_or_three_of_odd_pow_eq_one
    {A : Type*} [Finite A] (hcard : Nat.card A = 3)
    (p : Equiv.Perm A) (m : ℕ) (hm : Odd m) (hpow : p ^ m = 1) :
    orderOf p = 1 ∨ orderOf p = 3 := by
  have hdvdm : orderOf p ∣ m := orderOf_dvd_iff_pow_eq_one.mpr hpow
  have hnotTwo : ¬ 2 ∣ orderOf p := by
    intro htwo
    have htwoM : 2 ∣ m := dvd_trans htwo hdvdm
    rcases hm with ⟨k, rfl⟩
    omega
  have hdvdCard := orderOf_dvd_natCard p
  have hcardPerm : Nat.card (Equiv.Perm A) = 6 := by
    rw [Nat.card_perm, hcard]
    norm_num
  rw [hcardPerm] at hdvdCard
  have hpos : 0 < orderOf p := orderOf_pos p
  have hle : orderOf p ≤ 6 := Nat.le_of_dvd (by norm_num) hdvdCard
  interval_cases h : orderOf p <;> simp_all

private lemma example3_perm_three_orbit_of_moved
    {A : Type*} [Finite A] (hcard : Nat.card A = 3)
    (p : Equiv.Perm A) (hp : orderOf p = 3)
    (a : A) (ha : p a ≠ a) :
    ∀ b, b = a ∨ b = p a ∨ b = (p ^ 2) a := by
  classical
  let : Fintype A := Fintype.ofFinite A
  have hp3 : p ^ 3 = 1 := by
    rw [← hp]
    exact pow_orderOf_eq_one p
  have hp2a_ne_a : (p ^ 2) a ≠ a := by
    intro h
    have h' : (p ^ 3) a = p a := by
      calc
        (p ^ 3) a = p ((p ^ 2) a) := by simp [pow_succ]
        _ = p a := congrArg p h
    rw [hp3] at h'
    exact ha h'.symm
  have hp2a_ne_pa : (p ^ 2) a ≠ p a := by
    intro h
    apply ha
    apply p.injective
    simpa [pow_two] using h
  let s : Finset A := {a, p a, (p ^ 2) a}
  have hsCard : s.card = Fintype.card A := by
    rw [show Fintype.card A = 3 by simpa using hcard]
    simp [s, ha.symm, hp2a_ne_a.symm, hp2a_ne_pa.symm]
  have hs := Finset.eq_univ_of_card s hsCard
  intro b
  have hb : b ∈ s := by rw [hs]; simp
  simpa [s, eq_comm] using hb

private lemma example3_card_four_axis_fixed_of_card_eight
    {Q : Type*} [Group Q] [Finite Q] (hQcard : Nat.card Q = 8)
    (q : Q) (V : {V : Subgroup Q // Nat.card V = 4}) :
    example3_subgroup_card_perm (MulAut.conj q) V = V := by
  have hmul := V.val.card_mul_index
  have hindex : V.val.index = 2 := by
    rw [V.property, hQcard] at hmul
    omega
  let : V.val.Normal := Subgroup.normal_of_index_eq_two hindex
  apply Subtype.ext
  change (MulAut.conj q • V.val : Subgroup Q) = V.val
  exact Subgroup.Normal.conj_smul_eq_self q V.val


private lemma example3_normalizer_axis_perm_order
    {G : Type*} [Group G] [Finite G]
    (Q : Sylow 2 G) (hQcard : Nat.card Q = 8)
    (hAxisCard : Nat.card {V : Subgroup Q // Nat.card V = 4} = 3)
    (n : Subgroup.normalizer ((Q : Subgroup G) : Set G)) :
    orderOf ((example3_subgroup_card_perm_hom.comp
      (Q : Subgroup G).normalizerMonoidHom) n) = 1 ∨
    orderOf ((example3_subgroup_card_perm_hom.comp
      (Q : Subgroup G).normalizerMonoidHom) n) = 3 := by
  let N := Subgroup.normalizer ((Q : Subgroup G) : Set G)
  let Q0 : Subgroup N := (Q : Subgroup G).subgroupOf N
  let P : Sylow 2 N := Q.subtype Q.le_normalizer
  let rho := example3_subgroup_card_perm_hom.comp
    (Q : Subgroup G).normalizerMonoidHom
  let m := Q0.index
  have : Q0.Normal := by
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer
      Q.le_normalizer).2 le_rfl
  have hmNot : ¬ 2 ∣ m := by
    simpa [m, Q0, P] using P.not_dvd_index
  have hmOdd : Odd m := Nat.not_even_iff_odd.mp (by
    rw [even_iff_two_dvd]
    exact hmNot)
  have hnPow : n ^ m ∈ Q0 := Q0.pow_index_mem n
  let q : Q := ⟨((n ^ m : N) : G), hnPow⟩
  have hnormalizerAction :
      (Q : Subgroup G).normalizerMonoidHom (n ^ m) =
        MulAut.conj q := by
    ext y
    rfl
  have hpow : (rho n) ^ m = 1 := by
    rw [← rho.map_pow]
    apply Equiv.ext
    intro V
    change example3_subgroup_card_perm
      ((Q : Subgroup G).normalizerMonoidHom (n ^ m)) V = V
    rw [hnormalizerAction]
    exact example3_card_four_axis_fixed_of_card_eight hQcard q V
  exact example3_perm_order_eq_one_or_three_of_odd_pow_eq_one
    hAxisCard (rho n) m hmOdd hpow

private lemma example3_normalizer_axis_fixed_or_transitive
    {G : Type*} [Group G] [Finite G]
    (Q : Sylow 2 G) (hQcard : Nat.card Q = 8)
    (hAxisCard : Nat.card {V : Subgroup Q // Nat.card V = 4} = 3) :
    let rho := example3_subgroup_card_perm_hom.comp
      (Q : Subgroup G).normalizerMonoidHom
    (∀ n V, rho n V = V) ∨
      (∀ A B, ∃ n, rho n A = B) := by
  classical
  let rho := example3_subgroup_card_perm_hom.comp
    (Q : Subgroup G).normalizerMonoidHom
  by_cases hfixed : ∀ n V, rho n V = V
  · exact Or.inl hfixed
  · right
    push Not at hfixed
    obtain ⟨n, V, hnV⟩ := hfixed
    have hnOrder : orderOf (rho n) = 3 := by
      rcases example3_normalizer_axis_perm_order
          Q hQcard hAxisCard n with hone | hthree
      · have hnOne : rho n = 1 := orderOf_eq_one_iff.mp hone
        exact False.elim (hnV (by rw [hnOne]; rfl))
      · exact hthree
    have hpowers (B : {V : Subgroup Q // Nat.card V = 4}) :
        ∃ k : ℕ, ((rho n) ^ k) V = B := by
      rcases example3_perm_three_orbit_of_moved hAxisCard (rho n)
          hnOrder V hnV B with h | h | h
      · exact ⟨0, by simpa using h.symm⟩
      · exact ⟨1, by simpa using h.symm⟩
      · exact ⟨2, h.symm⟩
    intro A B
    obtain ⟨a, ha⟩ := hpowers A
    obtain ⟨b, hb⟩ := hpowers B
    refine ⟨n ^ b * (n ^ a)⁻¹, ?_⟩
    rw [rho.map_mul, rho.map_inv, rho.map_pow, rho.map_pow]
    change ((rho n) ^ b) ((((rho n) ^ a)⁻¹) A) = B
    rw [← ha, Equiv.Perm.coe_inv, Equiv.symm_apply_apply, hb]

private lemma example3_axis_transitive_order_four_conj
    {G : Type*} [Group G] [Finite G]
    (Q : Sylow 2 G)
    (htrans :
      let rho := example3_subgroup_card_perm_hom.comp
        (Q : Subgroup G).normalizerMonoidHom
      ∀ A B, ∃ n, rho n A = B)
    (hinverter : ∀ b : Q, orderOf (b : G) = 4 →
      ∃ q : Q, (q : G) * (b : G) * (q : G)⁻¹ = (b : G)⁻¹)
    (a b : Q) (ha : orderOf (a : G) = 4)
    (hb : orderOf (b : G) = 4) :
    ∃ g : G, g * (a : G) * g⁻¹ = (b : G) := by
  let rho := example3_subgroup_card_perm_hom.comp
    (Q : Subgroup G).normalizerMonoidHom
  let aQ : (Q : Subgroup G) := ⟨(a : G), a.property⟩
  let bQ : (Q : Subgroup G) := ⟨(b : G), b.property⟩
  have haQ : orderOf aQ = 4 := by
    simpa [aQ, Subgroup.orderOf_mk] using ha
  have hbQ : orderOf bQ = 4 := by
    simpa [bQ, Subgroup.orderOf_mk] using hb
  let A : {V : Subgroup Q // Nat.card V = 4} :=
    ⟨Subgroup.zpowers aQ, by rw [Nat.card_zpowers, haQ]⟩
  let B : {V : Subgroup Q // Nat.card V = 4} :=
    ⟨Subgroup.zpowers bQ, by rw [Nat.card_zpowers, hbQ]⟩
  obtain ⟨n, hn⟩ := htrans A B
  let e := (Q : Subgroup G).normalizerMonoidHom n
  have hmem : e aQ ∈ (rho n A).val := by
    change e aQ ∈ A.val.map e.toMonoidHom
    exact Subgroup.mem_map_of_mem e.toMonoidHom
      (Subgroup.mem_zpowers aQ)
  rw [hn] at hmem
  let cB : B.val := ⟨e aQ, hmem⟩
  let bB : B.val := ⟨bQ, Subgroup.mem_zpowers bQ⟩
  have hcB : orderOf cB = 4 := by
    rw [Subgroup.orderOf_mk]
    rw [e.orderOf_eq, haQ]
  have hbB : orderOf bB = 4 := by
    simpa [bB, Subgroup.orderOf_mk] using hbQ
  rcases example3_cyclic_card_four_order_four_eq_or_eq_inv
      B.property hbB hcB with hc | hc
  · refine ⟨(n : G), ?_⟩
    have hcG :=
      congrArg (fun z : B.val => (((z : (Q : Subgroup G)) : G))) hc
    exact (Subgroup.normalizerMonoidHom_apply_apply_coe
      (Q : Subgroup G) n aQ).symm.trans hcG
  · obtain ⟨q, hq⟩ := hinverter b hb
    refine ⟨(q : G) * (n : G), ?_⟩
    have hcG :=
      congrArg (fun z : B.val => (((z : (Q : Subgroup G)) : G))) hc
    have hconjInv :
        (n : G) * (a : G) * (n : G)⁻¹ = (b : G)⁻¹ := by
      exact (Subgroup.normalizerMonoidHom_apply_apply_coe
        (Q : Subgroup G) n aQ).symm.trans hcG
    calc
      ((q : G) * (n : G)) * (a : G) *
          ((q : G) * (n : G))⁻¹ =
        (q : G) * ((n : G) * (a : G) * (n : G)⁻¹) *
          (q : G)⁻¹ := by group
      _ = (q : G) * (b : G)⁻¹ * (q : G)⁻¹ := by rw [hconjInv]
      _ = ((q : G) * (b : G) * (q : G)⁻¹)⁻¹ := by group
      _ = ((b : G)⁻¹)⁻¹ := by rw [hq]
      _ = (b : G) := inv_inv _

private lemma example3_all_order_four_conj_of_sylow
    {G : Type*} [Group G] [Finite G]
    (Q : Sylow 2 G)
    (hQconj : ∀ (a b : Q),
      orderOf (a : G) = 4 → orderOf (b : G) = 4 →
        ∃ g : G, g * (a : G) * g⁻¹ = (b : G))
    {x y : G} (hx : orderOf x = 4) (hy : orderOf y = 4) :
    ∃ g : G, g * x * g⁻¹ = y := by
  have hxP : IsPGroup 2 (Subgroup.zpowers x) := by
    apply IsPGroup.of_card (p := 2)
      (G := Subgroup.zpowers x) (n := 2)
    rw [Nat.card_zpowers, hx]
    norm_num
  have hyP : IsPGroup 2 (Subgroup.zpowers y) := by
    apply IsPGroup.of_card (p := 2)
      (G := Subgroup.zpowers y) (n := 2)
    rw [Nat.card_zpowers, hy]
    norm_num
  obtain ⟨S, hxS⟩ :=
    IsPGroup.exists_le_sylow (G := G) (p := 2) hxP
  obtain ⟨T, hyT⟩ :=
    IsPGroup.exists_le_sylow (G := G) (p := 2) hyP
  obtain ⟨gx, hgx⟩ := MulAction.exists_smul_eq G S Q
  obtain ⟨gy, hgy⟩ := MulAction.exists_smul_eq G T Q
  have hxQmem : gx * x * gx⁻¹ ∈ (Q : Subgroup G) := by
    rw [← hgx]
    change gx * x * gx⁻¹ ∈
      (S : Subgroup G).map (MulAut.conj gx).toMonoidHom
    exact Subgroup.mem_map_of_mem (MulAut.conj gx).toMonoidHom
      (hxS (Subgroup.mem_zpowers x))
  have hyQmem : gy * y * gy⁻¹ ∈ (Q : Subgroup G) := by
    rw [← hgy]
    change gy * y * gy⁻¹ ∈
      (T : Subgroup G).map (MulAut.conj gy).toMonoidHom
    exact Subgroup.mem_map_of_mem (MulAut.conj gy).toMonoidHom
      (hyT (Subgroup.mem_zpowers y))
  let xQ : Q := ⟨gx * x * gx⁻¹, hxQmem⟩
  let yQ : Q := ⟨gy * y * gy⁻¹, hyQmem⟩
  have hxQorder : orderOf (xQ : G) = 4 := by
    change orderOf (MulAut.conj gx x) = 4
    rw [(MulAut.conj gx).orderOf_eq, hx]
  have hyQorder : orderOf (yQ : G) = 4 := by
    change orderOf (MulAut.conj gy y) = 4
    rw [(MulAut.conj gy).orderOf_eq, hy]
  obtain ⟨h, hh⟩ := hQconj xQ yQ hxQorder hyQorder
  refine ⟨gy⁻¹ * h * gx, ?_⟩
  calc
    (gy⁻¹ * h * gx) * x * (gy⁻¹ * h * gx)⁻¹ =
        gy⁻¹ * (h * (gx * x * gx⁻¹) * h⁻¹) * gy := by group
    _ = gy⁻¹ * (gy * y * gy⁻¹) * gy := by rw [hh]
    _ = y := by group

private lemma example3_all_involutions_conj_of_sylow
    {G : Type*} [Group G] [Finite G]
    (Q : Sylow 2 G)
    (hunique : ∀ a b : Q, IsInvolution a → IsInvolution b → a = b)
    {x y : G} (hx : orderOf x = 2) (hy : orderOf y = 2) :
    ∃ g : G, g * x * g⁻¹ = y := by
  have hxI : IsInvolution x := by
    have h := (orderOf_eq_prime_iff.mp hx)
    exact ⟨h.2, h.1⟩
  have hyI : IsInvolution y := by
    have h := (orderOf_eq_prime_iff.mp hy)
    exact ⟨h.2, h.1⟩
  have hxP : IsPGroup 2 (Subgroup.zpowers x) :=
    example3_isPGroup_zpowers_of_involution hxI
  have hyP : IsPGroup 2 (Subgroup.zpowers y) :=
    example3_isPGroup_zpowers_of_involution hyI
  obtain ⟨S, hxS⟩ :=
    IsPGroup.exists_le_sylow (G := G) (p := 2) hxP
  obtain ⟨T, hyT⟩ :=
    IsPGroup.exists_le_sylow (G := G) (p := 2) hyP
  obtain ⟨gx, hgx⟩ := MulAction.exists_smul_eq G S Q
  obtain ⟨gy, hgy⟩ := MulAction.exists_smul_eq G T Q
  have hxQmem : gx * x * gx⁻¹ ∈ (Q : Subgroup G) := by
    rw [← hgx]
    change gx * x * gx⁻¹ ∈
      (S : Subgroup G).map (MulAut.conj gx).toMonoidHom
    exact Subgroup.mem_map_of_mem (MulAut.conj gx).toMonoidHom
      (hxS (Subgroup.mem_zpowers x))
  have hyQmem : gy * y * gy⁻¹ ∈ (Q : Subgroup G) := by
    rw [← hgy]
    change gy * y * gy⁻¹ ∈
      (T : Subgroup G).map (MulAut.conj gy).toMonoidHom
    exact Subgroup.mem_map_of_mem (MulAut.conj gy).toMonoidHom
      (hyT (Subgroup.mem_zpowers y))
  let xQ : Q := ⟨gx * x * gx⁻¹, hxQmem⟩
  let yQ : Q := ⟨gy * y * gy⁻¹, hyQmem⟩
  have hxQI : IsInvolution xQ := by
    have hAmbient : IsInvolution (gx * x * gx⁻¹) := by
      simpa [rightConjugateElem] using
        isInvolution_rightConjugateElem (g := gx⁻¹) hxI
    exact ⟨fun h => hAmbient.1 (congrArg Subtype.val h),
      Subtype.ext (by simpa [xQ] using hAmbient.2)⟩
  have hyQI : IsInvolution yQ := by
    have hAmbient : IsInvolution (gy * y * gy⁻¹) := by
      simpa [rightConjugateElem] using
        isInvolution_rightConjugateElem (g := gy⁻¹) hyI
    exact ⟨fun h => hAmbient.1 (congrArg Subtype.val h),
      Subtype.ext (by simpa [yQ] using hAmbient.2)⟩
  have hxyQ : xQ = yQ := hunique xQ yQ hxQI hyQI
  have hxy :
      gx * x * gx⁻¹ = gy * y * gy⁻¹ :=
    congrArg Subtype.val hxyQ
  refine ⟨gy⁻¹ * gx, ?_⟩
  calc
    (gy⁻¹ * gx) * x * (gy⁻¹ * gx)⁻¹ =
        gy⁻¹ * (gx * x * gx⁻¹) * gy := by group
    _ = gy⁻¹ * (gy * y * gy⁻¹) * gy := by rw [hxy]
    _ = y := by group
private lemma example3_axis_fixed_normalizer_preserves_zpowers
    {G : Type*} [Group G] [Finite G]
    (Q : Sylow 2 G)
    (hfixed :
      let rho := example3_subgroup_card_perm_hom.comp
        (Q : Subgroup G).normalizerMonoidHom
      ∀ n V, rho n V = V)
    (n : Subgroup.normalizer ((Q : Subgroup G) : Set G))
    (x : Q) (hx : orderOf (x : G) = 4) :
    (n : G) * (x : G) * (n : G)⁻¹ ∈
      Subgroup.zpowers (x : G) := by
  let rho := example3_subgroup_card_perm_hom.comp
    (Q : Subgroup G).normalizerMonoidHom
  let xQ : (Q : Subgroup G) := ⟨(x : G), x.property⟩
  have hxQ : orderOf xQ = 4 := by
    simpa [xQ, Subgroup.orderOf_mk] using hx
  let V : {V : Subgroup Q // Nat.card V = 4} :=
    ⟨Subgroup.zpowers xQ, by rw [Nat.card_zpowers, hxQ]⟩
  let e := (Q : Subgroup G).normalizerMonoidHom n
  have hmem : e xQ ∈ (rho n V).val := by
    change e xQ ∈ V.val.map e.toMonoidHom
    exact Subgroup.mem_map_of_mem e.toMonoidHom
      (Subgroup.mem_zpowers xQ)
  rw [hfixed n V] at hmem
  rcases hmem with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  have hkG := congrArg (fun z : (Q : Subgroup G) => (z : G)) hk
  exact hkG.trans
    (Subgroup.normalizerMonoidHom_apply_apply_coe (Q : Subgroup G) n xQ)

private lemma example3_index_two_of_card_four_le_card_eight
    {G : Type*} [Group G] [Finite G]
    {V Q : Subgroup G} (hVQ : V ≤ Q)
    (hVcard : Nat.card V = 4) (hQcard : Nat.card Q = 8) :
    (V.subgroupOf Q).index = 2 := by
  have hsubcard : Nat.card (V.subgroupOf Q) = 4 := by
    calc
      Nat.card (V.subgroupOf Q) = Nat.card V :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVQ).toEquiv
      _ = 4 := hVcard
  have hmul := (V.subgroupOf Q).card_mul_index
  rw [hsubcard, hQcard] at hmul
  omega

private lemma example3_order_four_has_inverter_in_sylow
    {G : Type*} [Group G] [Finite G]
    (Q : Sylow 2 G) (hQcard : Nat.card Q = 8)
    (hcenter : Nat.card (Subgroup.center (Q : Subgroup G)) = 2)
    (b : Q) (hb : orderOf (b : G) = 4) :
    ∃ q : Q, (q : G) * (b : G) * (q : G)⁻¹ = (b : G)⁻¹ := by
  have hbQ : orderOf b = 4 := by
    simpa only [Subgroup.orderOf_coe] using hb
  obtain ⟨q, hq⟩ :=
    example3_card_eight_center_two_conj_eq_inv
      hQcard hcenter b hbQ
  exact ⟨q, congrArg (fun z : Q => (z : G)) hq⟩

private lemma example3_fusion_up_to_inverse
    {G : Type*} [Group G] [Finite G]
    (Q : Sylow 2 G) (hQcard : Nat.card Q = 8)
    (a b : Q) (ha : orderOf (a : G) = 4)
    (hb : orderOf (b : G) = 4)
    (hconj : ∃ g : G, g * (a : G) * g⁻¹ = (b : G)) :
    ∃ n : Subgroup.normalizer ((Q : Subgroup G) : Set G),
      ((n : G) * (a : G) * (n : G)⁻¹ = (b : G) ∨
       (n : G) * (a : G) * (n : G)⁻¹ = (b : G)⁻¹) := by
  classical
  obtain ⟨g, hgab⟩ := hconj
  let A : Subgroup G := Subgroup.zpowers (a : G)
  let B : Subgroup G := Subgroup.zpowers (b : G)
  have hAcard : Nat.card A = 4 := by rw [Nat.card_zpowers, ha]
  have hBcard : Nat.card B = 4 := by rw [Nat.card_zpowers, hb]
  have hA_le_Q : A ≤ (Q : Subgroup G) :=
    Subgroup.zpowers_le.mpr a.property
  have hB_le_Q : B ≤ (Q : Subgroup G) :=
    Subgroup.zpowers_le.mpr b.property
  have hAindex : (A.subgroupOf (Q : Subgroup G)).index = 2 :=
    example3_index_two_of_card_four_le_card_eight
      hA_le_Q hAcard hQcard
  have hBindex : (B.subgroupOf (Q : Subgroup G)).index = 2 :=
    example3_index_two_of_card_four_le_card_eight
      hB_le_Q hBcard hQcard
  have hAnormal : (A.subgroupOf (Q : Subgroup G)).Normal :=
    Subgroup.normal_of_index_eq_two hAindex
  have hBnormal : (B.subgroupOf (Q : Subgroup G)).Normal :=
    Subgroup.normal_of_index_eq_two hBindex
  have hQ_le_normA : (Q : Subgroup G) ≤ Subgroup.normalizer A :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hA_le_Q).mp hAnormal
  have hQ_le_normB : (Q : Subgroup G) ≤ Subgroup.normalizer B :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hB_le_Q).mp hBnormal
  have hgA : A.map (MulAut.conj g).toMonoidHom = B := by
    rw [MonoidHom.map_zpowers]
    change Subgroup.zpowers (g * (a : G) * g⁻¹) = B
    rw [hgab]
  have hgQ_le_normB :
      (Q : Subgroup G).map (MulAut.conj g).toMonoidHom ≤
        Subgroup.normalizer (B : Set G) := by
    rw [← hgA]
    rw [← Subgroup.map_equiv_normalizer_eq A (MulAut.conj g)]
    exact Subgroup.map_mono hQ_le_normA
  let NB : Subgroup G := Subgroup.normalizer (B : Set G)
  let QN : Sylow 2 NB := Q.subtype hQ_le_normB
  let R : Sylow 2 G := g • Q
  let RN : Sylow 2 NB := R.subtype hgQ_le_normB
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq NB QN RN
  have hcQ : (c : G) • Q = g • Q := by
    apply Sylow.subtype_injective (N := NB)
    calc
      ((c : G) • Q).subtype (Sylow.smul_le hQ_le_normB c) =
          c • QN := (Sylow.smul_subtype hQ_le_normB c).symm
      _ = RN := hc
      _ = (g • Q).subtype hgQ_le_normB := rfl
  let n0 : G := (c : G)⁻¹ * g
  have hn0 : n0 ∈ Subgroup.normalizer ((Q : Subgroup G) : Set G) := by
    apply Sylow.smul_eq_iff_mem_normalizer.mp
    calc
      n0 • Q = (c : G)⁻¹ • (g • Q) := by simp [n0, mul_smul]
      _ = (c : G)⁻¹ • ((c : G) • Q) := by rw [hcQ]
      _ = Q := inv_smul_smul (c : G) Q
  let n : Subgroup.normalizer ((Q : Subgroup G) : Set G) :=
    ⟨n0, hn0⟩
  have hnconj :
      (n : G) * (a : G) * (n : G)⁻¹ =
        (c : G)⁻¹ * (b : G) * (c : G) := by
    change n0 * (a : G) * n0⁻¹ = _
    calc
      n0 * (a : G) * n0⁻¹ =
          (c : G)⁻¹ * (g * (a : G) * g⁻¹) * (c : G) := by
        simp [n0, mul_assoc]
      _ = (c : G)⁻¹ * (b : G) * (c : G) := by rw [hgab]
  have hyB : (c : G)⁻¹ * (b : G) * (c : G) ∈ B :=
    ((Subgroup.mem_normalizer_iff''.mp c.property) (b : G)).mp
      (Subgroup.mem_zpowers (b : G))
  let y : B := ⟨(c : G)⁻¹ * (b : G) * (c : G), hyB⟩
  let bB : B := ⟨(b : G), Subgroup.mem_zpowers (b : G)⟩
  have hbB : orderOf bB = 4 := by
    simpa [bB, Subgroup.orderOf_mk] using hb
  have hy : orderOf y = 4 := by
    rw [Subgroup.orderOf_mk]
    have heq :
        (c : G)⁻¹ * (b : G) * (c : G) =
          (MulAut.conj ((c : G)⁻¹)) (b : G) := by simp
    rw [heq, (MulAut.conj ((c : G)⁻¹)).orderOf_eq, hb]
  rcases example3_cyclic_card_four_order_four_eq_or_eq_inv
      hBcard hbB hy with hyb | hyb
  · refine ⟨n, Or.inl ?_⟩
    rw [hnconj]
    exact congrArg (fun z : B => (z : G)) hyb
  · refine ⟨n, Or.inr ?_⟩
    rw [hnconj]
    exact congrArg (fun z : B => (z : G)) hyb

private lemma example3_controlled_fusion_order_four
    {G : Type*} [Group G] [Finite G]
    (Q : Sylow 2 G) (hQcard : Nat.card Q = 8)
    (hcenter : Nat.card (Subgroup.center (Q : Subgroup G)) = 2)
    (hfixed : ∀ n : Subgroup.normalizer ((Q : Subgroup G) : Set G),
      ∀ x : Q, orderOf (x : G) = 4 →
        (n : G) * (x : G) * (n : G)⁻¹ ∈
          Subgroup.zpowers (x : G))
    (a b : Q) (ha : orderOf (a : G) = 4)
    (hb : orderOf (b : G) = 4)
    (hconj : ∃ g : G, g * (a : G) * g⁻¹ = (b : G)) :
    ∃ q : Q, (q : G) * (a : G) * (q : G)⁻¹ = (b : G) := by
  obtain ⟨n, hn⟩ :=
    example3_fusion_up_to_inverse Q hQcard a b ha hb hconj
  have hbA : (b : G) ∈ Subgroup.zpowers (a : G) := by
    rcases hn with hn | hn
    · have hmem := hfixed n a ha
      rw [hn] at hmem
      exact hmem
    · have hmem := hfixed n a ha
      rw [hn] at hmem
      simpa only [inv_inv] using
        (Subgroup.zpowers (a : G)).inv_mem hmem
  let A : Subgroup G := Subgroup.zpowers (a : G)
  have hAcard : Nat.card A = 4 := by rw [Nat.card_zpowers, ha]
  let aA : A := ⟨(a : G), Subgroup.mem_zpowers (a : G)⟩
  let bA : A := ⟨(b : G), hbA⟩
  have haA : orderOf aA = 4 := by
    simpa [aA, Subgroup.orderOf_mk] using ha
  have hbAorder : orderOf bA = 4 := by
    simpa [bA, Subgroup.orderOf_mk] using hb
  rcases example3_cyclic_card_four_order_four_eq_or_eq_inv
      hAcard haA hbAorder with hba | hba
  · refine ⟨1, ?_⟩
    simpa [aA, bA] using
      (congrArg (fun z : A => (z : G)) hba).symm
  · obtain ⟨q, hq⟩ :=
      example3_order_four_has_inverter_in_sylow
        Q hQcard hcenter a ha
    refine ⟨q, ?_⟩
    calc
      (q : G) * (a : G) * (q : G)⁻¹ = (a : G)⁻¹ := hq
      _ = (b : G) := by
        have hbaG := congrArg (fun z : A => (z : G)) hba
        simpa [aA, bA] using hbaG.symm

private lemma example3_simple_no_normal_two_complement_corefree
    {G : Type*} [Group G] [Finite G]
    (hG : IsSimpleGroup G) (Q : Sylow 2 G)
    (hQcard : Nat.card Q = 8) (hcore : pPrimeCore 2 G = ⊥)
    (hcomp : HasNormalPComplement 2 G) : False := by
  have h8dvd : 8 ∣ Nat.card G := by
    rw [← hQcard]
    exact Subgroup.card_subgroup_dvd_card (Q : Subgroup G)
  let : Nontrivial G := Finite.one_lt_card_iff_nontrivial.mp (by
    have h8le : 8 ≤ Nat.card G :=
      Nat.le_of_dvd Nat.card_pos h8dvd
    omega)
  let : IsSimpleGroup G := hG
  have hGp : IsPGroup 2 G :=
    BenderSuzuki.External.hkt_isPGroup_of_hasNormalPComplement_of_pPrimeCore_eq_bot
      hcore hcomp
  have hcenterNontrivial : Nontrivial (Subgroup.center G) :=
    hGp.center_nontrivial
  have hcenterNeBot : Subgroup.center G ≠ ⊥ :=
    (Subgroup.nontrivial_iff_ne_bot (Subgroup.center G)).mp
      hcenterNontrivial
  have hcenterTop : Subgroup.center G = ⊤ :=
    (IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (Subgroup.center G)).resolve_left hcenterNeBot
  let : CommGroup G := Group.commGroupOfCenterEqTop hcenterTop
  have hprime : (Nat.card G).Prime := IsSimpleGroup.prime_card
  rcases (Nat.dvd_prime hprime).mp h8dvd with h8one | h8card
  · norm_num at h8one
  · rw [← h8card] at hprime
    exact (by norm_num : ¬ Nat.Prime 8) hprime

private lemma example3_quotient_card_four_kernel_cosets
    {Y : Type*} [Group Y] [Finite Y]
    (N : Subgroup Y) [N.Normal]
    (hcyclic : IsCyclic (Y ⧸ N))
    (hcard : Nat.card (Y ⧸ N) = 4)
    {x y : Y}
    (hx : orderOf (x : Y ⧸ N) = 4)
    (hy : orderOf (y : Y ⧸ N) = 4) :
    (∃ n : N, y = (n : Y) * x) ∨
      (∃ n : N, y = (n : Y) * x⁻¹) := by
  let : IsCyclic (Y ⧸ N) := hcyclic
  rcases example3_cyclic_card_four_order_four_eq_or_eq_inv hcard hx hy with h | h
  · left
    have hmem : y / x ∈ N := QuotientGroup.eq_iff_div_mem.mp h
    exact ⟨⟨y / x, hmem⟩, (div_mul_cancel y x).symm⟩
  · right
    have hquot : (y : Y ⧸ N) = (x⁻¹ : Y ⧸ N) := by simpa using h
    have hmem : y / x⁻¹ ∈ N := QuotientGroup.eq_iff_div_mem.mp hquot
    exact ⟨⟨y / x⁻¹, hmem⟩, (div_mul_cancel y x⁻¹).symm⟩
private lemma example3_irreducible_integer_valued_of_argumentPow_fixed
    {G : Type*} [Group G] [Finite G]
    (chi : Section1.ClassFunction G)
    (hchi : Section1.IsIrreducibleCharacterOnGroup chi)
    (hfixed : ∀ {a : ℕ}, a.Coprime (Nat.card G) →
      ∀ g : G, chi (g ^ a) = chi g) :
    ∀ g : G, ∃ z : ℤ, chi g = (z : ℂ) := by
  classical
  rcases hchi with ⟨m, rho, _hirr, hchi_rho⟩
  intro g
  have hcard : Nat.card G ≠ 0 := (Nat.card_pos (α := G)).ne'
  have hn : Nat.card G * 1 ≠ 0 := by simpa using hcard
  let : NeZero (Nat.card G * 1) := ⟨hn⟩
  let eta : ℂ :=
    Complex.exp (2 * Real.pi * Complex.I / (Nat.card G * 1))
  have heta : IsPrimitiveRoot eta (Nat.card G * 1) := by
    simpa [eta] using Complex.isPrimitiveRoot_exp (Nat.card G * 1) hn
  have hetaG : IsPrimitiveRoot eta (Nat.card G) := by simpa using heta
  have hmem : rho.character g ∈ Theory.Character.cyclotomicOrder eta :=
    Theory.Character.representation_character_mem_cyclotomicOrder hetaG rho g
  let K := Section1.CyclotomicABField (Nat.card G) 1
  let zeta : K := Section1.cyclotomicABRoot (Nat.card G) 1 hn
  have hzeta : IsPrimitiveRoot zeta (Nat.card G * 1) := by
    dsimp [zeta, Section1.cyclotomicABRoot, K, Section1.CyclotomicABField]
    exact IsCyclotomicExtension.zeta_spec
      (Nat.card G * 1) ℚ (CyclotomicField (Nat.card G * 1) ℚ)
  have hirr : Irreducible (Polynomial.cyclotomic (Nat.card G * 1) ℚ) :=
    Polynomial.cyclotomic.irreducible_rat (NeZero.pos (Nat.card G * 1))
  let etaRoot : primitiveRoots (Nat.card G * 1) ℂ := ⟨eta, by
    rw [mem_primitiveRoots (NeZero.pos (Nat.card G * 1))]
    exact heta⟩
  let iota : K →ₐ[ℚ] ℂ :=
    (hzeta.embeddingsEquivPrimitiveRoots ℂ hirr).symm etaRoot
  have hiota_zeta : iota zeta = eta := by
    change ((hzeta.embeddingsEquivPrimitiveRoots ℂ hirr) iota : ℂ) = eta
    simp [iota, etaRoot]
  rcases Theory.Character.mem_cyclotomicOrder_iff_exists_intPolynomial_eval.mp hmem with
    ⟨P, hP⟩
  let x : K := Polynomial.eval₂ (Int.castRingHom K) zeta P
  have hvalue : rho.character g = iota x := by
    rw [← hP]
    rw [← hiota_zeta]
    dsimp [x]
    exact (Polynomial.ringHom_eval₂_intCastRingHom
      P iota.toRingHom zeta).symm
  have hx_fixed : ∀ v : Gal(K/ℚ), v x = x := by
    intro v
    let u : (ZMod (Nat.card G * 1))ˣ :=
      IsCyclotomicExtension.Rat.galEquivZMod (Nat.card G * 1) K v
    let e : ℕ := (u : ZMod (Nat.card G * 1)).val
    have he : e.Coprime (Nat.card G * 1) := by
      simpa [e] using ZMod.val_coe_unit_coprime u
    have heG : e.Coprime (Nat.card G) := by simpa using he
    have hvzeta : v zeta = zeta ^ e := by
      rw [IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq
        (Nat.card G * 1) K v hzeta.pow_eq_one]
    have hiota_vzeta : iota (v zeta) = eta ^ e := by
      rw [hvzeta, map_pow, hiota_zeta]
    obtain ⟨tau, htau⟩ := Section5.complex_galois_aut_pow_on_roots he
    have htau_char : tau (rho.character g) = rho.character (g ^ e) :=
      Section1.representation_character_apply_galois_eq_argumentPow
        (N := Nat.card G * 1) (e := e) htau rho (by simp) g
    have hpow : rho.character (g ^ e) = rho.character g := by
      calc
        rho.character (g ^ e) = chi (g ^ e) :=
          (congrFun hchi_rho (g ^ e)).symm
        _ = chi g := hfixed heG g
        _ = rho.character g := congrFun hchi_rho g
    have htau_fixed : tau (rho.character g) = rho.character g :=
      htau_char.trans hpow
    have htau_eval :
        tau (Polynomial.eval₂ (Int.castRingHom ℂ) eta P) =
          Polynomial.eval₂ (Int.castRingHom ℂ) (eta ^ e) P := by
      rw [← htau eta heta.pow_eq_one]
      exact Polynomial.ringHom_eval₂_intCastRingHom
        P tau.toRingEquiv.toRingHom eta
    have heval_fixed :
        Polynomial.eval₂ (Int.castRingHom ℂ) (eta ^ e) P =
          Polynomial.eval₂ (Int.castRingHom ℂ) eta P := by
      calc
        _ = tau (Polynomial.eval₂ (Int.castRingHom ℂ) eta P) := htau_eval.symm
        _ = tau (rho.character g) := by rw [hP]
        _ = rho.character g := htau_fixed
        _ = Polynomial.eval₂ (Int.castRingHom ℂ) eta P := hP.symm
    apply iota.injective
    dsimp [x]
    have hvEval :
        v (Polynomial.eval₂ (Int.castRingHom K) zeta P) =
          Polynomial.eval₂ (Int.castRingHom K) (v zeta) P :=
      Polynomial.ringHom_eval₂_intCastRingHom
        P v.toRingEquiv.toRingHom zeta
    calc
      iota (v (Polynomial.eval₂ (Int.castRingHom K) zeta P)) =
          iota (Polynomial.eval₂ (Int.castRingHom K) (v zeta) P) := by
        rw [hvEval]
      _ = Polynomial.eval₂ (Int.castRingHom ℂ) (iota (v zeta)) P :=
        Polynomial.ringHom_eval₂_intCastRingHom P iota.toRingHom (v zeta)
      _ = Polynomial.eval₂ (Int.castRingHom ℂ) (eta ^ e) P := by
        rw [hiota_vzeta]
      _ = Polynomial.eval₂ (Int.castRingHom ℂ) eta P := heval_fixed
      _ = Polynomial.eval₂ (Int.castRingHom ℂ) (iota zeta) P := by
        rw [hiota_zeta]
      _ = iota (Polynomial.eval₂ (Int.castRingHom K) zeta P) :=
        (Polynomial.ringHom_eval₂_intCastRingHom P iota.toRingHom zeta).symm
  have hrat : ∃ q : ℚ, rho.character g = (q : ℂ) :=
    Section1.cyclotomicABField_complex_rat_of_fixed_gal
      iota x (rho.character g) hvalue hx_fixed
  rcases Theory.Character.isaacs_lemma_3_2_core
      (Theory.Character.representation_character_isIntegral rho g) hrat with ⟨z, hz⟩
  exact ⟨z, (congrFun hchi_rho g).trans hz⟩

private theorem example3_int_sum_even_of_fixedPointFree_involution
    {I : Type*} [DecidableEq I]
    (s : Finset I) (zVal : I → ℤ) (c : I → I)
    (hmem : ∀ i, i ∈ s → c i ∈ s)
    (hinv : ∀ i, i ∈ s → c (c i) = i)
    (hneq : ∀ i, i ∈ s → c i ≠ i)
    (hz : ∀ i, i ∈ s → zVal (c i) = zVal i) :
    ∃ z : ℤ, s.sum zVal = 2 * z := by
  classical
  have hsumMod : ((s.sum zVal : ℤ) : ZMod 2) = 0 := by
    have hcast : ((s.sum zVal : ℤ) : ZMod 2) =
        ∑ x ∈ s, ((zVal x : ℤ) : ZMod 2) := by
      simp
    rw [hcast, ← Finset.sum_attach]
    refine Finset.sum_involution
      (s := Finset.univ)
      (f := fun x : {x // x ∈ s} => ((zVal x : ℤ) : ZMod 2))
      (g := fun x _ => ⟨c x, hmem x x.2⟩) ?_ ?_ ?_ ?_
    · intro x _
      change ((zVal (x : I) : ℤ) : ZMod 2) +
          ((zVal (c (x : I)) : ℤ) : ZMod 2) = 0
      rw [hz x x.2]
      exact CharTwo.add_self_eq_zero _
    · intro x _ _ hfix
      exact hneq x x.2 (congrArg Subtype.val hfix)
    · intro x _
      simp
    · intro x _
      ext
      exact hinv x x.2
  have hEven : Even (s.sum zVal : ℤ) :=
    (ZMod.intCast_eq_zero_iff_even).1 hsumMod
  rcases hEven with ⟨z, hz⟩
  exact ⟨z, by omega⟩

private lemma example3_sum_eq_one_add_even_of_inv
    {N : Type*} [Group N] [Fintype N]
    (hodd : Nat.Coprime 2 (Nat.card N))
    (a : N → ℤ) (haInv : ∀ u : N, a u⁻¹ = a u) :
    ∃ z : ℤ, ∑ u : N, a u = a 1 + 2 * z := by
  classical
  let s : Finset N := Finset.univ.erase 1
  have hmem : ∀ u, u ∈ s → u⁻¹ ∈ s := by
    intro u hu
    rw [Finset.mem_erase] at hu ⊢
    exact ⟨by simpa using hu.1, Finset.mem_univ _⟩
  have hinv : ∀ u, u ∈ s → (u⁻¹)⁻¹ = u := by simp
  have hneq : ∀ u, u ∈ s → u⁻¹ ≠ u := by
    intro u hu hfix
    have huSq : u ^ 2 = 1 := by
      have h := congrArg (fun z : N => u * z) hfix
      simpa [pow_two] using h.symm
    have hordDvd : orderOf u ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr huSq
    have hordPos : 0 < orderOf u := orderOf_pos u
    have hordLe : orderOf u ≤ 2 := Nat.le_of_dvd (by norm_num) hordDvd
    have hordCases : orderOf u = 1 ∨ orderOf u = 2 := by omega
    rcases hordCases with hord | hord
    · have huone : u = 1 := orderOf_eq_one_iff.mp hord
      exact (Finset.mem_erase.mp hu).1 huone
    · have htwo : 2 ∣ Nat.card N := by
        rw [← hord]
        exact orderOf_dvd_natCard u
      exact (Nat.prime_two.coprime_iff_not_dvd.mp hodd) htwo
  obtain ⟨z, hz⟩ := example3_int_sum_even_of_fixedPointFree_involution
    s a (fun u => u⁻¹) hmem hinv hneq (fun u _ => haInv u)
  refine ⟨z, ?_⟩
  have hone : (1 : N) ∈ Finset.univ := Finset.mem_univ _
  rw [← Finset.sum_erase_add _ _ hone, show Finset.univ.erase 1 = s from rfl, hz]
  ring

private lemma example3_integer_scalar_product_sum
    {G : Type*} [Group G] [Finite G] [Fintype G]
    (phi psi : Section1.ClassFunction G)
    (b a : G → ℤ)
    (hphi : ∀ g, phi g = (b g : ℂ))
    (hpsi : ∀ g, psi g = (a g : ℂ))
    (c : ℤ)
    (hscalar : Section1.scalarProduct G phi psi = (c : ℂ)) :
    ∑ g : G, b g * a g = Nat.card G * c := by
  classical
  rw [Section1.scalarProduct] at hscalar
  simp_rw [hphi, hpsi] at hscalar
  rw [show @Finset.univ G (Fintype.ofFinite G) =
      @Finset.univ G (inferInstance : Fintype G) by ext; simp] at hscalar
  have hcardne : (Nat.card G : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := G)).ne'
  have hcomplex :
      (∑ g : G, (b g * a g : ℤ) : ℂ) = (Nat.card G * c : ℤ) := by
    field_simp [hcardne] at hscalar
    push_cast
    simpa [mul_comm] using hscalar
  exact_mod_cast hcomplex


private lemma example3_small_two_coset_sum
    {G : Type*} [Group G] [Finite G]
    (H : Subgroup G) (N : Subgroup H) [Fintype H] [Fintype N]
    (K : Set G) (eta : Section1.ClassFunction H) (x : H)
    (hodd : Nat.Coprime 2 (Nat.card N))
    (hxOrder : orderOf (x : G) = 4)
    (hKcosets : ∀ h : H, (h : G) ∈ K ↔
      (∃ u : N, h = x * (u : H)) ∨
      (∃ u : N, h = x⁻¹ * (u : H)))
    (hetaK : ∀ h : H, (h : G) ∈ K → eta h = 4)
    (hetaSupport : ∀ h : H, (h : G) ∉ K → eta h = 0)
    (a : H → ℤ)
    (hpair : ∀ u : N, a (x⁻¹ * (u : H)) = a (x * (u : H)))
    (hHcard : Nat.card H = 8 * Nat.card N)
    (c : ℤ)
    (hscalar : (Nat.card H : ℂ)⁻¹ *
      ∑ h : H, eta h * star (a h : ℂ) = (c : ℂ)) :
    ∑ u : N, a (x * (u : H)) = c * Nat.card N := by
  classical
  let S : Finset H := Finset.univ.filter (fun h => (h : G) ∈ K)
  have hcross : ∀ u v : N, x * (u : H) ≠ x⁻¹ * (v : H) := by
    intro u v huv
    have hx2eq : x ^ 2 = (v : H) * (u : H)⁻¹ := by
      rw [pow_two]
      calc
        x * x = (x * (x * (u : H))) * (u : H)⁻¹ := by group
        _ = (x * (x⁻¹ * (v : H))) * (u : H)⁻¹ := by rw [huv]
        _ = (v : H) * (u : H)⁻¹ := by group
    let z : N := ⟨x ^ 2, by
      rw [hx2eq]
      exact N.mul_mem v.property (N.inv_mem u.property)⟩
    have hxOrderH : orderOf x = 4 := by
      simpa [Subgroup.orderOf_coe] using hxOrder
    have hzOrderH : orderOf (x ^ 2) = 2 := by
      rw [orderOf_pow, hxOrderH]
      norm_num
    have hzOrderN : orderOf z = 2 := by
      simpa [z, Subgroup.orderOf_coe] using hzOrderH
    have htwo : 2 ∣ Nat.card N := by
      rw [← hzOrderN]
      exact orderOf_dvd_natCard z
    exact (Nat.prime_two.coprime_iff_not_dvd.mp hodd) htwo
  let phi : N ⊕ N → {h : H // h ∈ S} := fun z =>
    match z with
    | Sum.inl u => ⟨x * (u : H), by
        simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
        exact (hKcosets _).2 (Or.inl ⟨u, rfl⟩)⟩
    | Sum.inr u => ⟨x⁻¹ * (u : H), by
        simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
        exact (hKcosets _).2 (Or.inr ⟨u, rfl⟩)⟩
  have hphi_inj : Function.Injective phi := by
    intro p q hpq
    cases p with
    | inl u =>
        cases q with
        | inl v =>
            have huv : u = v := by
              apply Subtype.ext
              have hv := congrArg (fun h : {h : H // h ∈ S} => (h : H)) hpq
              simp only [phi] at hv
              exact mul_left_cancel hv
            exact congrArg Sum.inl huv
        | inr v =>
            exfalso
            have hv := congrArg (fun h : {h : H // h ∈ S} => (h : H)) hpq
            simp only [phi] at hv
            exact hcross u v hv
    | inr u =>
        cases q with
        | inl v =>
            exfalso
            have hv := congrArg (fun h : {h : H // h ∈ S} => (h : H)) hpq
            simp only [phi] at hv
            exact hcross v u hv.symm
        | inr v =>
            have huv : u = v := by
              apply Subtype.ext
              have hv := congrArg (fun h : {h : H // h ∈ S} => (h : H)) hpq
              simp only [phi] at hv
              exact mul_left_cancel hv
            exact congrArg Sum.inr huv
  have hphi_surj : Function.Surjective phi := by
    intro h
    have hhK : ((h : H) : G) ∈ K := by
      simpa only [S, Finset.mem_filter, Finset.mem_univ, true_and] using h.property
    rcases (hKcosets h).1 hhK with ⟨u, hu⟩ | ⟨u, hu⟩
    · refine ⟨Sum.inl u, ?_⟩
      apply Subtype.ext
      simpa only [phi] using hu.symm
    · refine ⟨Sum.inr u, ?_⟩
      apply Subtype.ext
      simpa only [phi] using hu.symm
  let e : (N ⊕ N) ≃ {h : H // h ∈ S} :=
    Equiv.ofBijective phi ⟨hphi_inj, hphi_surj⟩
  have hsumS : ∑ h ∈ S, a h = 2 * ∑ u : N, a (x * (u : H)) := by
    rw [← S.sum_attach]
    calc
      (∑ h : {h : H // h ∈ S}, a h) =
          ∑ z : N ⊕ N, a ((e z : {h : H // h ∈ S}) : H) := by
        exact (Equiv.sum_comp e (fun h : {h : H // h ∈ S} => a h)).symm
      _ = (∑ u : N, a (x * (u : H))) +
          ∑ u : N, a (x⁻¹ * (u : H)) := by
        rw [Fintype.sum_sum_type]
        rfl
      _ = 2 * ∑ u : N, a (x * (u : H)) := by
        simp_rw [hpair]
        ring
  have htotal :
      (∑ h : H, eta h * star (a h : ℂ)) =
        8 * (∑ u : N, a (x * (u : H)) : ℂ) := by
    calc
      (∑ h : H, eta h * star (a h : ℂ)) =
          ∑ h ∈ S, eta h * star (a h : ℂ) := by
        symm
        apply Finset.sum_subset (by simp)
        intro h _hh hnot
        have hhK : (h : G) ∉ K := by
          simpa only [S, Finset.mem_filter, Finset.mem_univ, true_and] using hnot
        rw [hetaSupport h hhK]
        simp
      _ = ∑ h ∈ S, (4 : ℂ) * (a h : ℂ) := by
        apply Finset.sum_congr rfl
        intro h hh
        have hhK : (h : G) ∈ K := by
          simpa only [S, Finset.mem_filter, Finset.mem_univ, true_and] using hh
        rw [hetaK h hhK]
        simp
      _ = 4 * (∑ h ∈ S, (a h : ℂ)) := by rw [Finset.mul_sum]
      _ = 4 * ((∑ h ∈ S, a h : ℤ) : ℂ) := by push_cast; rfl
      _ = 4 * ((2 * ∑ u : N, a (x * (u : H)) : ℤ) : ℂ) := by rw [hsumS]
      _ = 8 * (∑ u : N, a (x * (u : H)) : ℂ) := by push_cast; ring
  have hscalar' :
      ((Nat.card H : ℂ)⁻¹ *
        (8 * (∑ u : N, a (x * (u : H)) : ℂ))) = (c : ℂ) := by
    calc
      _ = (Nat.card H : ℂ)⁻¹ *
          ∑ h : H, eta h * star (a h : ℂ) := by rw [htotal]
      _ = (c : ℂ) := hscalar
  rw [hHcard, Nat.cast_mul] at hscalar'
  have hNne : (Nat.card N : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := N)).ne'
  have hcomplex :
      (∑ u : N, a (x * (u : H)) : ℂ) = (c * Nat.card N : ℤ) := by
    field_simp [hNne] at hscalar'
    apply mul_left_cancel₀ (by norm_num : (8 : ℂ) ≠ 0)
    simpa [mul_assoc, mul_comm, mul_left_comm] using hscalar'
  exact_mod_cast hcomplex


set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
private lemma example3_stage_i_character_value
    {G : Type u} [Group G] [Finite G]
    (hG : IsSimpleGroup G)
    (Q : Sylow 2 G) (hQeight : Nat.card Q = 8)
    (H : Subgroup G) (N : Subgroup H)
    (hNodd : Nat.Coprime 2 (Nat.card N))
    (hHcard : Nat.card H = 8 * Nat.card N)
    (K : Set G) (eta : Section1.ClassFunction H)
    (zeta chi : Section1.ClassFunction G)
    (hzeta_def : zeta = Section1.inducedCF H eta)
    (hzetaVirtual : Theory.Character.IsVirtualCharacter zeta)
    (hzetaSmall : ∀ g : G,
      ((∃ y : G, y * g * y⁻¹ ∈ K) ∧ zeta g = 4) ∨
      ((¬ ∃ y : G, y * g * y⁻¹ ∈ K) ∧ zeta g = 0))
    (hKfour : ∀ k : G, k ∈ K → 4 ∣ orderOf k)
    (x : H) (hxOrder : orderOf (x : G) = 4)
    (hxcomm : ∀ u : N, Commute (x : G) (u : G))
    (hKcosets : ∀ h : H, (h : G) ∈ K ↔
      (∃ u : N, h = x * (u : H)) ∨
      (∃ u : N, h = x⁻¹ * (u : H)))
    (hetaK : ∀ h : H, (h : G) ∈ K → eta h = 4)
    (hetaSupport : ∀ h : H, (h : G) ∉ K → eta h = 0)
    (hchi : Section1.IsIrreducibleCharacterOnGroup chi)
    (hchi_nonprincipal : chi ≠ Section1.principalCharacter G)
    (hfixed : ∀ {a : ℕ}, a.Coprime (Nat.card G) →
      ∀ g : G, chi (g ^ a) = chi g)
    (hchiInt : ∀ g : G, ∃ z : ℤ, chi g = (z : ℂ))
    (epsilon : ℂ) (hepsilon : epsilon = 1 ∨ epsilon = -1)
    (hscalarChi : Section1.scalarProduct G zeta chi = epsilon) :
    chi (x : G) = epsilon := by
  classical
  let : Fintype G := Fintype.ofFinite G
  let : Fintype H := Fintype.ofFinite H
  let : Fintype N := Fintype.ofFinite N
  rcases hchi with ⟨degree, rho, hirr, hchar⟩
  have hchi' : Section1.IsIrreducibleCharacterOnGroup chi :=
    ⟨degree, rho, hirr, hchar⟩
  obtain ⟨epsilonZ, hepsilonZ, hepsilonCast⟩ :
      ∃ epsilonZ : ℤ, (epsilonZ = 1 ∨ epsilonZ = -1) ∧
        epsilon = (epsilonZ : ℂ) := by
    rcases hepsilon with heps | heps
    · exact ⟨1, Or.inl rfl, by rw [heps]; norm_num⟩
    · exact ⟨-1, Or.inr rfl, by rw [heps]; norm_num⟩
  let a : G → ℤ := fun g => Classical.choose (hchiInt g)
  have ha (g : G) : chi g = (a g : ℂ) :=
    Classical.choose_spec (hchiInt g)
  have hchiClass : Section1.IsClassFunction chi :=
    Section1.isCharacter_isClassFunction chi
      (Section1.isCharacter_of_isIrreducibleCharacterOnGroup hchi')
  let chiSq : Section1.ClassFunction G := chi * chi
  let rhoSq := Section1.standardizeRepresentation (rho.tprod rho)
  have hchiSqVirtual : Theory.Character.IsVirtualCharacter chiSq := by
    refine ⟨1, (fun _ : Fin 1 => (1 : ℤ)),
      (fun _ : Fin 1 => Module.finrank ℂ
        (TensorProduct ℂ (Fin degree → ℂ) (Fin degree → ℂ))),
      (fun _ : Fin 1 => rhoSq), ?_⟩
    ext g
    simp [chiSq, rhoSq, Theory.Character.virtualCharacterOfRepresentations,
      Section1.standardizeRepresentation_character, Representation.char_tensor,
      ← hchar]
  have hchiSqClass : Section1.IsClassFunction chiSq :=
    Section1.isVirtualCharacter_isClassFunction hchiSqVirtual
  obtain ⟨m, hm⟩ :=
    Section1.scalarProduct_isVirtualCharacter_eq_int
      hzetaVirtual hchiSqVirtual
  have hscalarChiZ :
      Section1.scalarProduct G zeta chi = (epsilonZ : ℂ) := by
    rw [hscalarChi, hepsilonCast]
  have hscalarHChi :
      Section1.scalarProduct H eta
        (Section1.subgroupRestriction H chi) = (epsilonZ : ℂ) := by
    calc
      _ = Section1.scalarProduct G (Section1.inducedCF H eta) chi :=
        (Section1.scalarProduct_inducedCF_left H eta chi hchiClass).symm
      _ = Section1.scalarProduct G zeta chi := by rw [hzeta_def]
      _ = (epsilonZ : ℂ) := hscalarChiZ
  have hscalarHSq :
      Section1.scalarProduct H eta
        (Section1.subgroupRestriction H chiSq) = (m : ℂ) := by
    calc
      _ = Section1.scalarProduct G (Section1.inducedCF H eta) chiSq :=
        (Section1.scalarProduct_inducedCF_left H eta chiSq hchiSqClass).symm
      _ = Section1.scalarProduct G zeta chiSq := by rw [hzeta_def]
      _ = (m : ℂ) := hm
  have hGcard : Nat.card G = 8 * Q.index := by
    calc
      Nat.card G = Nat.card Q * Q.index := Q.card_mul_index.symm
      _ = 8 * Q.index := by rw [hQeight]
  have hN_dvd_index : Nat.card N ∣ Q.index := by
    have hHdvdG := Subgroup.card_subgroup_dvd_card H
    rw [hHcard, hGcard] at hHdvdG
    exact (Nat.mul_dvd_mul_iff_left (by norm_num : 0 < 8)).mp hHdvdG
  have hchiInv (g : G) : chi g⁻¹ = chi g := by
    calc
      chi g⁻¹ = rho.character g⁻¹ := congrFun hchar g⁻¹
      _ = star (rho.character g) :=
        Theory.Representation.representation_character_inv_eq_star_character rho g
      _ = star (chi g) := by rw [hchar]
      _ = chi g := by rw [ha g]; simp
  have hpairPow (u : N) :
      chi ((x : G) * (u : G)) = chi ((x : G) * (u : G)⁻¹) := by
    have huOrder : orderOf (u : G) ∣ Nat.card N := by
      simpa [Subgroup.orderOf_coe] using orderOf_dvd_natCard u
    exact (example3_character_mul_inv_eq_of_argumentPow_fixed
      Q hQeight hN_dvd_index hxOrder (hxcomm u) huOrder chi hfixed).choose_spec.2.2
  have hpairCosets (u : N) :
      a (((x⁻¹ * (u : H) : H) : G)) =
        a ((((x * (u : H) : H) : G))) := by
    have hgroup :
        (x⁻¹ * (u : H) : H) =
          ((x * (u : H)⁻¹ : H)⁻¹) := by
      apply Subtype.ext
      change (x : G)⁻¹ * (u : G) =
        ((x : G) * (u : G)⁻¹)⁻¹
      calc
        (x : G)⁻¹ * (u : G) = (u : G) * (x : G)⁻¹ :=
          (hxcomm u).inv_left.eq
        _ = ((x : G) * (u : G)⁻¹)⁻¹ := by simp
    have hvalue :
        chi (((x⁻¹ * (u : H) : H) : G)) =
          chi ((((x * (u : H) : H) : G))) := by
      calc
        chi (((x⁻¹ * (u : H) : H) : G)) =
            chi (((x * (u : H)⁻¹ : H)⁻¹ : H) : G) := by rw [hgroup]
        _ = chi (((x * (u : H)⁻¹ : H) : G)) := hchiInv _
        _ = chi (((x * (u : H) : H) : G)) := (hpairPow u).symm
    exact_mod_cast (ha _).symm.trans (hvalue.trans (ha _))
  have hscalarSumChi :
      (Nat.card H : ℂ)⁻¹ *
        ∑ h : H, eta h * star (a (h : G) : ℂ) =
          (epsilonZ : ℂ) := by
    simpa [Section1.scalarProduct, Section1.subgroupRestriction, ha] using
      hscalarHChi
  have hscalarSumSq :
      (Nat.card H : ℂ)⁻¹ *
        ∑ h : H, eta h * star ((a (h : G) ^ 2 : ℤ) : ℂ) =
          (m : ℂ) := by
    simpa [Section1.scalarProduct, Section1.subgroupRestriction, chiSq,
      ha, pow_two] using hscalarHSq
  let ax : N → ℤ := fun u => a (((x * (u : H) : H) : G))
  have hfirstMoment :
      ∑ u : N, ax u = epsilonZ * Nat.card N := by
    simpa [ax] using example3_small_two_coset_sum
      H N K eta x hNodd hxOrder hKcosets hetaK hetaSupport
      (fun h : H => a (h : G)) hpairCosets hHcard epsilonZ hscalarSumChi
  have hsecondMoment :
      ∑ u : N, ax u ^ 2 = m * Nat.card N := by
    simpa [ax] using example3_small_two_coset_sum
      H N K eta x hNodd hxOrder hKcosets hetaK hetaSupport
      (fun h : H => a (h : G) ^ 2)
      (fun u => congrArg (fun z : ℤ => z ^ 2) (hpairCosets u))
      hHcard m hscalarSumSq
  have haxInv (u : N) : ax u⁻¹ = ax u := by
    dsimp [ax]
    exact_mod_cast (ha _).symm.trans ((hpairPow u).symm.trans (ha _))
  obtain ⟨parityTail, hparity⟩ :=
    example3_sum_eq_one_add_even_of_inv hNodd ax haxInv
  have hcardNOddNat : Odd (Nat.card N) :=
    Nat.coprime_two_left.mp hNodd
  have hcardNOdd : Odd (Nat.card N : ℤ) := by
    exact_mod_cast hcardNOddNat
  have hepsilonOdd : Odd epsilonZ := by
    rcases hepsilonZ with rfl | rfl <;> norm_num
  have hsumOdd : Odd (∑ u : N, ax u) := by
    rw [hfirstMoment]
    exact hepsilonOdd.mul hcardNOdd
  have haxOneOdd : Odd (ax 1) := by
    rcases hsumOdd with ⟨q, hq⟩
    refine ⟨q - parityTail, ?_⟩
    omega
  have hsqParity :
      (((∑ u : N, ax u ^ 2 : ℤ) : ℤ) : ZMod 2) =
        (((∑ u : N, ax u : ℤ) : ℤ) : ZMod 2) := by
    push_cast
    apply Finset.sum_congr rfl
    intro u _hu
    have hbool : ∀ z : ZMod 2, z ^ 2 = z := by decide
    simp [hbool (ax u : ZMod 2)]
  have hsqOdd : Odd (∑ u : N, ax u ^ 2) := by
    apply ZMod.intCast_eq_one_iff_odd.mp
    rw [hsqParity]
    exact ZMod.intCast_eq_one_iff_odd.mpr hsumOdd
  have hmOdd : Odd m := by
    apply ZMod.intCast_eq_one_iff_odd.mp
    have hprod :
        (((m * Nat.card N : ℤ) : ℤ) : ZMod 2) = 1 := by
      rw [← hsecondMoment]
      exact ZMod.intCast_eq_one_iff_odd.mpr hsqOdd
    have hcardCast : (((Nat.card N : ℕ) : ℤ) : ZMod 2) = 1 :=
      ZMod.intCast_eq_one_iff_odd.mpr hcardNOdd
    push_cast at hprod
    have hcardCastNat : (Nat.card N : ZMod 2) = 1 := by
      exact_mod_cast hcardCast
    rw [hcardCastNat, mul_one] at hprod
    exact hprod
  by_contra hvalue
  have haxOneNe : ax 1 ≠ epsilonZ := by
    intro heq
    apply hvalue
    calc
      chi (x : G) = (a (x : G) : ℂ) := ha _
      _ = (ax 1 : ℤ) := by simp [ax]
      _ = (epsilonZ : ℤ) := by rw [heq]
      _ = epsilon := hepsilonCast.symm
  have hmThree : 3 ≤ m :=
    example3_positive_odd_scalar_ge_three ax 1 epsilonZ m hepsilonZ
      haxOneOdd hfirstMoment hsecondMoment hmOdd haxOneNe
  let support : G → Prop := fun g => ∃ y : G, y * g * y⁻¹ ∈ K
  let S : Finset G := Finset.univ.filter support
  let zetaZ : G → ℤ := fun g => if support g then 4 else 0
  have hzetaZ (g : G) : zeta g = (zetaZ g : ℂ) := by
    rcases hzetaSmall g with ⟨hg, hfour⟩ | ⟨hg, hzero⟩
    · simp [zetaZ, support, hg, hfour]
    · simp [zetaZ, support, hg, hzero]
  have hsumSupport (b : G → ℤ) :
      ∑ g : G, zetaZ g * b g = 4 * ∑ g ∈ S, b g := by
    rw [show (fun g => zetaZ g * b g) =
        (fun g => if support g then 4 * b g else 0) by
          funext g
          simp [zetaZ]]
    rw [← Finset.sum_filter]
    change (∑ g ∈ S, 4 * b g) = _
    rw [Finset.mul_sum]
  have hrowRaw :=
    example3_integer_scalar_product_sum chi chi a a ha ha 1
      (by simpa only [Int.cast_one] using
        Section1.scalarProduct_irreducibleCharacter_self hchi')
  have hrow :
      ∑ g : G, a g ^ 2 = Fintype.card G := by
    simpa [pow_two, Nat.card_eq_fintype_card] using hrowRaw
  have hprincipalValue :
      ∀ g : G, Section1.principalCharacter G g = ((1 : ℤ) : ℂ) := by
    intro g
    simp [Section1.principalCharacter]
  have hsumRaw :=
    example3_integer_scalar_product_sum chi
      (Section1.principalCharacter G) a (fun _ => 1)
      ha hprincipalValue 0
      (by simpa only [Int.cast_zero] using
        (Section1.scalarProduct_irreducibleCharacter_principal_eq_zero_of_ne
          hchi' hchi_nonprincipal))
  have hsum : ∑ g : G, a g = 0 := by
    simpa using hsumRaw
  have hglobalLin :=
    example3_integer_scalar_product_sum zeta chi zetaZ a hzetaZ ha
      epsilonZ hscalarChiZ
  have hsupportLinRaw :
      4 * ∑ g ∈ S, a g = Nat.card G * epsilonZ := by
    simpa [hsumSupport] using hglobalLin
  have hsupportLin :
      4 * ∑ g ∈ S, epsilonZ * a g = Fintype.card G := by
    rcases hepsilonZ with rfl | rfl
    · simpa [Nat.card_eq_fintype_card] using hsupportLinRaw
    · rw [show ∑ g ∈ S, (-1 : ℤ) * a g =
          -(∑ g ∈ S, a g) by rw [← Finset.mul_sum]; ring]
      rw [Nat.card_eq_fintype_card] at hsupportLinRaw
      nlinarith
  have hglobalSq :=
    example3_integer_scalar_product_sum zeta chiSq zetaZ
      (fun g => a g ^ 2) hzetaZ
      (fun g => by simp [chiSq, ha, pow_two]) m hm
  have hsupportSq :
      4 * ∑ g ∈ S, a g ^ 2 = Fintype.card G * m := by
    rw [hsumSupport] at hglobalSq
    simpa [Nat.card_eq_fintype_card] using hglobalSq
  have honeNotSupport : (1 : G) ∉ S := by
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    intro hone
    rcases hone with ⟨y, hy⟩
    have honeK : (1 : G) ∈ K := by simpa using hy
    have := hKfour 1 honeK
    simp at this
  have hpointwise :
      ∀ g ∈ Finset.univ \ S, -epsilonZ * a g ≤ a g ^ 2 := by
    intro g _hg
    rcases hepsilonZ with rfl | rfl <;> nlinarith [sq_nonneg (a g)]
  have hdegreeGt : 1 < degree :=
    example3_simple_nonprincipal_degree_gt_one hG Q hQeight chi hchi'
      hchi_nonprincipal degree rho hirr hchar
  have hchiOne : chi 1 = (degree : ℂ) := by
    rw [hchar]
    simp [Representation.character]
  have haOne : a 1 = (degree : ℤ) := by
    exact_mod_cast (ha 1).symm.trans hchiOne
  have hstrict : -epsilonZ * a 1 < a 1 ^ 2 := by
    rw [haOne]
    rcases hepsilonZ with rfl | rfl <;> nlinarith
  exact example3_row_orthogonality_arithmetic_core
    S a 1 epsilonZ m hepsilonZ honeNotSupport hpointwise hstrict
      hrow hsupportSq hsum hsupportLin hmThree


/-- Private continuation for the PNG proof, starting at source stage (c).
The public theorem only exposes Suzuki's stated endpoint; all stage data remains local. -/
private lemma suzuki_example3_stage_c_to_l_core
    {G : Type u} [Group G] [Finite G]
    (Q : Sylow 2 G) {n : ℕ} (hn : 3 ≤ n)
    (hQ : Nonempty (Q ≃* QuaternionGroup (2 ^ (n - 2))))
    (H X : Subgroup G) (CH : Subgroup H)
    (hQcard_X : Nat.card Q = 2 * Nat.card X)
    (NH : Subgroup H)
    (_hNHnormal : NH.Normal)
    (hNHodd : Nat.Coprime 2 (Nat.card NH))
    (hHcard_Q_NH : Nat.card H = Nat.card Q * Nat.card NH)
    (lambda : Section1.ClassFunction CH)
    (eta : Section1.ClassFunction H)
    (K : Set G)
    (hsmallXData : Nat.card X = 4 →
      ∃ x : H, (x : G) ∈ K ∧ orderOf (x : G) = 4 ∧
        (∀ u : NH, Commute (x : G) (u : G)) ∧
        ∀ h : H, (h : G) ∈ K ↔
          (∃ u : NH, h = x * (u : H)) ∨
          (∃ u : NH, h = x⁻¹ * (u : H)))
    (hKTI : IsTISubsetRelative H K)
    (hKfour : ∀ k : G, k ∈ K → 4 ∣ orderOf k)
    (hetaKSmall : Nat.card X = 4 →
      ∀ (k : G) (hk : k ∈ K), eta ⟨k, hKTI.1 hk⟩ = 4)
    (hetaSupport : ∀ h : H, (h : G) ∉ K → eta h = 0)
    (hetaOne : eta 1 = 0)
    (_hCHnormal : CH.Normal)
    (_hHquotCcard : Nat.card (H ⧸ CH) = 2)
    (hlambda_irreducible :
      Section1.IsIrreducibleCharacterOnGroup lambda)
    (_hlambda_ne_principal :
      lambda ≠ Section1.principalCharacter CH)
    (heta_def :
      eta = Section1.inducedCF CH
        (Section1.principalCharacter CH - lambda))
    (_heta_principal :
      Section1.scalarProduct H eta
        (Section1.principalCharacter H) = 1)
    (hstage_c_input :
      Section1.scalarProduct H eta (Section1.principalCharacter H) = 1 ∧
      (Section1.scalarProduct H eta eta = 3 ∨
        Section1.scalarProduct H eta eta = 4) ∧
      (4 < Nat.card X →
        Section1.scalarProduct H eta eta = 3) ∧
      (Nat.card X = 4 →
        Section1.scalarProduct H eta eta = 4))
    (hzetaIntSmall : Nat.card X = 4 →
      ∀ g : G, ∃ n : ℤ, Section1.inducedCF H eta g = (n : ℂ))
    (hzetaSmall : Nat.card X = 4 → ∀ g : G,
      ((∃ x : G, x * g * x⁻¹ ∈ K) ∧
        Section1.inducedCF H eta g = 4) ∨
      ((¬ ∃ x : G, x * g * x⁻¹ ∈ K) ∧
        Section1.inducedCF H eta g = 0))
    (hcore : pPrimeCore 2 G = ⊥)
    (hind : ∀ (M : Type u) [Group M] [Finite M],
      Nat.card M < Nat.card G →
      ∀ (S : Sylow 2 M) {m : ℕ}, 3 ≤ m →
        Nonempty (S ≃* QuaternionGroup (2 ^ (m - 2))) →
        2 ∣ Nat.card (Subgroup.center (M ⧸ pPrimeCore 2 M))) :
    2 ∣ Nat.card (Subgroup.center (G ⧸ pPrimeCore 2 G)) := by
  let zeta : Section1.ClassFunction G := Section1.inducedCF H eta
  have hstage_c :
      Section1.scalarProduct H eta (Section1.principalCharacter H) = 1 ∧
      (Section1.scalarProduct H eta eta = 3 ∨
        Section1.scalarProduct H eta eta = 4) ∧
      (4 < Nat.card X →
        Section1.scalarProduct H eta eta = 3) ∧
      (Nat.card X = 4 →
        Section1.scalarProduct H eta eta = 4) :=
    hstage_c_input
  have hstage_d :
      ∃ (r : ℕ) (chi : Fin r → Section1.ClassFunction G)
          (epsilon : Fin r → ℂ),
        (∀ i, Section1.IsIrreducibleCharacterOnGroup (chi i)) ∧
        Function.Injective chi ∧
        (∀ i, chi i ≠ Section1.principalCharacter G) ∧
        (∀ i, epsilon i = 1 ∨ epsilon i = -1) ∧
        zeta =
          Section1.principalCharacter G +
            Section1.weightedFamilySum epsilon chi ∧
        (4 < Nat.card X → r = 2) ∧
        (Nat.card X = 4 → r = 3) := by
    have hlambdaVirtual : Theory.Character.IsVirtualCharacter lambda :=
      Section3.isVirtualCharacter_of_irreducibleCharacterOnGroup
        hlambda_irreducible
    have hetaVirtual : Theory.Character.IsVirtualCharacter eta := by
      rw [heta_def]
      exact Section2.inducedCF_isVirtualCharacter_of_virtualCharacter CH
        (Section3.isVirtualCharacter_sub
          Section3.isVirtualCharacter_principalCharacter hlambdaVirtual)
    have hzetaVirtual : Theory.Character.IsVirtualCharacter zeta := by
      exact Section2.inducedCF_isVirtualCharacter_of_virtualCharacter H hetaVirtual
    have hprop := suzuki_ch6_proposition_2_9
      H K hKTI eta hetaVirtual hetaSupport
    have hzetaPrincipal :
        Section1.scalarProduct G zeta
          (Section1.principalCharacter G) = 1 := by
      calc
        _ = Section1.scalarProduct H eta
            (Section1.principalCharacter H) := by
              simpa [zeta] using hprop.2.1
        _ = 1 := hstage_c.1
    have hzetaSelf :
        Section1.scalarProduct G zeta zeta =
          Section1.scalarProduct H eta eta := by
      simpa [zeta] using
        hprop.2.2 hetaOne eta hetaVirtual hetaSupport
    rcases hstage_c.2.1 with hnorm3 | hnorm4
    · rcases example3_low_norm_virtual_character_decomposition
          zeta 2 (Or.inl rfl) hzetaVirtual hzetaPrincipal (by
            rw [hzetaSelf, hnorm3]
            norm_num) with
        ⟨chi, epsilon, hchi, hchiInjective, hchiNonprincipal, hepsilon, hdecomp⟩
      refine ⟨2, chi, epsilon, hchi, hchiInjective, hchiNonprincipal, hepsilon, hdecomp, ?_, ?_⟩
      · intro _hlarge
        rfl
      · intro hfour
        have := hstage_c.2.2.2 hfour
        rw [hnorm3] at this
        norm_num at this
    · rcases example3_low_norm_virtual_character_decomposition
          zeta 3 (Or.inr rfl) hzetaVirtual hzetaPrincipal (by
            rw [hzetaSelf, hnorm4]
            norm_num) with
        ⟨chi, epsilon, hchi, hchiInjective, hchiNonprincipal, hepsilon, hdecomp⟩
      refine ⟨3, chi, epsilon, hchi, hchiInjective, hchiNonprincipal, hepsilon, hdecomp, ?_, ?_⟩
      · intro hlarge
        have := hstage_c.2.2.1 hlarge
        rw [hnorm4] at this
        norm_num at this
      · intro _hfour
        rfl
  obtain ⟨r, chi, epsilon, hchi_irreducible, hchi_injective, hchi_nonprincipal, hepsilon_sign,
      hzeta_decomposition, hr_large, hr_small⟩ := hstage_d
  let : Fintype (Fin r) := Fintype.ofFinite (Fin r)
  have hstage_e :
      ∃ (t : G) (d e f : Fin r → ℂ),
        orderOf t = 2 ∧
        (∀ i, d i = chi i 1) ∧
        (∀ i, e i = chi i t) ∧
        (∀ i, f i = d i - e i) ∧
        (∑ i, epsilon i * f i) = 0 ∧
        (∑ i, epsilon i * f i ^ 2 / d i) = 0 := by
    obtain ⟨t, ht⟩ :=
      example3_exists_involution_of_generalizedQuaternionSylow Q hQ
    let d : Fin r → ℂ := fun i => chi i 1
    let e : Fin r → ℂ := fun i => chi i t
    let f : Fin r → ℂ := fun i => d i - e i
    have hzeta_one : zeta 1 = 0 := by
      dsimp [zeta]
      unfold Section1.inducedCF Section1.inducedClassFunction
      apply mul_eq_zero_of_right
      apply Finset.sum_eq_zero
      intro x _hx
      split
      next hmem =>
        have harg : (⟨x * 1 * x⁻¹, hmem⟩ : H) = 1 := by
          apply Subtype.ext
          simp
        rw [harg, hetaOne]
      next _hnot => rfl
    have hzeta_t : zeta t = 0 := by
      dsimp [zeta]
      exact example3_inducedCF_vanishes_at_involution
        H eta K hKfour hetaSupport ht
    have hsum_d_raw :
        1 + ∑ i, epsilon i * chi i 1 = 0 := by
      calc
        1 + ∑ i, epsilon i * chi i 1 =
            (Section1.principalCharacter G +
              Section1.weightedFamilySum epsilon chi) 1 := by
                simp [Section1.principalCharacter,
                  Section1.weightedFamilySum]
        _ = zeta 1 := congrFun hzeta_decomposition.symm 1
        _ = 0 := hzeta_one
    have hsum_e_raw :
        1 + ∑ i, epsilon i * chi i t = 0 := by
      calc
        1 + ∑ i, epsilon i * chi i t =
            (Section1.principalCharacter G +
              Section1.weightedFamilySum epsilon chi) t := by
                simp [Section1.principalCharacter,
                  Section1.weightedFamilySum]
        _ = zeta t := congrFun hzeta_decomposition.symm t
        _ = 0 := hzeta_t
    have hsum_f : (∑ i, epsilon i * f i) = 0 := by
      calc
        (∑ i, epsilon i * f i) =
            (∑ i, epsilon i * d i) - (∑ i, epsilon i * e i) := by
              rw [← Finset.sum_sub_distrib]
              apply Finset.sum_congr rfl
              intro i _hi
              dsimp [f]
              ring
        _ = 0 := by
          have hsum_d : 1 + ∑ i, epsilon i * d i = 0 := by
            simpa [d] using hsum_d_raw
          have hsum_e : 1 + ∑ i, epsilon i * e i = 0 := by
            simpa [e] using hsum_e_raw
          linear_combination hsum_d - hsum_e
    have hsum_e_sq_raw :
        1 + ∑ i, epsilon i * chi i t ^ 2 / chi i 1 = 0 := by
      have hraw := example3_stage_e_structure_constant_identity Q hQ H eta K hKfour
        hetaSupport zeta rfl chi epsilon hchi_irreducible
          hzeta_decomposition ht
      rw [show @Finset.univ (Fin r) (Fin.fintype r) =
        @Finset.univ (Fin r) (Fintype.ofFinite (Fin r)) by ext; simp] at hraw
      exact hraw
    have hsum_f_sq : (∑ i, epsilon i * f i ^ 2 / d i) = 0 := by
      have hd_ne : ∀ i, d i ≠ 0 := by
        intro i
        dsimp [d]
        simpa [Section1.degree] using
          (Section3.degree_ne_zero_of_isIrreducibleCharacterOnGroup
            (chi i) (hchi_irreducible i))
      have hexpand :
          (∑ i, epsilon i * f i ^ 2 / d i) =
            (∑ i, epsilon i * d i) -
              2 * (∑ i, epsilon i * e i) +
                ∑ i, epsilon i * e i ^ 2 / d i := by
        calc
          (∑ i, epsilon i * f i ^ 2 / d i) =
              ∑ i, (epsilon i * d i -
                2 * (epsilon i * e i) +
                  epsilon i * e i ^ 2 / d i) := by
                    apply Finset.sum_congr rfl
                    intro i _hi
                    dsimp [f]
                    field_simp [hd_ne i]
                    ring
          _ = (∑ i, epsilon i * d i) -
              2 * (∑ i, epsilon i * e i) +
                ∑ i, epsilon i * e i ^ 2 / d i := by
                  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
                    Finset.mul_sum]
      rw [hexpand]
      have hsum_d : 1 + ∑ i, epsilon i * d i = 0 := by
        simpa [d] using hsum_d_raw
      have hsum_e : 1 + ∑ i, epsilon i * e i = 0 := by
        simpa [e] using hsum_e_raw
      have hsum_e_sq :
          1 + ∑ i, epsilon i * e i ^ 2 / d i = 0 := by
        simpa [d, e] using hsum_e_sq_raw
      linear_combination hsum_d - 2 * hsum_e + hsum_e_sq
    refine ⟨t, d, e, f, ?_, ?_, ?_, ?_, hsum_f, hsum_f_sq⟩
    · exact orderOf_eq_prime ht.sq_eq_one ht.ne_one
    · intro i
      rfl
    · intro i
      rfl
    · intro i
      rfl
  obtain ⟨t, d, e, f, ht_order, hd, he, hf, hsum_f, hsum_f_sq⟩ := hstage_e
  have hstage_f :
      16 ≤ Nat.card Q →
        ∀ i : Fin r,
          ∃ (m : ℕ) (rho : Representation ℂ G (Fin m → ℂ)),
            Representation.IsIrreducible rho ∧
              chi i = rho.character ∧ t ∈ rho.ker := by
    intro hQlarge
    have hXlarge : 4 < Nat.card X := by
      rw [hQcard_X] at hQlarge
      omega
    have hr2 : r = 2 := hr_large hXlarge
    subst r
    have hzeta_one : zeta 1 = 0 := by
      dsimp [zeta]
      unfold Section1.inducedCF Section1.inducedClassFunction
      apply mul_eq_zero_of_right
      apply Finset.sum_eq_zero
      intro x _hx
      split
      next hmem =>
        have harg : (⟨x * 1 * x⁻¹, hmem⟩ : H) = 1 := by
          apply Subtype.ext
          simp
        rw [harg, hetaOne]
      next _hnot => rfl
    have hsum_d : 1 + ∑ i, epsilon i * d i = 0 := by
      calc
        1 + ∑ i, epsilon i * d i =
            (Section1.principalCharacter G +
              Section1.weightedFamilySum epsilon chi) 1 := by
                simp [Section1.principalCharacter,
                  Section1.weightedFamilySum, hd]
        _ = zeta 1 := congrFun hzeta_decomposition.symm 1
        _ = 0 := hzeta_one
    rw [show
      @Finset.univ (Fin 2) (Fintype.ofFinite (Fin 2)) =
        @Finset.univ (Fin 2) (Fin.fintype 2) by
          ext i
          simp] at hsum_d hsum_f hsum_f_sq
    have hsum_d_two :
        1 + epsilon 0 * d 0 + epsilon 1 * d 1 = 0 := by
      simpa [Fin.sum_univ_two, add_assoc] using hsum_d
    have hsum_f_two : epsilon 0 * f 0 + epsilon 1 * f 1 = 0 := by
      simpa [Fin.sum_univ_two] using hsum_f
    have hsum_f_sq_two :
        epsilon 0 * f 0 ^ 2 / d 0 + epsilon 1 * f 1 ^ 2 / d 1 = 0 := by
      simpa [Fin.sum_univ_two] using hsum_f_sq
    have hdegreeData : ∀ i : Fin 2,
        ∃ m : ℕ, 0 < m ∧ d i = (m : ℂ) := by
      intro i
      rcases hchi_irreducible i with ⟨m, rho, hirr, hchar⟩
      let : Representation.IsIrreducible rho := hirr
      let degreeNat := Module.finrank ℂ (Fin m → ℂ)
      have hpos : 0 < degreeNat := by
        exact (Module.finrank_pos_iff (R := ℂ) (M := Fin m → ℂ)).2
          (Theory.Character.irreducible_nontrivial (ρ := rho))
      refine ⟨degreeNat, hpos, ?_⟩
      rw [hd i, hchar]
      simp [degreeNat, Representation.character]
    obtain ⟨m0, hm0pos, hd0⟩ := hdegreeData 0
    obtain ⟨m1, hm1pos, hd1⟩ := hdegreeData 1
    have hd0ne : d 0 ≠ 0 := by
      rw [hd0]
      exact_mod_cast hm0pos.ne'
    have hd1ne : d 1 ≠ 0 := by
      rw [hd1]
      exact_mod_cast hm1pos.ne'
    have hm0C : (m0 : ℂ) ≠ 0 := by exact_mod_cast hm0pos.ne'
    have hm1C : (m1 : ℂ) ≠ 0 := by exact_mod_cast hm1pos.ne'
    have hsignOpp :
        (epsilon 0 = 1 ∧ epsilon 1 = -1) ∨
          (epsilon 0 = -1 ∧ epsilon 1 = 1) := by
      rcases hepsilon_sign 0 with he0 | he0 <;>
        rcases hepsilon_sign 1 with he1 | he1
      · exfalso
        have hre := congrArg Complex.re hsum_d_two
        have hm0R : (1 : ℝ) ≤ m0 := by exact_mod_cast hm0pos
        have hm1R : (1 : ℝ) ≤ m1 := by exact_mod_cast hm1pos
        norm_num [he0, he1, hd0, hd1] at hre
        nlinarith
      · exact Or.inl ⟨he0, he1⟩
      · exact Or.inr ⟨he0, he1⟩
      · exfalso
        have hre := congrArg Complex.re hsum_d_two
        have hm0R : (1 : ℝ) ≤ m0 := by exact_mod_cast hm0pos
        have hm1R : (1 : ℝ) ≤ m1 := by exact_mod_cast hm1pos
        norm_num [he0, he1, hd0, hd1] at hre
        nlinarith
    have hfall : ∀ i : Fin 2, f i = 0 := by
      rcases hsignOpp with ⟨he0, he1⟩ | ⟨he0, he1⟩
      · rw [he0, he1] at hsum_f_two hsum_f_sq_two hsum_d_two
        have hdegRe := congrArg Complex.re hsum_d_two
        rw [hd0, hd1] at hdegRe
        norm_num at hdegRe
        have hmrelR : (m1 : ℝ) = m0 + 1 := by linarith
        have hmrel : m1 = m0 + 1 := by exact_mod_cast hmrelR
        have hf01 : f 0 = f 1 := by
          apply sub_eq_zero.mp
          simpa [sub_eq_add_neg] using hsum_f_two
        have hfrel : f 1 = f 0 := hf01.symm
        rw [hfrel, hd0, hd1] at hsum_f_sq_two
        field_simp [hm0C, hm1C] at hsum_f_sq_two
        have hmrelC : (m1 : ℂ) = m0 + 1 := by exact_mod_cast hmrel
        rw [hmrelC] at hsum_f_sq_two
        ring_nf at hsum_f_sq_two
        have hf0 : f 0 = 0 := (sq_eq_zero_iff).mp hsum_f_sq_two
        have hf1 : f 1 = 0 := hf01 ▸ hf0
        intro i
        have hi : i = 0 ∨ i = 1 := by omega
        rcases hi with rfl | rfl
        · exact hf0
        · exact hf1
      · rw [he0, he1] at hsum_f_two hsum_f_sq_two hsum_d_two
        have hdegRe := congrArg Complex.re hsum_d_two
        rw [hd0, hd1] at hdegRe
        norm_num at hdegRe
        have hmrelR : (m0 : ℝ) = m1 + 1 := by linarith
        have hmrel : m0 = m1 + 1 := by exact_mod_cast hmrelR
        have hfrel : f 0 = f 1 := by
          apply sub_eq_zero.mp
          have hneg := congrArg Neg.neg hsum_f_two
          simpa [sub_eq_add_neg, add_comm] using hneg
        rw [hfrel, hd0, hd1] at hsum_f_sq_two
        field_simp [hm0C, hm1C] at hsum_f_sq_two
        have hmrelC : (m0 : ℂ) = m1 + 1 := by exact_mod_cast hmrel
        rw [hmrelC] at hsum_f_sq_two
        ring_nf at hsum_f_sq_two
        have hf1 : f 1 = 0 := (sq_eq_zero_iff).mp hsum_f_sq_two
        have hf0 : f 0 = 0 := hfrel.trans hf1
        intro i
        have hi : i = 0 ∨ i = 1 := by omega
        rcases hi with rfl | rfl
        · exact hf0
        · exact hf1
    intro i
    rcases hchi_irreducible i with ⟨m, rho, hirr, hchar⟩
    refine ⟨m, rho, hirr, hchar, ?_⟩
    let : Representation.IsIrreducible rho := hirr
    apply (suzuki_ch6_theorem_1_8_ii rho t).1
    rw [← hchar]
    have hfi := hfall i
    rw [hf i, hd i, he i] at hfi
    linear_combination -hfi
  have hstage_g :
      IsSimpleGroup G →
      (Nat.card Q = 8 →
        2 ∣ Nat.card (Subgroup.center (G ⧸ pPrimeCore 2 G))) →
      2 ∣ Nat.card (Subgroup.center (G ⧸ pPrimeCore 2 G)) := by
    intro hG hsmall
    rcases example3_quaternion_card_eq_eight_or_ge_sixteen hn hQ with hQeight | hQlarge
    · exact hsmall hQeight
    · exfalso
      have hXlarge : 4 < Nat.card X := by
        rw [hQcard_X] at hQlarge
        omega
      have hr2 : r = 2 := hr_large hXlarge
      subst r
      obtain ⟨m, rho, hirr, hchar, htker⟩ := hstage_f hQlarge 0
      exact example3_simple_kernel_contradiction hG (chi 0)
        (hchi_irreducible 0) (hchi_nonprincipal 0) t ht_order
        m rho hirr hchar htker
  have hstage_h :
      IsSimpleGroup G → Nat.card Q = 8 →
        2 ∣ Nat.card (Subgroup.center (G ⧸ pPrimeCore 2 G)) := by
    intro hG hQeight
    have hXfour : Nat.card X = 4 := by omega
    have hr3 : r = 3 := hr_small hXfour
    subst r
    have hd_ne : ∀ i : Fin 3, d i ≠ 0 := by
      intro i
      rw [hd i]
      simpa [Section1.degree] using
        (Section3.degree_ne_zero_of_isIrreducibleCharacterOnGroup
          (chi i) (hchi_irreducible i))
    have hfchi : ∀ i : Fin 3, f i = d i - chi i t := by
      intro i
      rw [hf i, he i]
    have hf_ne : ∀ i : Fin 3, f i ≠ 0 := by
      intro i hfi
      have hdit : d i = chi i t := by
        rw [hfchi i] at hfi
        exact sub_eq_zero.mp hfi
      have hvalue : chi i t = chi i 1 := by
        rw [← hd i]
        exact hdit.symm
      rcases hchi_irreducible i with ⟨m, rho, hirr, hchar⟩
      have htker : t ∈ rho.ker := by
        let : Representation.IsIrreducible rho := hirr
        apply (suzuki_ch6_theorem_1_8_ii rho t).1
        rw [← hchar]
        exact hvalue
      exact example3_simple_kernel_contradiction hG (chi i)
        (hchi_irreducible i) (hchi_nonprincipal i) t ht_order
        m rho hirr hchar htker
    have hzeta_one : zeta 1 = 0 := by
      dsimp [zeta]
      unfold Section1.inducedCF Section1.inducedClassFunction
      apply mul_eq_zero_of_right
      apply Finset.sum_eq_zero
      intro x _hx
      split
      next hmem =>
        have harg : (⟨x * 1 * x⁻¹, hmem⟩ : H) = 1 := by
          apply Subtype.ext
          simp
        rw [harg, hetaOne]
      next _hnot => rfl
    have hsum_d : 1 + ∑ i, epsilon i * d i = 0 := by
      calc
        1 + ∑ i, epsilon i * d i =
            (Section1.principalCharacter G +
              Section1.weightedFamilySum epsilon chi) 1 := by
                simp [Section1.principalCharacter,
                  Section1.weightedFamilySum, hd]
        _ = zeta 1 := congrFun hzeta_decomposition.symm 1
        _ = 0 := hzeta_one
    rw [show
      @Finset.univ (Fin 3) (Fintype.ofFinite (Fin 3)) =
        @Finset.univ (Fin 3) (Fin.fintype 3) by
          ext i
          simp] at hsum_d hsum_f hsum_f_sq
    have hetaVirtual : Theory.Character.IsVirtualCharacter eta := by
      rw [heta_def]
      exact Section2.inducedCF_isVirtualCharacter_of_virtualCharacter CH
        (Section3.isVirtualCharacter_sub
          Section3.isVirtualCharacter_principalCharacter
          (Section3.isVirtualCharacter_of_irreducibleCharacterOnGroup
            hlambda_irreducible))
    have hzetaVirtual : Theory.Character.IsVirtualCharacter zeta := by
      exact Section2.inducedCF_isVirtualCharacter_of_virtualCharacter H hetaVirtual
    have hzetaInt : ∀ g : G, ∃ n : ℤ, zeta g = (n : ℂ) := by
      exact hzetaIntSmall hXfour
    have htwoCard : 2 ∣ Nat.card G := by
      exact dvd_trans (by rw [hQeight]; norm_num)
        (Subgroup.card_subgroup_dvd_card (Q : Subgroup G))
    have hargumentPowFixed :
        ∀ {a : ℕ}, a.Coprime (Nat.card G) →
          ∀ i : Fin 3, ∀ g : G, chi i (g ^ a) = chi i g := by
      intro a ha
      have hzetaPow : ∀ g : G, zeta (g ^ a) = zeta g :=
        example3_argumentPow_eq_of_integer_valued_virtual
          hzetaVirtual hzetaInt ha
      have haTwo : a.Coprime 2 :=
        Nat.Coprime.of_dvd_right htwoCard ha
      have haOdd : Odd a := Nat.coprime_two_right.mp haTwo
      have htPow : t ^ a = t := by
        rcases haOdd with ⟨k, hk⟩
        rw [hk, pow_succ, pow_mul, show t ^ 2 = 1 from
          (orderOf_eq_prime_iff.mp ht_order).1, one_pow, one_mul]
      exact example3_three_constituent_argumentPow_fixed
        zeta chi epsilon d f t hchi_irreducible hchi_injective
          hchi_nonprincipal hepsilon_sign hzeta_decomposition hd hfchi
          hsum_d hsum_f hsum_f_sq hd_ne hf_ne ha hzetaPow htPow
    have hchiInt : ∀ i : Fin 3, ∀ g : G, ∃ z : ℤ, chi i g = (z : ℂ) := by
      intro i
      exact example3_irreducible_integer_valued_of_argumentPow_fixed
        (chi i) (hchi_irreducible i) (fun ha => hargumentPowFixed ha i)
    have hprincipal_chi : ∀ i : Fin 3,
        Section1.scalarProduct G (Section1.principalCharacter G) (chi i) = 0 := by
      intro i
      calc
        _ = star (Section1.scalarProduct G (chi i)
            (Section1.principalCharacter G)) :=
          (Section1.scalarProduct_star_swap _ _).symm
        _ = 0 := by
          rw [Section1.scalarProduct_irreducibleCharacter_principal_eq_zero_of_ne
            (hchi_irreducible i) (hchi_nonprincipal i)]
          simp
    have hchi_orth : ∀ i j : Fin 3,
        Section1.scalarProduct G (chi i) (chi j) = if i = j then 1 else 0 := by
      intro i j
      split
      next hij =>
        subst j
        exact Section1.scalarProduct_irreducibleCharacter_self
          (G := G) (hchi_irreducible i)
      next hij =>
        exact Section1.scalarProduct_irreducibleCharacter_eq_zero_of_ne
          (hchi_irreducible i) (hchi_irreducible j)
          (fun h => hij (hchi_injective h))
    have hscalar_chi : ∀ i : Fin 3,
        Section1.scalarProduct G zeta (chi i) = epsilon i := by
      intro i
      rw [hzeta_decomposition, Section1.scalarProduct_add_left,
        Section1.scalarProduct_weightedFamilySum_left, hprincipal_chi i]
      simp [hchi_orth]
    obtain ⟨x, hxK, hxOrder, hxcomm, hxcosets⟩ := hsmallXData hXfour
    have hHcard : Nat.card H = 8 * Nat.card NH := by
      rw [hHcard_Q_NH, hQeight]
    have hetaK : ∀ h : H, (h : G) ∈ K → eta h = 4 := by
      intro h hh
      simpa using hetaKSmall hXfour (h : G) hh
    have hchiX : ∀ i : Fin 3, chi i (x : G) = epsilon i := by
      intro i
      exact example3_stage_i_character_value hG Q hQeight H NH hNHodd
        hHcard K eta zeta (chi i) rfl hzetaVirtual (hzetaSmall hXfour)
        hKfour x hxOrder hxcomm hxcosets hetaK hetaSupport
        (hchi_irreducible i) (hchi_nonprincipal i)
        (fun ha g => hargumentPowFixed ha i g) (hchiInt i)
        (epsilon i) (hepsilon_sign i) (hscalar_chi i)
    have hstage_j :
        ∀ {a b : G}, orderOf a = 4 → orderOf b = 4 →
          ∃ g : G, g * a * g⁻¹ = b := by
      have hAxisCard :
          Nat.card {V : Subgroup Q // Nat.card V = 4} = 3 :=
        example3_generalized_quaternion_eight_order_four_axes_card
          hn hQ hQeight
      let eQ : Q ≃* QuaternionGroup (2 ^ (n - 2)) :=
        Classical.choice hQ
      obtain ⟨X0, U0, T0, hX0cyclic, hU0normal, hU0X0, hT0U0,
        hU0card, hT0card, hQcard0, hcenter0, hunique0, hinv0,
        hinvol0⟩ := generalizedQuaternion_source_subgroups hn eQ
      have hcenterCard :
          Nat.card (Subgroup.center (Q : Subgroup G)) = 2 := by
        rw [hcenter0, hT0card]
      rcases example3_normalizer_axis_fixed_or_transitive
          Q hQeight hAxisCard with hfixed | htrans
      · exfalso
        have hcontrolled :
            ∀ {a b : G}, a ∈ (Q : Subgroup G) →
              b ∈ (Q : Subgroup G) →
              (∃ g : G, g * a * g⁻¹ = b) →
              ∃ q : Q, (q : G) * a * (q : G)⁻¹ = b := by
          intro a b haQ hbQ hconj
          let aQ : Q := ⟨a, haQ⟩
          let bQ : Q := ⟨b, hbQ⟩
          have hordb : orderOf b = orderOf a := by
            obtain ⟨g, hg⟩ := hconj
            rw [← hg]
            change orderOf ((MulAut.conj g) a) = orderOf a
            exact (MulAut.conj g).orderOf_eq a
          rcases example3_order_eq_one_two_or_four_of_card_eight_center_two
              hQeight hcenterCard aQ with ha1 | ha2 | ha4
          · have haG : orderOf a = 1 := by
              simpa [aQ, Subgroup.orderOf_mk] using ha1
            have hbG : orderOf b = 1 := hordb.trans haG
            have hab : a = b := by
              rw [orderOf_eq_one_iff.mp haG,
                orderOf_eq_one_iff.mp hbG]
            exact ⟨1, by simp [hab]⟩
          · have hbG : orderOf b = 2 := by
              have haG : orderOf a = 2 := by
                simpa [aQ, Subgroup.orderOf_mk] using ha2
              exact hordb.trans haG
            have hb2 : orderOf bQ = 2 := by
              rw [← Subgroup.orderOf_coe]
              exact hbG
            have haInv : IsInvolution aQ := by
              have h := (orderOf_eq_prime_iff.mp ha2)
              exact ⟨h.2, h.1⟩
            have hbInv : IsInvolution bQ := by
              have h := (orderOf_eq_prime_iff.mp hb2)
              exact ⟨h.2, h.1⟩
            have habQ : aQ = bQ :=
              example3_sylow_involution_unique Q hQ
                aQ bQ haInv hbInv
            refine ⟨1, ?_⟩
            simpa [aQ, bQ] using
              congrArg (fun z : Q => (z : G)) habQ
          · have haG : orderOf a = 4 := by
              simpa [aQ, Subgroup.orderOf_mk] using ha4
            have hbG : orderOf b = 4 := hordb.trans haG
            have hb4 : orderOf (bQ : G) = 4 := by
              simpa [bQ] using hbG
            have hfixed' :
                ∀ n : Subgroup.normalizer
                    ((Q : Subgroup G) : Set G),
                  ∀ y : Q, orderOf (y : G) = 4 →
                    (n : G) * (y : G) * (n : G)⁻¹ ∈
                      Subgroup.zpowers (y : G) :=
              fun n y hy =>
                example3_axis_fixed_normalizer_preserves_zpowers
                  Q hfixed n y hy
            simpa [aQ, bQ] using
              example3_controlled_fusion_order_four
                Q hQeight hcenterCard hfixed' aQ bQ
                (by simpa [aQ] using haG) hb4 hconj
        have hnormalComplement : HasNormalPComplement 2 G :=
          BenderSuzuki.External.Suzuki.V.suzuki_ch5_theorem_2_27_v
            Q hcontrolled
        have hnormalComplementImpossible : False :=
          example3_simple_no_normal_two_complement_corefree
            hG Q hQeight hcore hnormalComplement
        exact hnormalComplementImpossible
      · have hinverter :
            ∀ b : Q, orderOf (b : G) = 4 →
              ∃ q : Q,
                (q : G) * (b : G) * (q : G)⁻¹ = (b : G)⁻¹ :=
          fun b hb =>
            example3_order_four_has_inverter_in_sylow
              Q hQeight hcenterCard b hb
        have hQconj :
            ∀ a b : Q, orderOf (a : G) = 4 →
              orderOf (b : G) = 4 →
              ∃ g : G, g * (a : G) * g⁻¹ = (b : G) :=
          example3_axis_transitive_order_four_conj
            Q htrans hinverter
        intro a b ha hb
        exact example3_all_order_four_conj_of_sylow Q hQconj ha hb
    have hstage_k :
        ∃ dZ eZ fZ epsilonZ : Fin 3 → ℤ,
          (∀ i, d i = (dZ i : ℂ)) ∧
          (∀ i, e i = (eZ i : ℂ)) ∧
          (∀ i, f i = (fZ i : ℂ)) ∧
          (∀ i, epsilon i = (epsilonZ i : ℂ)) ∧
          (∀ i, epsilonZ i = 1 ∨ epsilonZ i = -1) ∧
          ∀ i, 0 < fZ i ∧ 4 ∣ fZ i ∧
            (8 ∣ fZ i →
              (dZ i : ZMod 4) = (epsilonZ i : ZMod 4)) := by
      let dZ : Fin 3 → ℤ :=
        fun i => Classical.choose (hchiInt i 1)
      have hdZ : ∀ i, d i = (dZ i : ℂ) := by
        intro i
        rw [hd i]
        exact Classical.choose_spec (hchiInt i 1)
      let eZ : Fin 3 → ℤ :=
        fun i => Classical.choose (hchiInt i t)
      have heZ : ∀ i, e i = (eZ i : ℂ) := by
        intro i
        rw [he i]
        exact Classical.choose_spec (hchiInt i t)
      let fZ : Fin 3 → ℤ := fun i => dZ i - eZ i
      have hfZ : ∀ i, f i = (fZ i : ℂ) := by
        intro i
        rw [hf i, hdZ i, heZ i]
        simp [fZ]
      let epsilonZ : Fin 3 → ℤ :=
        fun i => if epsilon i = 1 then 1 else -1
      have hepsilonZ :
          ∀ i, epsilon i = (epsilonZ i : ℂ) := by
        intro i
        by_cases hi : epsilon i = 1
        · simp [epsilonZ, hi]
        · have hi' : epsilon i = -1 :=
            (hepsilon_sign i).resolve_left hi
          simp [epsilonZ, hi']
      have hepsilonZ_sign :
          ∀ i, epsilonZ i = 1 ∨ epsilonZ i = -1 := by
        intro i
        by_cases hi : epsilon i = 1
        · exact Or.inl (by simp [epsilonZ, hi])
        · exact Or.inr (by simp [epsilonZ, hi])
      have hchiClass :
          ∀ i, Section1.IsClassFunction (chi i) := by
        intro i
        exact Section1.isCharacter_isClassFunction (chi i)
          (Section1.isCharacter_of_isIrreducibleCharacterOnGroup
            (hchi_irreducible i))
      have hfourValue :
          ∀ i, ∀ y : G, orderOf y = 4 → chi i y = epsilon i := by
        intro i y hy
        obtain ⟨g, hg⟩ := hstage_j hy hxOrder
        calc
          chi i y = chi i (g * y * g⁻¹) :=
            (hchiClass i g y).symm
          _ = chi i (x : G) := by rw [hg]
          _ = epsilon i := hchiX i
      have htwoValue :
          ∀ i, ∀ y : G, orderOf y = 2 → chi i y = chi i t := by
        intro i y hy
        obtain ⟨g, hg⟩ :=
          example3_all_involutions_conj_of_sylow Q
            (example3_sylow_involution_unique Q hQ) hy ht_order
        calc
          chi i y = chi i (g * y * g⁻¹) :=
            (hchiClass i g y).symm
          _ = chi i t := by rw [hg]
      let qeq : Q ≃* QuaternionGroup 2 :=
        Classical.choice
          (example3_generalized_quaternion_eight_equiv_q8 hn hQ hQeight)
      have hdefectData :
          ∀ i, 0 < fZ i ∧ 4 ∣ fZ i := by
        intro i
        rcases hchi_irreducible i with ⟨m, rho, _hirr, hchar⟩
        apply example3_stage_k_positive_four
          (chi i) m rho hchar t (x : G) ht_order hxOrder
            (epsilon i) (hfourValue i) (htwoValue i) (fZ i)
        · calc
            chi i 1 - chi i t = d i - chi i t := by rw [hd i]
            _ = f i := (hfchi i).symm
            _ = (fZ i : ℂ) := hfZ i
        · intro hzero
          apply hf_ne i
          rw [hfZ i, hzero]
          norm_num
      have hdefectPositive : ∀ i, 0 < fZ i :=
        fun i => (hdefectData i).1
      have hdefectFour : ∀ i, 4 ∣ fZ i :=
        fun i => (hdefectData i).2
      have hdegreeModFour :
          ∀ i, 8 ∣ fZ i →
            (dZ i : ZMod 4) = (epsilonZ i : ZMod 4) := by
        intro i hdiv
        rcases hchi_irreducible i with ⟨m, rho, _hirr, hchar⟩
        apply example3_stage_k_degree_mod_four
          (chi i) m rho hchar Q hQeight qeq t (epsilon i)
            (hfourValue i) (htwoValue i)
            (dZ i) (eZ i) (fZ i) (epsilonZ i)
        · exact (hd i).symm.trans (hdZ i)
        · exact (he i).symm.trans (heZ i)
        · exact hepsilonZ i
        · rfl
        · exact hdiv
      exact ⟨dZ, eZ, fZ, epsilonZ, hdZ, heZ, hfZ, hepsilonZ,
        hepsilonZ_sign, fun i =>
          ⟨hdefectPositive i, hdefectFour i, hdegreeModFour i⟩⟩
    obtain ⟨dZ, eZ, fZ, epsilonZ, hdZ, heZ, hfZ, hepsilonZ,
      hepsilonZ_sign, hdefect⟩ := hstage_k
    have hstage_l : False := by
      have hsum_d_three :
          1 + epsilon 0 * d 0 + epsilon 1 * d 1 +
            epsilon 2 * d 2 = 0 := by
        simpa [Fin.sum_univ_three, add_assoc] using hsum_d
      have hsum_f_three :
          epsilon 0 * f 0 + epsilon 1 * f 1 +
            epsilon 2 * f 2 = 0 := by
        simpa [Fin.sum_univ_three, add_assoc] using hsum_f
      have hsum_f_sq_three :
          epsilon 0 * f 0 ^ 2 / d 0 +
            epsilon 1 * f 1 ^ 2 / d 1 +
            epsilon 2 * f 2 ^ 2 / d 2 = 0 := by
        simpa [Fin.sum_univ_three, add_assoc] using hsum_f_sq
      obtain ⟨hsum_dZ, hsum_fZ, hsum_f_sqZ⟩ :=
        example3_cast_three_data epsilon f d epsilonZ fZ dZ
          hepsilonZ hfZ hdZ hd_ne
          hsum_d_three hsum_f_three hsum_f_sq_three
      exact example3_stage_l_final dZ fZ epsilonZ
        hepsilonZ_sign
        (fun i => (hdefect i).1)
        (fun i => (hdefect i).2.1)
        (fun i => (hdefect i).2.2)
        hsum_dZ hsum_fZ hsum_f_sqZ
    exact hstage_l.elim
  have hstage_i :
      2 ∣ Nat.card (Subgroup.center (G ⧸ pPrimeCore 2 G)) := by
    obtain ⟨t0, ht0⟩ :=
      example3_exists_involution_of_generalizedQuaternionSylow Q hQ
    let : Nontrivial G := ⟨⟨t0, 1, ht0.ne_one⟩⟩
    by_cases hsimple : IsSimpleGroup G
    · exact hstage_g hsimple (hstage_h hsimple)
    · exact example3_corefree_nonsimple_target
        Q hQ (by infer_instance) hcore hsimple hind
  exact hstage_i
private lemma cyclic_square_character_inversion_split
    {Y : Type*} [Group Y] [Finite Y]
    (m : ℕ) [NeZero m]
    (e : Multiplicative (ZMod m) ≃* Y)
    (chi0 : Y →* ℂˣ)
    (hchi0_injective : Function.Injective chi0) :
    (m = 4 →
      ∀ y : Y, (((chi0 ^ 2) y⁻¹ : ℂ) = ((chi0 ^ 2) y : ℂ))) ∧
    (4 < m →
      ∃ y : Y, (((chi0 ^ 2) y⁻¹ : ℂ) ≠ ((chi0 ^ 2) y : ℂ))) := by
  constructor
  · intro hm4 y
    let : Fintype Y := Fintype.ofFinite Y
    have hcard : Nat.card Y = m := by
      calc
        Nat.card Y = Nat.card (Multiplicative (ZMod m)) :=
          Nat.card_congr e.symm.toEquiv
        _ = m := by simp
    have hy4 : y ^ 4 = 1 := by
      have hy := pow_card_eq_one (x := y)
      rw [← Nat.card_eq_fintype_card, hcard, hm4] at hy
      exact hy
    apply congrArg Units.val
    change (chi0 y⁻¹) ^ 2 = (chi0 y) ^ 2
    rw [map_inv]
    have ha4 : (chi0 y) ^ 4 = 1 := by
      rw [← map_pow, hy4, map_one]
    calc
      (chi0 y)⁻¹ ^ 2 = ((chi0 y) ^ 4)⁻¹ * (chi0 y) ^ 2 := by group
      _ = (chi0 y) ^ 2 := by rw [ha4]; simp
  · intro hmlarge
    let a : Multiplicative (ZMod m) := Multiplicative.ofAdd (1 : ZMod m)
    refine ⟨e a, ?_⟩
    intro h
    have hu : (chi0 ^ 2) (e a)⁻¹ = (chi0 ^ 2) (e a) := Units.ext h
    change (chi0 (e a)⁻¹) ^ 2 = (chi0 (e a)) ^ 2 at hu
    rw [map_inv] at hu
    have ha4 : (chi0 (e a)) ^ 4 = 1 := by
      calc
        (chi0 (e a)) ^ 4 =
            (chi0 (e a)) ^ 2 * (chi0 (e a)) ^ 2 := by group
        _ = (chi0 (e a))⁻¹ ^ 2 * (chi0 (e a)) ^ 2 := by rw [hu]
        _ = 1 := by group
    have hy4 : (e a) ^ 4 = 1 := hchi0_injective (by
      rw [map_pow, ha4, map_one])
    have ha4' : a ^ 4 = 1 := by
      have he := congrArg e.symm hy4
      simpa only [map_pow, map_one, e.symm_apply_apply] using he
    have hz := congrArg Multiplicative.toAdd ha4'
    have hz' : (4 : ZMod m) = 0 := by simpa [a] using hz
    have hdiv : m ∣ 4 := (ZMod.natCast_eq_zero_iff 4 m).1 hz'
    have hmle : m ≤ 4 := Nat.le_of_dvd (by norm_num : 0 < 4) hdiv
    omega

private lemma example3_stage_c_norm_core
    {H : Type*} [Group H] [Finite H]
    (CH : Subgroup H) [CH.Normal]
    (lambda : Section1.ClassFunction CH)
    (eta : Section1.ClassFunction H)
    (xCard : ℕ)
    (hlambda_irreducible :
      Section1.IsIrreducibleCharacterOnGroup lambda)
    (hlambda_ne_principal :
      lambda ≠ Section1.principalCharacter CH)
    (heta_def : eta =
      Section1.inducedCF CH (Section1.principalCharacter CH - lambda))
    (hHquotCcard : Nat.card (H ⧸ CH) = 2)
    (heta_principal :
      Section1.scalarProduct H eta (Section1.principalCharacter H) = 1)
    (hlambda_rel_large :
      4 < xCard →
        CH.relIndex (Section1.inertiaSubgroup CH lambda) = 1)
    (hlambda_rel_small :
      xCard = 4 →
        CH.relIndex (Section1.inertiaSubgroup CH lambda) = 2)
    (hfour_le : 4 ≤ xCard) :
    Section1.scalarProduct H eta (Section1.principalCharacter H) = 1 ∧
      (Section1.scalarProduct H eta eta = 3 ∨
        Section1.scalarProduct H eta eta = 4) ∧
      (4 < xCard → Section1.scalarProduct H eta eta = 3) ∧
      (xCard = 4 → Section1.scalarProduct H eta eta = 4) := by
  rcases hlambda_irreducible with
    ⟨nLam, lambdaRep, hlambdaRep_irr, hlambdaRep_char⟩
  let oneRep : Representation ℂ CH ℂ := Representation.trivial ℂ CH ℂ
  have honeRep_irr : oneRep.IsIrreducible := by
    exact Theory.Character.trivial_complex_irreducible
  have honeRep_char :
      oneRep.character = Section1.principalCharacter CH := by
    ext c
    simp [oneRep, Representation.character, Section1.principalCharacter]
  let I := Section1.inertiaSubgroup CH lambda
  have hI_lambda_norm :
      Section1.scalarProduct H (Section1.inducedCF CH lambda)
        (Section1.inducedCF CH lambda) = (CH.relIndex I : ℂ) := by
    simpa [I, hlambdaRep_char] using
      Section1.proposition_1_5_b_rep_orbit_relIndex_canonical
        CH lambdaRep hlambdaRep_irr
  have hone_inertia :
      Section1.inertiaSubgroup CH oneRep.character =
        (⊤ : Subgroup H) := by
    apply top_unique
    intro g _hg
    change Section1.conjugateOnNormal CH oneRep.character g =
      oneRep.character
    funext c
    simp [Section1.conjugateOnNormal, oneRep, Representation.character]
  have hI_one_norm :
      Section1.scalarProduct H
        (Section1.inducedCF CH (Section1.principalCharacter CH))
        (Section1.inducedCF CH (Section1.principalCharacter CH)) = 2 := by
    have hnorm :=
      Section1.proposition_1_5_b_rep_orbit_relIndex_canonical
        CH oneRep honeRep_irr
    have hone_inertia_principal :
        Section1.inertiaSubgroup CH (Section1.principalCharacter CH) =
          (⊤ : Subgroup H) := by
      simpa only [← honeRep_char] using hone_inertia
    rw [honeRep_char, hone_inertia_principal] at hnorm
    simpa [Subgroup.relIndex_top_right, Subgroup.index_eq_card,
      hHquotCcard] using hnorm
  have hcross_lambda_one :
      Section1.scalarProduct H (Section1.inducedCF CH lambda)
        (Section1.inducedCF CH (Section1.principalCharacter CH)) = 0 := by
    have hnotConj :
        ∀ i : Section1.conjugateOrbitIndex CH oneRep.character,
          lambda ≠
            Section1.conjugateOrbitConj CH oneRep.character i := by
      intro i
      refine Quotient.inductionOn i ?_
      intro g
      change lambda ≠ Section1.conjugateOnNormal CH oneRep.character g
      intro hEq
      apply hlambda_ne_principal
      calc
        lambda = Section1.conjugateOnNormal CH oneRep.character g := hEq
        _ = Section1.conjugateOnNormal CH
            (Section1.principalCharacter CH) g := by rw [honeRep_char]
        _ = Section1.principalCharacter CH := by
          funext c
          simp [Section1.conjugateOnNormal, Section1.principalCharacter]
    simpa [honeRep_char, hlambdaRep_char] using
      Section1.proposition_1_5_c_nonconjugate_rep_orbit_relIndex_canonical
        CH lambda lambdaRep oneRep hlambdaRep_char hlambdaRep_irr
          honeRep_irr hnotConj
  have hcross_one_lambda :
      Section1.scalarProduct H
        (Section1.inducedCF CH (Section1.principalCharacter CH))
        (Section1.inducedCF CH lambda) = 0 := by
    calc
      _ = star (Section1.scalarProduct H (Section1.inducedCF CH lambda)
          (Section1.inducedCF CH (Section1.principalCharacter CH))) :=
        (Section1.scalarProduct_star_swap _ _).symm
      _ = star 0 := congrArg star hcross_lambda_one
      _ = 0 := by simp
  have hsub : Section1.principalCharacter CH - lambda =
      Section1.principalCharacter CH + (-1 : ℂ) • lambda := by
    ext c
    simp [sub_eq_add_neg]
  have heta_expand : eta =
      Section1.inducedCF CH (Section1.principalCharacter CH) +
        (-1 : ℂ) • Section1.inducedCF CH lambda := by
    rw [heta_def, hsub]
    ext x
    change Section1.inducedClassFunction CH
        (Section1.principalCharacter CH + (-1 : ℂ) • lambda) x = _
    rw [Section1.inducedClassFunction_add,
      Section1.inducedClassFunction_smul]
  have scalarProduct_add_right
      (phi psi₁ psi₂ : Section1.ClassFunction H) :
      Section1.scalarProduct H phi (psi₁ + psi₂) =
        Section1.scalarProduct H phi psi₁ +
          Section1.scalarProduct H phi psi₂ := by
    simp [Section1.scalarProduct, mul_add, Finset.sum_add_distrib]
  have heta_norm_of_rel (r : ℕ) (hr : CH.relIndex I = r) :
      Section1.scalarProduct H eta eta = 2 + r := by
    rw [heta_expand, Section1.scalarProduct_add_left,
      scalarProduct_add_right, scalarProduct_add_right,
      Section1.scalarProduct_smul_right,
      Section1.scalarProduct_smul_left,
      Section1.scalarProduct_smul_right,
      Section1.scalarProduct_smul_left,
      hI_one_norm, hcross_one_lambda, hcross_lambda_one,
      hI_lambda_norm, hr]
    norm_num
  have hnorm_large (hlarge : 4 < xCard) :
      Section1.scalarProduct H eta eta = 3 := by
    convert heta_norm_of_rel 1 (hlambda_rel_large hlarge) using 1
    norm_num
  have hnorm_small (hfour : xCard = 4) :
      Section1.scalarProduct H eta eta = 4 := by
    convert heta_norm_of_rel 2 (hlambda_rel_small hfour) using 1
    norm_num
  have hnorm_cases : Section1.scalarProduct H eta eta = 3 ∨
      Section1.scalarProduct H eta eta = 4 := by
    rcases eq_or_lt_of_le hfour_le with hfour | hlarge
    · exact Or.inr (hnorm_small hfour.symm)
    · exact Or.inl (hnorm_large hlarge)
  exact ⟨heta_principal, hnorm_cases, hnorm_large, hnorm_small⟩

set_option maxHeartbeats 500000 in
set_option backward.isDefEq.respectTransparency false in
private theorem suzuki_example3_corefree_setup
    {G : Type u} [Group G] [Finite G]
    (Q : Sylow 2 G) {n : ℕ} (hn : 3 ≤ n)
    (hQ : Nonempty (Q ≃* QuaternionGroup (2 ^ (n - 2))))
    (hcore : pPrimeCore 2 G = ⊥)
    (hind : ∀ (M : Type u) [Group M] [Finite M],
      Nat.card M < Nat.card G →
      ∀ (S : Sylow 2 M) {m : ℕ}, 3 ≤ m →
        Nonempty (S ≃* QuaternionGroup (2 ^ (m - 2))) →
        2 ∣ Nat.card (Subgroup.center (M ⧸ pPrimeCore 2 M))) :
    2 ∣ Nat.card (Subgroup.center (G ⧸ pPrimeCore 2 G)) := by
  classical
  let e : Q ≃* QuaternionGroup (2 ^ (n - 2)) := Classical.choice hQ
  obtain ⟨XQ, UQ, TQ, hXQcyclic, hUQnormal, hUQ_le_XQ, hTQ_le_UQ,
      hUQcard, hTQcard, hQcard, hcenterQ, hOrderFourUniqueXQ, hConjInvXQ,
      hUniqueInvolutionQ⟩ :=
    generalizedQuaternion_source_subgroups hn e
  let X : Subgroup G := XQ.map (Q : Subgroup G).subtype
  let U : Subgroup G := UQ.map (Q : Subgroup G).subtype
  let T : Subgroup G := TQ.map (Q : Subgroup G).subtype
  let C : Subgroup G := Subgroup.centralizer (U : Set G)
  let H : Subgroup G := Subgroup.normalizer (U : Set G)
  have hXcard_transport : Nat.card X = Nat.card XQ := by
    exact (Nat.card_congr
      (Subgroup.equivMapOfInjective XQ (Q : Subgroup G).subtype
        (Q : Subgroup G).subtype_injective).toEquiv).symm
  have hUcard : Nat.card U = 4 := by
    calc
      Nat.card U = Nat.card UQ :=
        (Nat.card_congr
          (Subgroup.equivMapOfInjective UQ (Q : Subgroup G).subtype
            (Q : Subgroup G).subtype_injective).toEquiv).symm
      _ = 4 := hUQcard
  have hTcard : Nat.card T = 2 := by
    calc
      Nat.card T = Nat.card TQ :=
        (Nat.card_congr
          (Subgroup.equivMapOfInjective TQ (Q : Subgroup G).subtype
            (Q : Subgroup G).subtype_injective).toEquiv).symm
      _ = 2 := hTQcard
  have hU_le_X : U ≤ X := Subgroup.map_mono hUQ_le_XQ
  have hT_le_U : T ≤ U := Subgroup.map_mono hTQ_le_UQ
  have hQcard_X : Nat.card Q = 2 * Nat.card X := by
    rw [hXcard_transport]
    exact hQcard
  have hXcyclic : IsCyclic X :=
    isCyclic_of_surjective ((Q : Subgroup G).subtype.subgroupMap XQ)
      ((Q : Subgroup G).subtype.subgroupMap_surjective XQ)
  have hX_le_Q : X ≤ (Q : Subgroup G) := by
    rintro x ⟨xQ, _hxQ, rfl⟩
    exact xQ.property
  have hOrderFourUniqueX :
      ∀ V : Subgroup G, V ≤ X → Nat.card V = 4 → V = U := by
    intro V hV_le_X hVcard
    have hV_le_Q : V ≤ (Q : Subgroup G) := hV_le_X.trans hX_le_Q
    let VQ : Subgroup Q := V.subgroupOf (Q : Subgroup G)
    have hVQ_le_XQ : VQ ≤ XQ := by
      intro v hv
      have hvX : (v : G) ∈ X := hV_le_X hv
      rcases hvX with ⟨x, hx, hxv⟩
      have hvx : v = x := Subtype.ext hxv.symm
      simpa [hvx] using hx
    have hVQcard : Nat.card VQ = 4 := by
      calc
        Nat.card VQ = Nat.card V :=
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe hV_le_Q).toEquiv
        _ = 4 := hVcard
    have hVQeq : VQ = UQ := hOrderFourUniqueXQ VQ hVQ_le_XQ hVQcard
    calc
      V = VQ.map (Q : Subgroup G).subtype :=
        (Subgroup.map_subgroupOf_eq_of_le hV_le_Q).symm
      _ = UQ.map (Q : Subgroup G).subtype := congrArg
        (fun W : Subgroup Q => W.map (Q : Subgroup G).subtype) hVQeq
      _ = U := rfl
  have hUniqueInvolutionX :
      ∀ x : G, x ∈ X → orderOf x = 2 → x ∈ T := by
    intro x hxX hxorder
    let xQ : Q := ⟨x, hX_le_Q hxX⟩
    have hxQorder : orderOf xQ = 2 := by
      change orderOf (⟨x, hX_le_Q hxX⟩ : (Q : Subgroup G)) = 2
      rw [Subgroup.orderOf_mk, hxorder]
    have hxQT : xQ ∈ TQ := hUniqueInvolutionQ xQ hxQorder
    exact ⟨xQ, hxQT, rfl⟩
  have hX_le_C : X ≤ C := by
    let : IsMulCommutative XQ := hXQcyclic.isMulCommutative
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rcases hx with ⟨xQ, hxQ, rfl⟩
    rcases hy with ⟨yQ, hyQ, rfl⟩
    exact congrArg (fun z : Q => (z : G))
      (setLike_mul_comm (hUQ_le_XQ hyQ) hxQ)
  have hQ_le_H : (Q : Subgroup G) ≤ H := by
    have hnormalizerQ : Subgroup.normalizer (UQ : Set Q) = ⊤ :=
      Subgroup.normalizer_eq_top_iff.mpr hUQnormal
    have hmap_normalizer :
        (Subgroup.normalizer (UQ : Set Q)).map (Q : Subgroup G).subtype ≤
          Subgroup.normalizer
            (UQ.map (Q : Subgroup G).subtype : Set G) :=
      Subgroup.le_normalizer_map (Q : Subgroup G).subtype
    intro q hq
    apply hmap_normalizer
    rw [hnormalizerQ]
    exact ⟨⟨q, hq⟩, by simp, rfl⟩
  have hQ_not_le_C : ¬ (Q : Subgroup G) ≤ C := by
    intro hQ_le_C
    have hUQ_le_center : UQ ≤ Subgroup.center Q := by
      intro u hu
      rw [Subgroup.mem_center_iff]
      intro q
      apply Subtype.ext
      have hqC : (q : G) ∈ C := hQ_le_C q.property
      exact ((Subgroup.mem_centralizer_iff.mp hqC) (u : G)
        ⟨u, hu, rfl⟩).symm
    have hUQ_le_TQ : UQ ≤ TQ := by
      rw [← hcenterQ]
      exact hUQ_le_center
    have hcard_le : Nat.card UQ ≤ Nat.card TQ :=
      Nat.card_le_card_of_injective
        (fun u : UQ => (⟨u, hUQ_le_TQ u.property⟩ : TQ))
        (fun _ _ h => Subtype.ext (congrArg (fun z : TQ => (z : Q)) h))
    rw [hUQcard, hTQcard] at hcard_le
    omega
  let XC : Subgroup C := X.subgroupOf C
  have hXQp : IsPGroup 2 XQ := Q.isPGroup'.to_subgroup XQ
  have hXp : IsPGroup 2 X :=
    hXQp.of_equiv
      (Subgroup.equivMapOfInjective XQ (Q : Subgroup G).subtype
        (Q : Subgroup G).subtype_injective)
  have hXCp : IsPGroup 2 XC :=
    hXp.of_equiv (Subgroup.subgroupOfEquivOfLe hX_le_C).symm
  obtain ⟨S, hXC_le_S⟩ := hXCp.exists_le_sylow
  obtain ⟨R, hRcomap⟩ := Sylow.exists_comap_subtype_eq S
  let SG : Subgroup G := (S : Subgroup C).map C.subtype
  have hSG_le_R : SG ≤ (R : Subgroup G) := by
    change (S : Subgroup C).map C.subtype ≤ (R : Subgroup G)
    rw [Subgroup.map_le_iff_le_comap, hRcomap]
  have hXCmap : XC.map C.subtype = X :=
    Subgroup.map_subgroupOf_eq_of_le hX_le_C
  have hX_le_SG : X ≤ SG := by
    rw [← hXCmap]
    exact Subgroup.map_mono hXC_le_S
  have hX_le_R : X ≤ (R : Subgroup G) := hX_le_SG.trans hSG_le_R
  have hRcardQ : Nat.card R = Nat.card Q :=
    Nat.card_congr (R.equiv Q).toEquiv
  have hXsubcard : Nat.card (X.subgroupOf (R : Subgroup G)) = Nat.card X :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hX_le_R).toEquiv
  have hXrelR : X.relIndex (R : Subgroup G) = 2 := by
    have hmul := (X.subgroupOf (R : Subgroup G)).card_mul_index
    change Nat.card (X.subgroupOf (R : Subgroup G)) *
        X.relIndex (R : Subgroup G) = Nat.card R at hmul
    rw [hXsubcard, hRcardQ, hQcard_X, mul_comm 2] at hmul
    exact Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := X)) hmul
  have hSG_eq_X_or_R : SG = X ∨ SG = (R : Subgroup G) := by
    by_cases hSGX : SG = X
    · exact Or.inl hSGX
    · right
      have hprod := Subgroup.relIndex_mul_relIndex
        X SG (R : Subgroup G) hX_le_SG hSG_le_R
      rw [hXrelR] at hprod
      have hrel_ne_one : X.relIndex SG ≠ 1 := by
        intro hrel
        have hSG_le_X : SG ≤ X := Subgroup.relIndex_eq_one.mp hrel
        exact hSGX (le_antisymm hSG_le_X hX_le_SG)
      have hrel_dvd : X.relIndex SG ∣ 2 :=
        ⟨SG.relIndex (R : Subgroup G), hprod.symm⟩
      have hrel_eq_two : X.relIndex SG = 2 := by
        rcases (Nat.dvd_prime Nat.prime_two).mp hrel_dvd with hrel | hrel
        · exact False.elim (hrel_ne_one hrel)
        · exact hrel
      have hSGrelR : SG.relIndex (R : Subgroup G) = 1 := by
        rw [hrel_eq_two] at hprod
        omega
      exact le_antisymm hSG_le_R (Subgroup.relIndex_eq_one.mp hSGrelR)
  have hSG_le_C : SG ≤ C := by
    rintro g ⟨s, _hs, rfl⟩
    exact s.property
  have hSG_eq_X : SG = X := by
    rcases hSG_eq_X_or_R with h | h
    · exact h
    · exfalso
      have hR_le_C : (R : Subgroup G) ≤ C := by simpa [h] using hSG_le_C
      let UR : Subgroup R := U.subgroupOf (R : Subgroup G)
      have hU_le_R : U ≤ (R : Subgroup G) := hU_le_X.trans hX_le_R
      have hURcard : Nat.card UR = 4 := by
        calc
          Nat.card UR = Nat.card U :=
            Nat.card_congr (Subgroup.subgroupOfEquivOfLe hU_le_R).toEquiv
          _ = 4 := hUcard
      have hUR_le_center : UR ≤ Subgroup.center R := by
        intro u hu
        rw [Subgroup.mem_center_iff]
        intro r
        apply Subtype.ext
        have hrC : (r : G) ∈ C := hR_le_C r.property
        have huU : (u : G) ∈ U := hu
        exact ((Subgroup.mem_centralizer_iff.mp hrC) (u : G) huU).symm
      have hcenterRcard_le : Nat.card UR ≤ Nat.card (Subgroup.center R) :=
        Nat.card_le_card_of_injective
          (fun u : UR => (⟨u, hUR_le_center u.property⟩ : Subgroup.center R))
          (fun _ _ hu => Subtype.ext
            (congrArg (fun z : Subgroup.center R => (z : R)) hu))
      have hcenterQcard : Nat.card (Subgroup.center Q) = 2 := by
        rw [hcenterQ, hTQcard]
      have hcenterRcard : Nat.card (Subgroup.center R) = 2 := by
        calc
          Nat.card (Subgroup.center R) = Nat.card (Subgroup.center Q) :=
            Nat.card_congr (Subgroup.centerCongr (R.equiv Q)).toEquiv
          _ = 2 := hcenterQcard
      rw [hURcard, hcenterRcard] at hcenterRcard_le
      omega
  have hS_eq_XC : (S : Subgroup C) = XC := by
    apply Subgroup.map_subtype_inj.mp
    calc
      (S : Subgroup C).map C.subtype = SG := rfl
      _ = X := hSG_eq_X
      _ = XC.map C.subtype := hXCmap.symm
  have hOrderFourUniqueC :
      ∀ V : Subgroup G, V ≤ C → Nat.card V = 4 → V = U := by
    intro V hV_le_C hVcard
    let VC : Subgroup C := V.subgroupOf C
    have hVCcard : Nat.card VC = 4 := by
      calc
        Nat.card VC = Nat.card V :=
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe hV_le_C).toEquiv
        _ = 4 := hVcard
    have hVCp : IsPGroup 2 VC := by
      apply IsPGroup.of_card (n := 2)
      norm_num [hVCcard]
    obtain ⟨R, hVC_le_R⟩ := hVCp.exists_le_sylow
    obtain ⟨c, hc⟩ := MulAction.exists_smul_eq C R S
    have hcmap : (R : Subgroup C).map (MulAut.conj c).toMonoidHom =
        (S : Subgroup C) := by
      have hcsub := congrArg (fun P : Sylow 2 C => (P : Subgroup C)) hc
      change (R : Subgroup C).map (MulAut.conj c).toMonoidHom =
        (S : Subgroup C) at hcsub
      exact hcsub
    let cG : G := c
    let autG : G ≃* G := MulAut.conj cG
    let W : Subgroup G := V.map autG.toMonoidHom
    have hW_le_X : W ≤ X := by
      rintro w ⟨v, hv, rfl⟩
      let vC : C := ⟨v, hV_le_C hv⟩
      have hvR : vC ∈ (R : Subgroup C) := hVC_le_R hv
      have hcvS : (MulAut.conj c) vC ∈ (S : Subgroup C) := by
        rw [← hcmap]
        exact Subgroup.mem_map_of_mem (MulAut.conj c).toMonoidHom hvR
      have hcvXC : (MulAut.conj c) vC ∈ XC := by
        rw [← hS_eq_XC]
        exact hcvS
      exact hcvXC
    have hWcard : Nat.card W = 4 := by
      calc
        Nat.card W = Nat.card V :=
          Subgroup.card_map_of_injective autG.injective
        _ = 4 := hVcard
    have hWeq : W = U := hOrderFourUniqueX W hW_le_X hWcard
    have hUfixed : U.map autG.toMonoidHom = U := by
      apply Subgroup.eq_of_le_of_card_ge
      · rintro z ⟨u, hu, rfl⟩
        have hcomm : u * (c : G) = (c : G) * u :=
          (Subgroup.mem_centralizer_iff.mp c.property) u hu
        have hconj : (c : G) * u * (c : G)⁻¹ = u := by
          calc
            (c : G) * u * (c : G)⁻¹ = u * (c : G) * (c : G)⁻¹ := by
              rw [hcomm]
            _ = u := by simp
        simpa [autG, cG, hconj] using hu
      · rw [Subgroup.card_map_of_injective (K := U) (f := autG.toMonoidHom) autG.injective]
    apply (Subgroup.map_injective (f := autG.toMonoidHom) autG.injective)
    calc
      V.map autG.toMonoidHom = W := rfl
      _ = U := hWeq
      _ = U.map autG.toMonoidHom := hUfixed.symm
  have hXCcyclic : IsCyclic XC :=
    isCyclic_of_surjective
      (Subgroup.subgroupOfEquivOfLe hX_le_C).symm
      (Subgroup.subgroupOfEquivOfLe hX_le_C).symm.surjective
  have hScyclic : IsCyclic S := by
    rw [hS_eq_XC]
    exact hXCcyclic
  have hU_le_C : U ≤ C := hU_le_X.trans hX_le_C
  have hUcard_dvd_C : Nat.card U ∣ Nat.card C :=
    Subgroup.card_dvd_of_le hU_le_C
  have htwo_dvd_C : 2 ∣ Nat.card C := by
    rw [hUcard] at hUcard_dvd_C
    exact dvd_trans (by norm_num : 2 ∣ 4) hUcard_dvd_C
  have hminFacC : (Nat.card C).minFac = 2 :=
    (Nat.minFac_eq_two_iff (Nat.card C)).2 htwo_dvd_C
  have hcompC : HasNormalPComplement 2 C :=
    V.suzuki_ch5_theorem_2_10_corollary_1 S hminFacC hScyclic
  let N : Subgroup C := pPrimeCore 2 C
  have hNnormal : N.Normal := by
    dsimp [N]
    infer_instance
  have hNodd : Nat.Coprime 2 (Nat.card N) := by
    dsimp [N]
    exact pPrimeCore_coprime_card (p := 2) (G := C)
  have hCquotp : IsPGroup 2 (C ⧸ N) := by
    dsimp [N]
    exact isPGroup_quotient_pPrimeCore_of_hasNormalPComplement
      (p := 2) C hcompC
  have hC_le_H : C ≤ H := by
    simpa [C, H] using centralizer_le_normalizer U
  let CH : Subgroup H := C.subgroupOf H
  have hCHnormal : CH.Normal := by
    dsimp [CH, C, H]
    rw [← U.normalizerMonoidHom_ker]
    infer_instance
  let : CH.Normal := hCHnormal
  let phi : H →* MulAut U := by
    simpa [H] using U.normalizerMonoidHom
  have hphi_ker : phi.ker = CH := by
    simpa [phi, CH, C, H] using U.normalizerMonoidHom_ker
  let : IsCyclic X := hXcyclic
  have hUcyclic : IsCyclic U := Subgroup.isCyclic_of_le hU_le_X
  let : IsCyclic U := hUcyclic
  have hAutUcard : Nat.card (MulAut U) = 2 := by
    rw [IsCyclic.card_mulAut U, hUcard]
    decide
  have hquotRange : (H ⧸ CH) ≃* MonoidHom.range phi := by
    exact (QuotientGroup.quotientMulEquivOfEq hphi_ker.symm).trans
      (QuotientGroup.quotientKerEquivRange phi)
  obtain ⟨q, hqQ, hqC⟩ := Set.not_subset.mp hQ_not_le_C
  let qH : H := ⟨q, hQ_le_H hqQ⟩
  have hqH_not_CH : qH ∉ CH := by
    exact hqC
  have hphiq_ne_one : phi qH ≠ 1 := by
    intro hphiq
    have hqker : qH ∈ phi.ker := by
      simpa using hphiq
    rw [hphi_ker] at hqker
    exact hqH_not_CH hqker
  let oneRange : MonoidHom.range phi := ⟨1, ⟨1, by simp⟩⟩
  let qRange : MonoidHom.range phi := ⟨phi qH, ⟨qH, rfl⟩⟩
  have honeRange_ne_qRange : oneRange ≠ qRange := by
    intro heq
    apply hphiq_ne_one
    exact (congrArg Subtype.val heq).symm
  let : Nontrivial (MonoidHom.range phi) :=
    ⟨⟨oneRange, qRange, honeRange_ne_qRange⟩⟩
  have hrange_card_le : Nat.card (MonoidHom.range phi) ≤
      Nat.card (MulAut U) :=
    Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
  have hrange_card : Nat.card (MonoidHom.range phi) = 2 := by
    have hrange_one_lt : 1 < Nat.card (MonoidHom.range phi) :=
      Finite.one_lt_card
    rw [hAutUcard] at hrange_card_le
    omega
  have hHquotCcard : Nat.card (H ⧸ CH) = 2 := by
    calc
      Nat.card (H ⧸ CH) = Nat.card (MonoidHom.range phi) :=
        Nat.card_congr hquotRange.toEquiv
      _ = 2 := hrange_card
  let eCH : CH ≃* C := Subgroup.subgroupOfEquivOfLe hC_le_H
  let : N.Characteristic := by
    dsimp [N]
    exact pPrimeCore_characteristic (p := 2) (G := C)
  let NCH : Subgroup CH := N.map eCH.symm
  have hNCHcharacteristic : NCH.Characteristic := by
    dsimp [NCH]
    rw [Subgroup.characteristic_iff_map_le]
    intro aut x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
    rcases Subgroup.mem_map.mp hy with ⟨z, hz, rfl⟩
    let psi : C ≃* C := (eCH.symm.trans aut).trans eCH
    have hpsiN : N.map psi.toMonoidHom ≤ N :=
      (Subgroup.characteristic_iff_map_le.mp
        (inferInstance : N.Characteristic)) psi
    have hpsiz : psi z ∈ N :=
      hpsiN (Subgroup.mem_map_of_mem psi.toMonoidHom hz)
    exact Subgroup.mem_map.mpr ⟨psi z, hpsiz, by simp [psi]⟩
  let : NCH.Characteristic := hNCHcharacteristic
  let NH : Subgroup H := NCH.map CH.subtype
  have hNHnormal : NH.Normal := by
    dsimp [NH]
    infer_instance
  let : NH.Normal := hNHnormal
  have hNH_iff (c : C) :
      (⟨(c : G), hC_le_H c.property⟩ : H) ∈ NH ↔ c ∈ N := by
    constructor
    · rintro ⟨x, hxNCH, hxc⟩
      rcases hxNCH with ⟨a, haN, hax⟩
      have haxG0 : (((eCH.symm a : CH) : H) : G) = ((x : H) : G) :=
        congrArg (fun z : CH => ((z : H) : G)) hax
      have hcast : (((eCH.symm a : CH) : H) : G) = (a : G) := rfl
      have haxG : (a : G) = ((x : H) : G) :=
        hcast.symm.trans haxG0
      have hxcG : ((x : H) : G) = (c : G) :=
        congrArg (fun h : H => (h : G)) hxc
      have hacG : (a : G) = (c : G) := haxG.trans hxcG
      have hac : a = c := (Subtype.ext_iff).2 hacG
      simpa [hac] using haN
    · intro hc
      refine ⟨eCH.symm c, ?_, ?_⟩
      · exact ⟨c, hc, rfl⟩
      · rfl
  have hNCHcard : Nat.card NCH = Nat.card N := by
    dsimp [NCH]
    exact Subgroup.card_map_of_injective eCH.symm.injective
  have hNHcard : Nat.card NH = Nat.card N := by
    calc
      Nat.card NH = Nat.card NCH := by
        dsimp [NH]
        exact Subgroup.card_map_of_injective CH.subtype_injective
      _ = Nat.card N := hNCHcard
  have hNHodd : Nat.Coprime 2 (Nat.card NH) := by
    rw [hNHcard]
    exact hNodd
  have hSNcoprime : Nat.Coprime (Nat.card S) (Nat.card N) := by
    rcases S.isPGroup'.exists_card_eq with ⟨a, ha⟩
    rw [ha]
    exact hNodd.pow_left a
  have hSNdisjoint : Disjoint (S : Subgroup C) N :=
    Subgroup.disjoint_of_coprime_natCard hSNcoprime
  let qN : C →* C ⧸ N := QuotientGroup.mk' N
  let SQ : Sylow 2 (C ⧸ N) :=
    S.mapSurjective (QuotientGroup.mk'_surjective N)
  have hSQtop : (SQ : Subgroup (C ⧸ N)) = ⊤ := by
    apply le_antisymm le_top
    have htopP : IsPGroup 2 (⊤ : Subgroup (C ⧸ N)) := by
      exact hCquotp.of_equiv Subgroup.topEquiv.symm
    have heq : (⊤ : Subgroup (C ⧸ N)) = (SQ : Subgroup (C ⧸ N)) :=
      SQ.3 htopP le_top
    exact heq.le
  have hSmap_top : (S : Subgroup C).map qN = ⊤ := by
    exact hSQtop
  let fSN : S →* C ⧸ N := qN.comp (S : Subgroup C).subtype
  have hfSNker : fSN.ker = ⊥ := by
    change ((QuotientGroup.mk' N).comp (S : Subgroup C).subtype).ker = ⊥
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk',
      Subgroup.comap_subtype, Subgroup.subgroupOf_eq_bot]
    exact hSNdisjoint.symm
  have hfSNinjective : Function.Injective fSN :=
    (MonoidHom.ker_eq_bot_iff fSN).mp hfSNker
  have hfSNsurjective : Function.Surjective fSN := by
    intro y
    have hy : y ∈ (S : Subgroup C).map qN := by
      rw [hSmap_top]
      exact Subgroup.mem_top y
    rcases hy with ⟨s, hs, rfl⟩
    exact ⟨⟨s, hs⟩, by simp [fSN, qN]⟩
  let eSN : S ≃* C ⧸ N :=
    MulEquiv.ofBijective fSN ⟨hfSNinjective, hfSNsurjective⟩
  have hCquotNcard : Nat.card (C ⧸ N) = Nat.card S :=
    Nat.card_congr eSN.symm.toEquiv
  have hCHcard : Nat.card CH = Nat.card C :=
    Nat.card_congr eCH.toEquiv
  have hScardX : Nat.card S = Nat.card X := by
    calc
      Nat.card S = Nat.card XC := by rw [hS_eq_XC]
      _ = Nat.card X :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hX_le_C).toEquiv
  let QH : Subgroup H := (Q : Subgroup G).subgroupOf H
  have hQHcard : Nat.card QH = Nat.card Q :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQ_le_H).toEquiv
  have hQHcard_S : Nat.card QH = 2 * Nat.card S := by
    rw [hQHcard, hQcard_X, hScardX]
  have hHcard_QH_NH : Nat.card H = Nat.card QH * Nat.card NH := by
    calc
      Nat.card H = Nat.card (H ⧸ CH) * Nat.card CH :=
        Subgroup.card_eq_card_quotient_mul_card_subgroup CH
      _ = 2 * Nat.card C := by rw [hHquotCcard, hCHcard]
      _ = 2 * (Nat.card (C ⧸ N) * Nat.card N) := by
        rw [← Subgroup.card_eq_card_quotient_mul_card_subgroup N]
      _ = (2 * Nat.card S) * Nat.card NH := by
        rw [hCquotNcard, hNHcard]
        ring
      _ = Nat.card QH * Nat.card NH := by rw [hQHcard_S]
  have hHquotNHcard : Nat.card (H ⧸ NH) = Nat.card QH := by
    apply Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := NH))
    calc
      Nat.card (H ⧸ NH) * Nat.card NH = Nat.card H :=
        (Subgroup.card_eq_card_quotient_mul_card_subgroup NH).symm
      _ = Nat.card QH * Nat.card NH := hHcard_QH_NH
  have hQHp : IsPGroup 2 QH :=
    Q.isPGroup'.of_equiv
      (Subgroup.subgroupOfEquivOfLe hQ_le_H).symm
  have hQHNHcoprime : Nat.Coprime (Nat.card QH) (Nat.card NH) := by
    rcases hQHp.exists_card_eq with ⟨a, ha⟩
    rw [ha]
    exact hNHodd.pow_left a
  have hQHNHdisjoint : Disjoint QH NH :=
    Subgroup.disjoint_of_coprime_natCard hQHNHcoprime
  let qNH : H →* H ⧸ NH := QuotientGroup.mk' NH
  let fQH : QH →* H ⧸ NH := qNH.comp QH.subtype
  have hfQHker : fQH.ker = ⊥ := by
    change ((QuotientGroup.mk' NH).comp QH.subtype).ker = ⊥
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk',
      Subgroup.comap_subtype, Subgroup.subgroupOf_eq_bot]
    exact hQHNHdisjoint.symm
  have hfQHinjective : Function.Injective fQH :=
    (MonoidHom.ker_eq_bot_iff fQH).mp hfQHker
  let : Fintype QH := Fintype.ofFinite QH
  let : Fintype (H ⧸ NH) := Fintype.ofFinite (H ⧸ NH)
  have hfQHbijective : Function.Bijective fQH :=
    (Fintype.bijective_iff_injective_and_card fQH).2
      ⟨hfQHinjective, by
        simpa [Nat.card_eq_fintype_card] using hHquotNHcard.symm⟩
  let eQHquot : QH ≃* H ⧸ NH :=
    MulEquiv.ofBijective fQH hfQHbijective
  have hHquot_equiv_Q : Nonempty ((H ⧸ NH) ≃* Q) := by
    exact ⟨eQHquot.symm.trans (Subgroup.subgroupOfEquivOfLe hQ_le_H)⟩
  have hHquotp : IsPGroup 2 (H ⧸ NH) :=
    Q.isPGroup'.of_equiv
      (Classical.choice hHquot_equiv_Q).symm
  let OH : Subgroup H := pPrimeCore 2 H
  have hNH_le_OH : NH ≤ OH := by
    exact le_sSup ⟨hNHnormal, hNHodd⟩
  have hOHnormal : OH.Normal := by
    dsimp [OH]
    infer_instance
  have hOHodd : Nat.Coprime 2 (Nat.card OH) := by
    dsimp [OH]
    exact pPrimeCore_coprime_card (p := 2) (G := H)
  let OHbar : Subgroup (H ⧸ NH) := OH.map qNH
  have hOHbarP : IsPGroup 2 OHbar := hHquotp.to_subgroup OHbar
  have hOHbarOdd : Nat.Coprime 2 (Nat.card OHbar) := by
    exact hOHodd.of_dvd_right (OH.card_map_dvd qNH)
  have hOHbarCard : Nat.card OHbar = 1 := by
    rcases hOHbarP.exists_card_eq with ⟨a, ha⟩
    have ha0 : a = 0 := by
      by_contra ha_ne
      have ha_pos : 0 < a := Nat.pos_of_ne_zero ha_ne
      have hcop22 : Nat.Coprime 2 2 :=
        (Nat.coprime_pow_right_iff ha_pos 2 2).mp (by
          rw [← ha]
          exact hOHbarOdd)
      norm_num at hcop22
    rw [ha, ha0, pow_zero]
  have hOHbar_bot : OHbar = ⊥ := Subgroup.card_eq_one.mp hOHbarCard
  have hOH_le_NH : OH ≤ NH := by
    intro x hx
    have hxbar : qNH x ∈ OHbar :=
      Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
    rw [hOHbar_bot] at hxbar
    have hxker : x ∈ qNH.ker := by
      simpa using hxbar
    have hqNHker : qNH.ker = NH := by
      dsimp [qNH]
      exact QuotientGroup.ker_mk' (G := H) (N := NH)
    rw [hqNHker] at hxker
    exact hxker
  have hNH_eq_oddCore : NH = pPrimeCore 2 H := by
    change NH = OH
    exact le_antisymm hNH_le_OH hOH_le_NH
  let K : Set G := {k : G | k ∈ C ∧ 4 ∣ orderOf k}
  have hK_generator : ∀ k : G, k ∈ K →
      Subgroup.zpowers (k ^ (orderOf k / 4)) = U := by
    intro k hk
    have hkC : k ∈ C := hk.1
    have hpowC : k ^ (orderOf k / 4) ∈ C :=
      C.pow_mem hkC (orderOf k / 4)
    have hzp_le_C : Subgroup.zpowers (k ^ (orderOf k / 4)) ≤ C :=
      Subgroup.zpowers_le.mpr hpowC
    have horder : orderOf (k ^ (orderOf k / 4)) = 4 :=
      orderOf_pow_orderOf_div (orderOf_pos k).ne' hk.2
    have hzpcard : Nat.card (Subgroup.zpowers (k ^ (orderOf k / 4))) = 4 := by
      rw [Nat.card_zpowers, horder]
    exact hOrderFourUniqueC _ hzp_le_C hzpcard
  have hKH : K ⊆ H := by
    intro k hk
    exact hC_le_H hk.1
  have hH_le_normC : H ≤ Subgroup.normalizer (C : Set G) :=
    Subgroup.le_normalizer_of_normal_subgroupOf hC_le_H
  have hHnormK : H ≤ Subgroup.normalizer K := by
    intro h hh
    have hhNormC := hH_le_normC hh
    rw [Subgroup.mem_normalizer_iff] at hhNormC
    change ∀ k : G, k ∈ K ↔ h * k * h⁻¹ ∈ K
    intro k
    have hord : orderOf (h * k * h⁻¹) = orderOf k := by
      simpa using (MulAut.conj (h : G)).orderOf_eq k
    constructor
    · intro hk
      refine ⟨(hhNormC k).1 hk.1, ?_⟩
      rw [hord]
      exact hk.2
    · intro hk
      have hkorder := hk.2
      rw [hord] at hkorder
      exact ⟨(hhNormC k).2 hk.1, hkorder⟩
  have hKnontrivial : ∃ k : G, k ∈ K ∧ k ≠ 1 := by
    obtain ⟨u, huorder⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := U)
    have huorderG : orderOf (u : G) = 4 := by
      rw [Subgroup.orderOf_coe, huorder, hUcard]
    refine ⟨u, ⟨hU_le_C u.property, by rw [huorderG]⟩, ?_⟩
    intro huone
    have : orderOf (u : G) = 1 := by rw [huone, orderOf_one]
    omega
  have hKintersection : ∀ g : G, g ∉ H →
      (((fun x : G => g * x * g⁻¹) '' K) ∩ K) ⊆ ({1} : Set G) := by
    intro g hgH z hz
    rcases hz with ⟨⟨k, hkK, rfl⟩, hgkK⟩
    let cg : G ≃* G := MulAut.conj g
    have hcgkK : cg k ∈ K := by
      simpa [cg] using hgkK
    have hmapU : U.map cg.toMonoidHom = U := by
      calc
        U.map cg.toMonoidHom =
            (Subgroup.zpowers (k ^ (orderOf k / 4))).map cg.toMonoidHom := by
              rw [hK_generator k hkK]
        _ = Subgroup.zpowers (cg (k ^ (orderOf k / 4))) :=
          MonoidHom.map_zpowers cg.toMonoidHom _
        _ = Subgroup.zpowers ((cg k) ^ (orderOf k / 4)) := by
          rw [map_pow]
        _ = Subgroup.zpowers ((cg k) ^ (orderOf (cg k) / 4)) := by
          rw [cg.orderOf_eq k]
        _ = U := hK_generator (cg k) hcgkK
    have hgNormU : g ∈ Subgroup.normalizer (U : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · intro hx
        have hmem : cg x ∈ U.map cg.toMonoidHom :=
          Subgroup.mem_map_of_mem cg.toMonoidHom hx
        rw [hmapU] at hmem
        simpa [cg] using hmem
      · intro hx
        have hmem : cg x ∈ U.map cg.toMonoidHom := by
          rw [hmapU]
          simpa [cg] using hx
        rcases hmem with ⟨y, hy, hyx⟩
        have hyx' : y = x := cg.injective hyx
        simpa [hyx'] using hy
    have hgH' : g ∈ H := by
      simpa [H] using hgNormU
    exact False.elim (hgH hgH')
  have hKTI : IsTISubsetRelative H K :=
    (suzuki_ch6_proposition_2_8 H K hKH hHnormK hKnontrivial).2 hKintersection
  let TC : Subgroup C := T.subgroupOf C
  let TNC : Subgroup C := TC ⊔ N
  let TNG : Subgroup G := TNC.map C.subtype
  have hTCcard : Nat.card TC = 2 := by
    calc
      Nat.card TC = Nat.card T :=
        Nat.card_congr
          (Subgroup.subgroupOfEquivOfLe (hT_le_U.trans hU_le_C)).toEquiv
      _ = 2 := hTcard
  have hTC_le_S : TC ≤ (S : Subgroup C) := by
    rw [hS_eq_XC]
    intro t ht
    exact hT_le_U.trans hU_le_X ht
  have hqNker : qN.ker = N := by
    dsimp [qN]
    exact QuotientGroup.ker_mk' (G := C) (N := N)
  have hmapNbot : N.map qN = ⊥ := by
    rw [Subgroup.map_eq_bot_iff, hqNker]
  have hmapTNC : TNC.map qN = TC.map qN := by
    dsimp [TNC]
    rw [Subgroup.map_sup, hmapNbot, sup_bot_eq]
  have hker_le_TNC : qN.ker ≤ TNC := by
    rw [hqNker]
    exact le_sup_right
  have hcomapTbar : (TC.map qN).comap qN = TNC := by
    rw [← hmapTNC]
    exact Subgroup.comap_map_eq_self hker_le_TNC
  have hcTNC_iff (c : C) : c ∈ TNC ↔ qN c ∈ TC.map qN := by
    change c ∈ TNC ↔ c ∈ (TC.map qN).comap qN
    rw [hcomapTbar]
  have hTbar_iff_order_dvd_two (c : C) :
      qN c ∈ TC.map qN ↔ orderOf (qN c) ∣ 2 := by
    constructor
    · rintro ⟨t, ht, htc⟩
      rw [← htc]
      exact (orderOf_map_dvd qN t).trans (by
        have htorder := TC.orderOf_dvd_natCard ht
        simpa [hTCcard] using htorder)
    · intro hcorder
      obtain ⟨s, hs⟩ := eSN.surjective (qN c)
      have hsorder : orderOf s ∣ 2 := by
        rw [← eSN.orderOf_eq s, hs]
        exact hcorder
      rcases (Nat.dvd_prime Nat.prime_two).mp hsorder with hsone | hstwo
      · have hs_eq_one : s = 1 := orderOf_eq_one_iff.mp hsone
        have hqc_one : qN c = 1 := by
          rw [← hs, hs_eq_one, map_one]
        rw [hqc_one]
        exact (TC.map qN).one_mem
      · have hsXC : (s : C) ∈ XC := by
          rw [← hS_eq_XC]
          exact s.property
        have hsX : (s : G) ∈ X := hsXC
        have hsorderG : orderOf (s : G) = 2 := by
          calc
            orderOf (s : G) = orderOf (s : C) := Subgroup.orderOf_coe _
            _ = orderOf s := Subgroup.orderOf_coe _
            _ = 2 := hstwo
        have hsT : (s : G) ∈ T := hUniqueInvolutionX (s : G) hsX hsorderG
        have hsTC : (s : C) ∈ TC := hsT
        refine ⟨(s : C), hsTC, ?_⟩
        change qN (s : C) = qN c at hs
        exact hs
  have horder_dvd_quotient_mul_kernel (c : C) :
      orderOf c ∣ orderOf (qN c) * Nat.card N := by
    have hpowKer : c ^ orderOf (qN c) ∈ qN.ker := by
      change qN (c ^ orderOf (qN c)) = 1
      rw [map_pow, pow_orderOf_eq_one]
    rw [hqNker] at hpowKer
    let cn : N := ⟨c ^ orderOf (qN c), hpowKer⟩
    have hpowOneN : cn ^ Nat.card N = 1 := pow_card_eq_one'
    have hpowOne : (c ^ orderOf (qN c)) ^ Nat.card N = 1 :=
      congrArg Subtype.val hpowOneN
    apply orderOf_dvd_iff_pow_eq_one.mpr
    rw [pow_mul]
    exact hpowOne
  have hfour_order_iff_quotient (c : C) :
      4 ∣ orderOf c ↔ 4 ∣ orderOf (qN c) := by
    constructor
    · intro hc
      have hprod : 4 ∣ orderOf (qN c) * Nat.card N :=
        hc.trans (horder_dvd_quotient_mul_kernel c)
      have hcop : Nat.Coprime 4 (Nat.card N) := by
        simpa using hNodd.pow_left 2
      exact hcop.dvd_of_dvd_mul_right hprod
    · intro hc
      exact hc.trans (orderOf_map_dvd qN c)
  have hnot_order_dvd_two_iff_four (y : C ⧸ N) :
      (¬ orderOf y ∣ 2) ↔ 4 ∣ orderOf y := by
    obtain ⟨a, ha⟩ := (IsPGroup.iff_orderOf.mp hCquotp) y
    rw [ha]
    constructor
    · intro hnot
      have ha2 : 2 ≤ a := by
        by_contra ha2
        have ha_cases : a = 0 ∨ a = 1 := by omega
        rcases ha_cases with rfl | rfl
        · simp at hnot
        · norm_num at hnot
      simpa using Nat.pow_dvd_pow 2 ha2
    · intro hfour htwo
      have : 4 ∣ 2 := hfour.trans htwo
      norm_num at this
  have hc_not_mem_TNC_iff_four (c : C) :
      c ∉ TNC ↔ 4 ∣ orderOf c := by
    constructor
    · intro hcnot
      have hnotTwo : ¬ orderOf (qN c) ∣ 2 := by
        intro htwo
        apply hcnot
        exact (hcTNC_iff c).2 ((hTbar_iff_order_dvd_two c).2 htwo)
      exact (hfour_order_iff_quotient c).2
        ((hnot_order_dvd_two_iff_four (qN c)).1 hnotTwo)
    · intro hfour hcTNC
      have htwo : orderOf (qN c) ∣ 2 :=
        (hTbar_iff_order_dvd_two c).1 ((hcTNC_iff c).1 hcTNC)
      have hfourQ : 4 ∣ orderOf (qN c) :=
        (hfour_order_iff_quotient c).1 hfour
      have : 4 ∣ 2 := hfourQ.trans htwo
      norm_num at this
  have hmemTNG_iff (k : G) (hkC : k ∈ C) :
      k ∈ TNG ↔ (⟨k, hkC⟩ : C) ∈ TNC := by
    constructor
    · rintro ⟨c, hc, hck⟩
      have : c = (⟨k, hkC⟩ : C) := Subtype.ext hck
      simpa [this] using hc
    · intro hk
      exact ⟨⟨k, hkC⟩, hk, rfl⟩
  have hK_eq_source : K = (C : Set G) \ (TNG : Set G) := by
    ext k
    constructor
    · intro hk
      refine ⟨hk.1, ?_⟩
      intro hkTNG
      have hkTNC := (hmemTNG_iff k hk.1).1 hkTNG
      exact ((hc_not_mem_TNC_iff_four ⟨k, hk.1⟩).2 (by
        simpa [Subgroup.orderOf_mk] using hk.2)) hkTNC
    · intro hk
      have hkTNC : (⟨k, hk.1⟩ : C) ∉ TNC := by
        intro hkTNC
        exact hk.2 ((hmemTNG_iff k hk.1).2 hkTNC)
      refine ⟨hk.1, ?_⟩
      have hfour := (hc_not_mem_TNC_iff_four ⟨k, hk.1⟩).1 hkTNC
      simpa [Subgroup.orderOf_mk] using hfour
  have hCquotCyclic : IsCyclic (C ⧸ N) :=
    isCyclic_of_surjective eSN eSN.surjective
  let m : ℕ := Nat.card (C ⧸ N)
  let : NeZero m := ⟨by
    dsimp [m]
    exact Nat.card_pos.ne'⟩
  let zchar : Multiplicative (ZMod m) →* ℂˣ :=
    Circle.toUnits.comp (ZMod.toCircle (N := m)).toMonoidHom
  let eCyclic : Multiplicative (ZMod m) ≃* C ⧸ N :=
    zmodCyclicMulEquiv hCquotCyclic
  let chi0 : (C ⧸ N) →* ℂˣ :=
    zchar.comp eCyclic.symm.toMonoidHom
  have hchi0_injective : Function.Injective chi0 := by
    intro a b hab
    apply eCyclic.symm.injective
    apply Multiplicative.ext
    apply ZMod.injective_toCircle
    apply Subtype.ext
    exact congrArg Units.val hab
  let chi : (C ⧸ N) →* ℂˣ := chi0 ^ 2
  have hchi_qN_eq_one_iff (c : C) : chi (qN c) = 1 ↔ c ∈ TNC := by
    constructor
    · intro hc
      have hchi0sq : chi0 ((qN c) ^ 2) = chi0 1 := by
        rw [map_pow, map_one]
        simpa [chi] using hc
      have hsq : (qN c) ^ 2 = 1 := hchi0_injective hchi0sq
      exact (hcTNC_iff c).2 ((hTbar_iff_order_dvd_two c).2
        (orderOf_dvd_iff_pow_eq_one.mpr hsq))
    · intro hc
      have hsq : (qN c) ^ 2 = 1 :=
        orderOf_dvd_iff_pow_eq_one.mp
          ((hTbar_iff_order_dvd_two c).1 ((hcTNC_iff c).1 hc))
      change (chi0 (qN c)) ^ 2 = 1
      rw [← map_pow, hsq, map_one]
  let piCH : CH →* C ⧸ N := qN.comp eCH.toMonoidHom
  let lambda : Section1.ClassFunction CH :=
    Section1.characterInflationByHom piCH chi
  have hlambda_eq_one_iff (c : CH) : lambda c = 1 ↔ eCH c ∈ TNC := by
    have hunit : chi (piCH c) = 1 ↔ lambda c = 1 := by
      constructor
      · intro h
        change (chi (piCH c) : ℂ) = 1
        rw [h]
        rfl
      · intro h
        apply Units.ext
        exact h
    rw [← hunit]
    exact hchi_qN_eq_one_iff (eCH c)
  have hlambda_irreducible :
      Section1.IsIrreducibleCharacterOnGroup lambda := by
    simpa [lambda] using
      Section1.characterInflationByHom_isIrreducibleCharacterOnGroup piCH chi
  have hlambda_class : Section1.IsClassFunction lambda := by
    simpa [lambda] using
      Section1.characterInflationByHom_isClassFunction piCH chi
  let eta : Section1.ClassFunction H :=
    Section1.inducedCF CH (Section1.principalCharacter CH - lambda)
  obtain ⟨k0, hk0K, _hk0ne⟩ := hKnontrivial
  let k0CH : CH := ⟨⟨k0, hC_le_H hk0K.1⟩, hk0K.1⟩
  have hk0_not_TNC : eCH k0CH ∉ TNC := by
    change (⟨k0, hk0K.1⟩ : C) ∉ TNC
    exact (hc_not_mem_TNC_iff_four ⟨k0, hk0K.1⟩).2 (by
      simpa [Subgroup.orderOf_mk] using hk0K.2)
  have hlambda_ne_principal :
      lambda ≠ Section1.principalCharacter CH := by
    intro heq
    have hvalue := congrFun heq k0CH
    have hlambda_one : lambda k0CH = 1 := by
      simpa [Section1.principalCharacter] using hvalue
    exact hk0_not_TNC ((hlambda_eq_one_iff k0CH).1 hlambda_one)
  have hlambda_principal_zero :
      Section1.scalarProduct CH lambda
          (Section1.principalCharacter CH) = 0 :=
    Section1.scalarProduct_irreducibleCharacter_principal_eq_zero_of_ne
      hlambda_irreducible hlambda_ne_principal
  have hprincipal_self :
      Section1.scalarProduct CH (Section1.principalCharacter CH)
          (Section1.principalCharacter CH) = 1 := by
    let : Fintype CH := Fintype.ofFinite CH
    unfold Section1.scalarProduct Section1.principalCharacter
    simp only [mul_one, star_one, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul]
    rw [← Nat.card_eq_fintype_card]
    apply inv_mul_cancel₀
    exact_mod_cast (Nat.card_pos.ne' : Nat.card CH ≠ 0)
  have heta_principal :
      Section1.scalarProduct H eta (Section1.principalCharacter H) = 1 := by
    rw [show eta = Section1.inducedCF CH
      (Section1.principalCharacter CH - lambda) by rfl]
    rw [Section1.scalarProduct_inducedCF_left CH
      (Section1.principalCharacter CH - lambda)
      (Section1.principalCharacter H) (by
        intro x g
        rfl)]
    have hres :
        Section1.subgroupRestriction CH (Section1.principalCharacter H) =
          Section1.principalCharacter CH := by
      ext c
      rfl
    rw [hres]
    have hsub :
        Section1.principalCharacter CH - lambda =
          Section1.principalCharacter CH + (-1 : ℂ) • lambda := by
      ext c
      simp [sub_eq_add_neg]
    rw [hsub, Section1.scalarProduct_add_left,
      Section1.scalarProduct_smul_left, hprincipal_self,
      hlambda_principal_zero]
    norm_num
  have hqQ_not_XQ : (⟨q, hqQ⟩ : Q) ∉ XQ := by
    intro hqXQ
    have hqX : q ∈ X := by
      exact ⟨(⟨q, hqQ⟩ : Q), hqXQ, rfl⟩
    exact hqC (hX_le_C hqX)
  have hq_conj_quotient_inv (c : C) :
      qN ⟨q * (c : G) * q⁻¹,
        (Subgroup.mem_normalizer_iff.mp (hH_le_normC qH.property) c).1 c.property⟩ =
        (qN c)⁻¹ := by
    have hy : qN c ∈ (S : Subgroup C).map qN := by
      rw [hSmap_top]
      exact Subgroup.mem_top _
    rcases hy with ⟨s, hsS, hsc⟩
    have hsX : (s : G) ∈ X := by
      rw [hS_eq_XC] at hsS
      exact hsS
    rcases hsX with ⟨x, hxXQ, hxs⟩
    have hconjS : q * (s : G) * q⁻¹ = (s : G)⁻¹ := by
      have hconjQ := hConjInvXQ (⟨q, hqQ⟩ : Q) hqQ_not_XQ x hxXQ
      have hconjG := congrArg (fun z : Q => (z : G)) hconjQ
      change (x : G) = (s : G) at hxs
      simpa [hxs] using hconjG
    have hscN : s / c ∈ N := by
      exact QuotientGroup.eq_iff_div_mem.mp hsc
    let qs : C :=
      ⟨q * (s : G) * q⁻¹,
        (Subgroup.mem_normalizer_iff.mp (hH_le_normC qH.property) s).1 s.property⟩
    let qc : C :=
      ⟨q * (c : G) * q⁻¹,
        (Subgroup.mem_normalizer_iff.mp (hH_le_normC qH.property) c).1 c.property⟩
    let qsc : C :=
      ⟨q * ((s / c : C) : G) * q⁻¹,
        (Subgroup.mem_normalizer_iff.mp (hH_le_normC qH.property) (s / c)).1
          (s / c).property⟩
    have hqsc_mem_N : qsc ∈ N := by
      apply (hNH_iff _).1
      have hscNH :
          (⟨((s / c : C) : G), hC_le_H (s / c).property⟩ : H) ∈ NH :=
        (hNH_iff (s / c)).2 hscN
      exact hNHnormal.conj_mem _ hscNH qH
    have hqsc : qN qs = qN qc := by
      change (↑qs : C ⧸ N) = ↑qc
      apply QuotientGroup.eq_iff_div_mem.mpr
      have hdiv : qs / qc = qsc := by
        apply Subtype.ext
        dsimp [qs, qc, qsc]
        simp only [div_eq_mul_inv]
        group
      rw [hdiv]
      exact hqsc_mem_N
    calc
      qN qc = qN qs := hqsc.symm
      _ = qN s⁻¹ := by
        apply congrArg qN
        apply Subtype.ext
        exact hconjS
      _ = (qN s)⁻¹ := map_inv qN s
      _ = (qN c)⁻¹ := congrArg Inv.inv hsc
  have hq_conj_lambda_inv (c : CH) :
      lambda ⟨qH * (c : H) * qH⁻¹,
        hCHnormal.conj_mem (c : H) c.property qH⟩ = lambda c⁻¹ := by
    let qcCH : CH := ⟨qH * (c : H) * qH⁻¹,
      hCHnormal.conj_mem (c : H) c.property qH⟩
    let qcC : C :=
      ⟨q * ((eCH c : C) : G) * q⁻¹,
        (Subgroup.mem_normalizer_iff.mp
          (hH_le_normC qH.property) (eCH c)).1 (eCH c).property⟩
    have heqc : eCH qcCH = qcC := by
      apply Subtype.ext
      rfl
    change
      (chi (qN (eCH qcCH)) : ℂ) =
      (chi ((qN (eCH c))⁻¹) : ℂ)
    rw [heqc]
    exact congrArg (fun y : C ⧸ N => (chi y : ℂ))
      (hq_conj_quotient_inv (eCH c))
  have hmX : m = Nat.card X := by
    dsimp [m]
    rw [hCquotNcard, hScardX]
  have hchi_inv_split :=
    cyclic_square_character_inversion_split m eCyclic chi0 hchi0_injective
  have hchi_inv_small :
      Nat.card X = 4 →
        ∀ y : C ⧸ N, (chi y⁻¹ : ℂ) = (chi y : ℂ) := by
    intro hX4
    exact hchi_inv_split.1 (hmX.trans hX4)
  have hchi_inv_large :
      4 < Nat.card X →
        ∃ y : C ⧸ N, (chi y⁻¹ : ℂ) ≠ (chi y : ℂ) := by
    intro hXlarge
    apply hchi_inv_split.2
    simpa [hmX] using hXlarge
  have hpiCH_surjective : Function.Surjective piCH := by
    intro y
    obtain ⟨c, hc⟩ := QuotientGroup.mk'_surjective N y
    refine ⟨eCH.symm c, ?_⟩
    simpa [piCH, qN] using hc
  have hqH_mem_inertia_iff :
      qH ∈ Section1.inertiaSubgroup CH lambda ↔
        ∀ c : CH, lambda c⁻¹ = lambda c := by
    constructor
    · intro hqI c
      have hfun : Section1.conjugateOnNormal CH lambda qH = lambda := hqI
      have hv := congrFun hfun c
      simpa [Section1.conjugateOnNormal, hq_conj_lambda_inv c] using hv
    · intro hfix
      change Section1.conjugateOnNormal CH lambda qH = lambda
      funext c
      simpa [Section1.conjugateOnNormal, hq_conj_lambda_inv c] using hfix c
  have hqH_inertia_small (hX4 : Nat.card X = 4) :
      qH ∈ Section1.inertiaSubgroup CH lambda := by
    rw [hqH_mem_inertia_iff]
    intro c
    simpa [lambda, Section1.characterInflationByHom] using
      hchi_inv_small hX4 (piCH c)
  have hqH_not_inertia_large (hXlarge : 4 < Nat.card X) :
      qH ∉ Section1.inertiaSubgroup CH lambda := by
    intro hqI
    have hfix := hqH_mem_inertia_iff.mp hqI
    obtain ⟨y, hy⟩ := hchi_inv_large hXlarge
    obtain ⟨c, rfl⟩ := hpiCH_surjective y
    exact hy (by
      simpa [lambda, Section1.characterInflationByHom] using hfix c)
  let I := Section1.inertiaSubgroup CH lambda
  have hCH_le_I : CH ≤ I := by
    intro x hx
    change Section1.conjugateOnNormal CH lambda x = lambda
    funext c
    change lambda ⟨x * (c : H) * x⁻¹,
      hCHnormal.conj_mem (c : H) c.property x⟩ = lambda c
    exact hlambda_class ⟨x, hx⟩ c
  have hrel_dvd_two : CH.relIndex I ∣ 2 := by
    rw [← hHquotCcard, ← Subgroup.index_eq_card]
    exact Subgroup.relIndex_dvd_index_of_le hCH_le_I
  have hrel_cases : CH.relIndex I = 1 ∨ CH.relIndex I = 2 :=
    (Nat.dvd_prime Nat.prime_two).1 hrel_dvd_two
  have hCHtop : CH.relIndex (⊤ : Subgroup H) = 2 := by
    simpa [Subgroup.relIndex_top_right, Subgroup.index_eq_card] using hHquotCcard
  have hlambda_rel_large (hXlarge : 4 < Nat.card X) : CH.relIndex I = 1 := by
    rcases hrel_cases with h1 | h2
    · exact h1
    · exfalso
      have hmul := Subgroup.relIndex_mul_relIndex CH I ⊤ hCH_le_I le_top
      rw [h2, hCHtop] at hmul
      have hItop : I.relIndex ⊤ = 1 := by omega
      have htopI : (⊤ : Subgroup H) ≤ I := (Subgroup.relIndex_eq_one).1 hItop
      exact hqH_not_inertia_large hXlarge (htopI (Subgroup.mem_top qH))
  have hlambda_rel_small (hX4 : Nat.card X = 4) : CH.relIndex I = 2 := by
    rcases hrel_cases with h1 | h2
    · exact False.elim (hqH_not_CH
        ((Subgroup.relIndex_eq_one).1 h1 (hqH_inertia_small hX4)))
    · exact h2
  have hstage_c_input :
      Section1.scalarProduct H eta (Section1.principalCharacter H) = 1 ∧
      (Section1.scalarProduct H eta eta = 3 ∨
        Section1.scalarProduct H eta eta = 4) ∧
      (4 < Nat.card X →
        Section1.scalarProduct H eta eta = 3) ∧
      (Nat.card X = 4 →
        Section1.scalarProduct H eta eta = 4) := by
    have hfour_le_X : 4 ≤ Nat.card X := by
      rw [← hUcard]
      exact Nat.card_le_card_of_injective
        (fun u : U => (⟨u, hU_le_X u.property⟩ : X))
        (fun _ _ h => Subtype.ext (congrArg (fun z : X => (z : G)) h))
    exact example3_stage_c_norm_core CH lambda eta (Nat.card X)
      hlambda_irreducible hlambda_ne_principal rfl hHquotCcard
        heta_principal hlambda_rel_large hlambda_rel_small hfour_le_X
  have htheta_support :
      ∀ c : CH, ((c : H) : G) ∉ K →
        (Section1.principalCharacter CH - lambda) c = 0 := by
    intro c hcK
    have hcC : ((c : H) : G) ∈ C := by
      exact c.property
    have hcTNG : ((c : H) : G) ∈ TNG := by
      by_contra hcTNG
      apply hcK
      rw [hK_eq_source]
      exact ⟨hcC, hcTNG⟩
    have hcTNC :=
      (hmemTNG_iff ((c : H) : G) hcC).1 hcTNG
    have hlc : lambda c = 1 := (hlambda_eq_one_iff c).2 (by
      convert hcTNC using 1
      apply Subtype.ext
      rfl)
    simp [Section1.principalCharacter, hlc]
  have heta_support :
      ∀ h : H, (h : G) ∉ K → eta h = 0 := by
    intro h hhK
    rw [show eta = Section1.inducedCF CH
      (Section1.principalCharacter CH - lambda) by rfl]
    unfold Section1.inducedCF Section1.inducedClassFunction
    apply mul_eq_zero_of_right
    apply Finset.sum_eq_zero
    intro x _hx
    split
    next hxCH =>
      have hxNorm := hHnormK x.property
      change ∀ k : G, k ∈ K ↔
        (x : G) * k * (x : G)⁻¹ ∈ K at hxNorm
      have hconjNot : (((x * h * x⁻¹ : H) : G)) ∉ K := by
        intro hconjK
        apply hhK
        exact (hxNorm (h : G)).2 (by simpa using hconjK)
      exact htheta_support
        (⟨x * h * x⁻¹, hxCH⟩ : CH) (by simpa using hconjNot)
    next hxnot =>
      rfl
  have hone_not_K : (1 : G) ∉ K := by
    intro h1
    simp [K] at h1
  have heta_one : eta 1 = 0 :=
    heta_support 1 (by simpa using hone_not_K)
  have hKfour : ∀ k : G, k ∈ K → 4 ∣ orderOf k := by
    intro k hk
    exact hk.2
  have hetaKSmall : Nat.card X = 4 →
      ∀ (k : G) (hk : k ∈ K), eta ⟨k, hKTI.1 hk⟩ = 4 := by
    intro hX4 k hk
    let c : CH := ⟨⟨k, hC_le_H hk.1⟩, hk.1⟩
    have hcnot : eCH c ∉ TNC := by
      change (⟨k, hk.1⟩ : C) ∉ TNC
      exact (hc_not_mem_TNC_iff_four ⟨k, hk.1⟩).2 (by
        simpa [Subgroup.orderOf_mk] using hk.2)
    have hlambda_ne : lambda c ≠ 1 := by
      intro hlambda
      exact hcnot ((hlambda_eq_one_iff c).1 hlambda)
    have hlambda_inv : lambda c⁻¹ = lambda c := by
      simpa [lambda, Section1.characterInflationByHom] using
        hchi_inv_small hX4 (piCH c)
    have hlambda_sq : (lambda c) ^ 2 = 1 := by
      have hmul : lambda c⁻¹ * lambda c = 1 := by
        simp [lambda, Section1.characterInflationByHom]
      rw [hlambda_inv] at hmul
      simpa [pow_two] using hmul
    have hlambda_neg : lambda c = -1 := by
      rcases sq_eq_one_iff.mp hlambda_sq with hlambda_one | hlambda_neg
      · exact False.elim (hlambda_ne hlambda_one)
      · exact hlambda_neg
    have htop_le_I : (⊤ : Subgroup H) ≤ I := by
      have hmul := Subgroup.relIndex_mul_relIndex CH I ⊤ hCH_le_I le_top
      rw [hlambda_rel_small hX4, hCHtop] at hmul
      have hIrel : I.relIndex ⊤ = 1 := by omega
      exact (Subgroup.relIndex_eq_one).1 hIrel
    have htheta_fixed : ∀ x : H,
        Section1.conjugateOnNormal CH
          (Section1.principalCharacter CH - lambda) x =
            Section1.principalCharacter CH - lambda := by
      intro x
      have hlambda_fixed : Section1.conjugateOnNormal CH lambda x = lambda :=
        htop_le_I (Subgroup.mem_top x)
      funext d
      simpa [Section1.conjugateOnNormal, Section1.principalCharacter] using
        congrArg (fun z : ℂ => 1 - z) (congrFun hlambda_fixed d)
    have heta_restrict :
        Section1.subgroupRestriction CH eta = fun d =>
          2 * (Section1.principalCharacter CH - lambda) d := by
      simpa [eta] using
        example3_inducedCF_restrict_eq_two_mul_of_fixed CH
          (Section1.principalCharacter CH - lambda) hHquotCcard htheta_fixed
    have heta_c : eta (c : H) = 4 := by
      calc
        eta (c : H) = Section1.subgroupRestriction CH eta c := rfl
        _ = 2 * (Section1.principalCharacter CH - lambda) c :=
          congrFun heta_restrict c
        _ = 4 := by
          norm_num [Section1.principalCharacter, hlambda_neg]
    have hkc : (⟨k, hKTI.1 hk⟩ : H) = (c : H) := by
      apply Subtype.ext
      rfl
    rw [hkc]
    exact heta_c
  have hetaVirtualSmall : Theory.Character.IsVirtualCharacter eta := by
    rw [show eta = Section1.inducedCF CH
      (Section1.principalCharacter CH - lambda) by rfl]
    exact Section2.inducedCF_isVirtualCharacter_of_virtualCharacter CH
      (Section3.isVirtualCharacter_sub
        Section3.isVirtualCharacter_principalCharacter
        (Section3.isVirtualCharacter_of_irreducibleCharacterOnGroup
          hlambda_irreducible))
  have hzetaSmall : Nat.card X = 4 → ∀ g : G,
      ((∃ x : G, x * g * x⁻¹ ∈ K) ∧
        Section1.inducedCF H eta g = 4) ∨
      ((¬ ∃ x : G, x * g * x⁻¹ ∈ K) ∧
        Section1.inducedCF H eta g = 0) := by
    intro hX4
    exact example3_inducedCF_eq_four_or_zero_of_ti_constant_four
      H eta K hKTI hKfour hetaVirtualSmall heta_support (hetaKSmall hX4)
  have hzetaIntSmall : Nat.card X = 4 →
      ∀ g : G, ∃ n : ℤ, Section1.inducedCF H eta g = (n : ℂ) := by
    intro hX4
    exact example3_induced_integer_of_ti_constant_four
      H eta K hKTI hKfour hetaVirtualSmall heta_support (hetaKSmall hX4)
  have hHcard_Q_NH : Nat.card H = Nat.card Q * Nat.card NH := by
    rw [hHcard_QH_NH, hQHcard]
  have hNH_le_CH : NH ≤ CH := by
    intro a ha
    dsimp [NH] at ha
    rcases ha with ⟨b, hb, rfl⟩
    exact b.property
  have hsmallXData : Nat.card X = 4 →
      ∃ x : H, (x : G) ∈ K ∧ orderOf (x : G) = 4 ∧
        (∀ u : NH, Commute (x : G) (u : G)) ∧
        ∀ h : H, (h : G) ∈ K ↔
          (∃ u : NH, h = x * (u : H)) ∨
          (∃ u : NH, h = x⁻¹ * (u : H)) := by
    intro hX4
    let : IsCyclic X := hXcyclic
    obtain ⟨x, hxgen⟩ := IsCyclic.exists_generator (α := X)
    have hxzpowers : Subgroup.zpowers x = (⊤ : Subgroup X) := by
      apply le_antisymm le_top
      intro y _hy
      exact hxgen y
    have hxorderX : orderOf x = Nat.card X :=
      orderOf_eq_card_of_zpowers_eq_top hxzpowers
    have hxorderG : orderOf (x : G) = 4 := by
      rw [Subgroup.orderOf_coe, hxorderX, hX4]
    let xH : H := ⟨(x : G), hX_le_Q.trans hQ_le_H x.property⟩
    let xC : C := ⟨(x : G), hX_le_C x.property⟩
    have hxcomm : ∀ u : NH, Commute (x : G) (u : G) := by
      intro u
      have hXeqU : X = U := hOrderFourUniqueX X le_rfl hX4
      have hxU : (x : G) ∈ U := by
        rw [← hXeqU]
        exact x.property
      have huC : (u : G) ∈ C := hNH_le_CH u.property
      exact Subgroup.mem_centralizer_iff.mp huC (x : G) hxU
    have hquotCard : Nat.card (C ⧸ N) = 4 := by
      rw [hCquotNcard, hScardX, hX4]
    have hxqOrder : orderOf (qN xC) = 4 := by
      apply Nat.dvd_antisymm
      · simpa [hquotCard] using orderOf_dvd_natCard (qN xC)
      · exact (hfour_order_iff_quotient xC).1 (by
          simp [xC, Subgroup.orderOf_mk, hxorderG])
    refine ⟨xH, ?_, hxorderG, hxcomm, ?_⟩
    · exact ⟨hX_le_C x.property, by rw [hxorderG]⟩
    · intro h
      constructor
      · intro hhK
        let c : C := ⟨(h : G), hhK.1⟩
        have hcqFour : 4 ∣ orderOf (qN c) :=
          (hfour_order_iff_quotient c).1 (by
            simpa [c, Subgroup.orderOf_mk] using hhK.2)
        have hcqOrder : orderOf (qN c) = 4 := by
          apply Nat.dvd_antisymm
          · simpa [hquotCard] using orderOf_dvd_natCard (qN c)
          · exact hcqFour
        rcases example3_quotient_card_four_kernel_cosets N hCquotCyclic
            hquotCard hxqOrder hcqOrder with hcoset | hcoset
        · rcases hcoset with ⟨v, hcv⟩
          let vH : H := ⟨(v : G), hC_le_H (v : C).property⟩
          have hvNH : vH ∈ NH := (hNH_iff (v : C)).2 v.property
          let u : NH := ⟨vH, hvNH⟩
          left
          refine ⟨u, ?_⟩
          apply Subtype.ext
          have hcvG := congrArg (fun z : C => (z : G)) hcv
          calc
            (h : G) = (v : G) * (x : G) := by simpa [c, xC] using hcvG
            _ = (x : G) * (v : G) := by
              simpa [u, vH] using (hxcomm u).eq.symm
        · rcases hcoset with ⟨v, hcv⟩
          let vH : H := ⟨(v : G), hC_le_H (v : C).property⟩
          have hvNH : vH ∈ NH := (hNH_iff (v : C)).2 v.property
          let u : NH := ⟨vH, hvNH⟩
          right
          refine ⟨u, ?_⟩
          apply Subtype.ext
          have hcvG := congrArg (fun z : C => (z : G)) hcv
          calc
            (h : G) = (v : G) * (x : G)⁻¹ := by simpa [c, xC] using hcvG
            _ = (x : G)⁻¹ * (v : G) := by
              simpa [u, vH] using (hxcomm u).inv_left.eq.symm
      · rintro (⟨u, rfl⟩ | ⟨u, rfl⟩)
        · let uC : C := ⟨(u : G), hNH_le_CH u.property⟩
          have huN : uC ∈ N := (hNH_iff uC).1 (by
            change (u : H) ∈ NH
            exact u.property)
          let c : C := xC * uC
          have hquone : qN uC = 1 := by
            change (uC : C ⧸ N) = 1
            exact (QuotientGroup.eq_one_iff uC).2 huN
          have hfourC : 4 ∣ orderOf c :=
            (hfour_order_iff_quotient c).2 (by
              change 4 ∣ orderOf (qN xC * qN uC)
              rw [hquone, mul_one, hxqOrder])
          refine ⟨C.mul_mem (hX_le_C x.property) (hNH_le_CH u.property), ?_⟩
          simpa [c, xC, uC, Subgroup.orderOf_mk] using hfourC
        · let uC : C := ⟨(u : G), hNH_le_CH u.property⟩
          have huN : uC ∈ N := (hNH_iff uC).1 (by
            change (u : H) ∈ NH
            exact u.property)
          let c : C := xC⁻¹ * uC
          have hquone : qN uC = 1 := by
            change (uC : C ⧸ N) = 1
            exact (QuotientGroup.eq_one_iff uC).2 huN
          have hfourC : 4 ∣ orderOf c :=
            (hfour_order_iff_quotient c).2 (by
              change 4 ∣ orderOf ((qN xC)⁻¹ * qN uC)
              rw [hquone, mul_one, orderOf_inv, hxqOrder])
          refine ⟨C.mul_mem (C.inv_mem (hX_le_C x.property))
            (hNH_le_CH u.property), ?_⟩
          change 4 ∣ orderOf (c : G)
          rw [Subgroup.orderOf_coe]
          exact hfourC
  exact suzuki_example3_stage_c_to_l_core
    Q hn hQ H X CH hQcard_X NH hNHnormal hNHodd hHcard_Q_NH lambda eta K
      hsmallXData hKTI hKfour hetaKSmall heta_support heta_one hCHnormal hHquotCcard
      hlambda_irreducible hlambda_ne_principal rfl heta_principal
      hstage_c_input hzetaIntSmall hzetaSmall hcore hind

set_option maxHeartbeats 500000 in
/-- Suzuki, *Group Theory II*, Chapter 6, Section 2.2, Example 3
(Brauer--Suzuki theorem). -/
public theorem suzuki_chapter6_section2_2_example3
    {G : Type u} [Group G] [Finite G]
    (Q : Sylow 2 G) {n : ℕ} (hn : 3 ≤ n)
    (hQ : Nonempty (Q ≃* QuaternionGroup (2 ^ (n - 2)))) :
    2 ∣ Nat.card (Subgroup.center (G ⧸ pPrimeCore 2 G)) := by
  classical
  let P : ℕ → Prop := fun k =>
    ∀ (M : Type u) [Group M] [Finite M], Nat.card M = k →
      ∀ (S : Sylow 2 M) {m : ℕ}, 3 ≤ m →
        Nonempty (S ≃* QuaternionGroup (2 ^ (m - 2))) →
        2 ∣ Nat.card (Subgroup.center (M ⧸ pPrimeCore 2 M))
  have hP : ∀ k, P k := by
    intro k
    refine Nat.strong_induction_on k ?_
    intro k ih M _ _ hMcard S m hm hS
    by_cases hcore : pPrimeCore 2 M = ⊥
    · exact suzuki_example3_corefree_setup S hm hS hcore
        (fun R _ _ hRcard T j hj hT =>
          ih (Nat.card R) (by simpa [hMcard] using hRcard)
            R rfl T hj hT)
    · obtain ⟨Sbar, hSbar⟩ := example3_quotient_sylow S hS
      have hquot_lt :
          Nat.card (M ⧸ pPrimeCore 2 M) < Nat.card M :=
        natCard_quotient_lt_natCard_of_ne_bot (pPrimeCore 2 M) hcore
      have hquot_target :
          2 ∣ Nat.card (Subgroup.center
            ((M ⧸ pPrimeCore 2 M) ⧸
              pPrimeCore 2 (M ⧸ pPrimeCore 2 M))) :=
        ih (Nat.card (M ⧸ pPrimeCore 2 M))
          (by simpa [hMcard] using hquot_lt)
          (M ⧸ pPrimeCore 2 M) rfl Sbar hm hSbar
      have hquot_core :
          pPrimeCore 2 (M ⧸ pPrimeCore 2 M) = ⊥ := by
        simpa using pPrimeCore_quotient_pPrimeCore_eq_bot (G := M) (p := 2)
      exact example3_center_even_of_quotient_center_even_corefree
        hquot_core hquot_target
  exact hP (Nat.card G) G rfl Q hn hQ

end VI
end Suzuki
end External
end CFSG.BenderSuzuki
