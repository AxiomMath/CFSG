module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Classification
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.Definitions
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.GroupTheory.SpecificGroups.Quaternion

namespace CFSG
end CFSG
open CFSG

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

/-!
# Odd-characteristic SL₂ is not involved in a dihedral-Sylow group

For an odd prime `p`, `SL₂(p)` contains an explicit quaternion subgroup.
That subgroup cannot lie in a cyclic or dihedral Sylow 2-subgroup.  Since the
cyclic-or-dihedral Sylow condition descends to subgroups and quotients, this
excludes `SL₂(p)` from every subquotient of a finite group with dihedral
Sylow 2-subgroups.
-/

open scoped MatrixGroups

namespace CFSG.GorensteinWalter

open Glauberman

private theorem exists_qd_parameters {p : ℕ} [Fact p.Prime] :
    ∃ a b : ZMod p, a ^ 2 + b ^ 2 = -1 := by
  rcases Nat.sq_add_sq_zmodEq p (-1) with ⟨a, b, _ha, _hb, hab⟩
  refine ⟨(a : ZMod p), (b : ZMod p), ?_⟩
  have hc := (ZMod.intCast_eq_intCast_iff
    ((a : ℤ) ^ 2 + (b : ℤ) ^ 2) (-1) p).2 hab
  simpa using hc


private def qi {p : ℕ} [Fact p.Prime] : qdSL p :=
  ⟨!![(0 : ZMod p), -1; 1, 0], by
    simp [Matrix.det_fin_two_of]⟩

private def qj {p : ℕ} [Fact p.Prime]
    (a b : ZMod p) (hab : a ^ 2 + b ^ 2 = -1) : qdSL p :=
  ⟨!![a, b; b, -a], by
    rw [Matrix.det_fin_two_of]
    calc
      a * -a - b * b = -(a ^ 2 + b ^ 2) := by ring
      _ = 1 := by rw [hab]; simp⟩

set_option backward.isDefEq.respectTransparency false in
private lemma qi_sq {p : ℕ} [Fact p.Prime] :
    (qi (p := p)) ^ 2 = -(1 : qdSL p) := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [qi, pow_two, Matrix.mul_apply, Fin.sum_univ_two]

set_option backward.isDefEq.respectTransparency false in
private lemma qj_sq {p : ℕ} [Fact p.Prime]
    (a b : ZMod p) (hab : a ^ 2 + b ^ 2 = -1) :
    (qj a b hab) ^ 2 = -(1 : qdSL p) := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [qj, pow_two, Matrix.mul_apply, Fin.sum_univ_two] <;>
    ring_nf <;>
    simpa [pow_two, add_comm] using hab

set_option backward.isDefEq.respectTransparency false in
private lemma qi_mul_qj {p : ℕ} [Fact p.Prime]
    (a b : ZMod p) (hab : a ^ 2 + b ^ 2 = -1) :
    qi * qj a b hab = -(qj a b hab * qi) := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [qi, qj, Matrix.mul_apply, Fin.sum_univ_two]

private lemma neg_one_ne_one_qdSL {p : ℕ} [Fact p.Prime]
    (hpodd : p ≠ 2) : -(1 : qdSL p) ≠ 1 := by
  intro h
  have hentry := congrArg
    (fun A : qdSL p => (A : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 0) h
  have hz : (-1 : ZMod p) = 1 := by simpa using hentry
  have htwo : (2 : ZMod p) = 0 := by
    calc
      (2 : ZMod p) = 1 + 1 := by norm_num
      _ = -1 + 1 := by rw [hz]
      _ = 0 := neg_add_cancel 1
  have hpdiv : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp htwo
  rcases (Nat.dvd_prime Nat.prime_two).mp hpdiv with hp1 | hp2
  · exact (Fact.out : p.Prime).ne_one hp1
  · exact hpodd hp2

private lemma qi_inv {p : ℕ} [Fact p.Prime] :
    (qi (p := p))⁻¹ = -qi := by
  apply inv_eq_of_mul_eq_one_right
  rw [mul_neg, ← pow_two, qi_sq]
  simp

private lemma qj_mul_qi {p : ℕ} [Fact p.Prime]
    (a b : ZMod p) (hab : a ^ 2 + b ^ 2 = -1) :
    qj a b hab * qi = -(qi * qj a b hab) := by
  have h := congrArg Neg.neg (qi_mul_qj a b hab)
  simpa using h.symm

private lemma qj_conj_qi {p : ℕ} [Fact p.Prime]
    (a b : ZMod p) (hab : a ^ 2 + b ^ 2 = -1) :
    qj a b hab * qi * (qj a b hab)⁻¹ = qi⁻¹ := by
  have hji : qj a b hab * qi = qi⁻¹ * qj a b hab := by
    rw [qj_mul_qi, qi_inv]
    simp
  rw [hji]
  group

private lemma qi_order {p : ℕ} [Fact p.Prime] (hpodd : p ≠ 2) :
    orderOf (qi (p := p)) = 4 := by
  change orderOf (qi (p := p)) = 2 ^ 2
  apply orderOf_eq_prime_pow (p := 2) (n := 1)
  · intro h
    apply neg_one_ne_one_qdSL hpodd
    rw [← qi_sq]
    exact h
  · calc
      qi ^ (2 ^ 2) = (qi ^ 2) ^ 2 := by rw [← pow_mul]; norm_num
      _ = (-(1 : qdSL p)) ^ 2 := by rw [qi_sq]
      _ = 1 := by simp

private lemma pow_val_add_eq {D : Type*} [Group D] [Finite D]
    {ρ : D} {n : ℕ} (hn : orderOf ρ = n)
    (i j : ZMod n) : ρ ^ ((i + j).val) = ρ ^ i.val * ρ ^ j.val := by
  have : NeZero n := ⟨by rw [← hn]; exact (orderOf_pos ρ).ne'⟩
  have hcong : (i.val + j.val) % n ≡ i.val + j.val [MOD n] :=
    Nat.mod_modEq (i.val + j.val) n
  have hx : ρ ^ n = 1 := by rw [← hn]; exact pow_orderOf_eq_one ρ
  calc
    ρ ^ ((i + j).val) = ρ ^ ((i.val + j.val) % n) := by
      rw [ZMod.val_add (n := n) i j]
    _ = ρ ^ (i.val + j.val) := pow_eq_pow_of_modEq hcong hx
    _ = ρ ^ i.val * ρ ^ j.val := by rw [pow_add]

private lemma pow_val_sub_zpow {D : Type*} [Group D] [Finite D]
    {ρ : D} {n : ℕ} (hn : orderOf ρ = n)
    (i j : ZMod n) : ρ ^ ((j - i).val) = ρ ^ ((j.val : ℤ) - (i.val : ℤ)) := by
  have : NeZero n := ⟨by rw [← hn]; exact (orderOf_pos ρ).ne'⟩
  have hji : (i + (j - i) : ZMod n) = j := by
    simp [sub_eq_add_neg]
  have hval : j.val = (i.val + (j - i).val) % n := by
    calc
      j.val = (i + (j - i) : ZMod n).val := by rw [hji]
      _ = (i.val + (j - i).val) % n := ZMod.val_add (n := n) i (j - i)
  have hcong : j.val ≡ i.val + (j - i).val [MOD n] := by
    rw [hval]
    exact Nat.mod_modEq _ _
  have hx : ρ ^ n = 1 := by rw [← hn]; exact pow_orderOf_eq_one ρ
  have hp : ρ ^ j.val = ρ ^ i.val * ρ ^ ((j - i).val) := by
    calc
      ρ ^ j.val = ρ ^ (i.val + (j - i).val) :=
        pow_eq_pow_of_modEq hcong hx
      _ = ρ ^ i.val * ρ ^ ((j - i).val) := by rw [pow_add]
  calc
    ρ ^ ((j - i).val) = (ρ ^ i.val)⁻¹ * ρ ^ j.val := by rw [hp]; group
    _ = ρ ^ (-(i.val : ℤ)) * ρ ^ (j.val : ℤ) := by
      rw [← zpow_natCast (a := ρ) (n := i.val),
        ← zpow_neg (a := ρ) (n := (i.val : ℤ)),
        ← zpow_natCast (a := ρ) (n := j.val)]
    _ = ρ ^ ((j.val : ℤ) - (i.val : ℤ)) := by
      rw [← zpow_add]
      congr 1
      ring

private lemma rel_zpow_mul {D : Type*} [Group D] {ρ σ : D}
    (hrel : σ * ρ * σ⁻¹ = ρ⁻¹) (t : ℕ) :
    σ * ρ ^ t = ρ ^ (-(t : ℤ)) * σ := by
  induction t with
  | zero => simp
  | succ t ih =>
      have h' : σ * ρ = ρ⁻¹ * σ := by
        simpa [mul_assoc] using congrArg (fun x : D => x * σ) hrel
      calc
        σ * ρ ^ (t + 1) = σ * (ρ ^ t * ρ) := by rw [pow_succ]
        _ = (σ * ρ ^ t) * ρ := by rw [mul_assoc]
        _ = (ρ ^ (-(t : ℤ)) * σ) * ρ := by rw [ih]
        _ = ρ ^ (-(t : ℤ)) * (σ * ρ) := by rw [mul_assoc]
        _ = ρ ^ (-(t : ℤ)) * (ρ⁻¹ * σ) := by rw [h']
        _ = (ρ ^ (-(t : ℤ)) * ρ⁻¹) * σ := by rw [mul_assoc]
        _ = ρ ^ (-((t + 1 : ℕ) : ℤ)) * σ := by
          rw [← zpow_neg_one ρ, ← zpow_add]
          exact congrArg (fun e : ℤ => ρ ^ e * σ) (by omega)

private lemma pow_mul_rel {D : Type*} [Group D] {ρ σ : D}
    (hrel : σ * ρ * σ⁻¹ = ρ⁻¹) (t : ℕ) :
    ρ ^ t * σ = σ * ρ ^ (-(t : ℤ)) := by
  have hconjInv : σ * ρ⁻¹ * σ⁻¹ = ρ := by
    have h := congrArg Inv.inv hrel
    simpa [mul_assoc] using h
  have hρσ : ρ * σ = σ * ρ⁻¹ := by
    calc
      ρ * σ = (σ * ρ⁻¹ * σ⁻¹) * σ := by rw [hconjInv]
      _ = σ * ρ⁻¹ := by group
  induction t with
  | zero => simp
  | succ t ih =>
      calc
        ρ ^ (t + 1) * σ = (ρ ^ t * ρ) * σ := by rw [pow_succ]
        _ = ρ ^ t * (ρ * σ) := by rw [mul_assoc]
        _ = ρ ^ t * (σ * ρ⁻¹) := by rw [hρσ]
        _ = (ρ ^ t * σ) * ρ⁻¹ := by rw [mul_assoc]
        _ = (σ * ρ ^ (-(t : ℤ))) * ρ⁻¹ := by rw [ih]
        _ = σ * ρ ^ (-((t + 1 : ℕ) : ℤ)) := by
          rw [mul_assoc, ← zpow_neg_one ρ, ← zpow_add]
          exact congrArg (fun e : ℤ => σ * ρ ^ e) (by omega)

private def quaternionToQdSL {p : ℕ} [Fact p.Prime]
    (hpodd : p ≠ 2) (a b : ZMod p) (hab : a ^ 2 + b ^ 2 = -1) :
    QuaternionGroup 2 →* qdSL p where
  toFun
    | QuaternionGroup.a i => qi ^ i.val
    | QuaternionGroup.xa i => qj a b hab * qi ^ i.val
  map_one' := by
    change qi ^ 0 = 1
    simp
  map_mul' := by
    have hn : orderOf (qi (p := p)) = 4 := qi_order hpodd
    have hrel : qj a b hab * qi * (qj a b hab)⁻¹ = qi⁻¹ :=
      qj_conj_qi a b hab
    rintro (i | i) (j | j)
    · change qi ^ (i + j).val = qi ^ i.val * qi ^ j.val
      exact pow_val_add_eq hn i j
    · change qj a b hab * qi ^ (j - i).val =
        qi ^ i.val * (qj a b hab * qi ^ j.val)
      symm
      calc
        qi ^ i.val * (qj a b hab * qi ^ j.val) =
            (qi ^ i.val * qj a b hab) * qi ^ j.val := by rw [mul_assoc]
        _ = (qj a b hab * qi ^ (-(i.val : ℤ))) * qi ^ j.val := by
          rw [pow_mul_rel hrel i.val]
        _ = qj a b hab *
            (qi ^ (-(i.val : ℤ)) * qi ^ (j.val : ℤ)) := by
          rw [mul_assoc, zpow_natCast]
        _ = qj a b hab * qi ^ ((j.val : ℤ) - (i.val : ℤ)) := by
          rw [← zpow_add]
          congr 2
          ring
        _ = qj a b hab * qi ^ (j - i).val := by rw [pow_val_sub_zpow hn i j]
    · change qj a b hab * qi ^ (i + j).val =
        (qj a b hab * qi ^ i.val) * qi ^ j.val
      rw [pow_val_add_eq hn]
      simp [mul_assoc]
    · change qi ^ (((2 : ZMod 4) + j - i).val) =
        (qj a b hab * qi ^ i.val) * (qj a b hab * qi ^ j.val)
      symm
      calc
        (qj a b hab * qi ^ i.val) * (qj a b hab * qi ^ j.val) =
            qj a b hab * (qi ^ i.val * qj a b hab) * qi ^ j.val := by group
        _ = qj a b hab * (qj a b hab * qi ^ (-(i.val : ℤ))) *
            qi ^ j.val := by rw [pow_mul_rel hrel i.val]
        _ = (qj a b hab) ^ 2 *
            (qi ^ (-(i.val : ℤ)) * qi ^ (j.val : ℤ)) := by
          rw [pow_two]
          group
        _ = qi ^ 2 *
            (qi ^ (-(i.val : ℤ)) * qi ^ (j.val : ℤ)) := by
          rw [qj_sq, qi_sq]
        _ = qi ^ 2 * qi ^ ((j.val : ℤ) - (i.val : ℤ)) := by
          rw [← zpow_add]
          congr 2
          ring
        _ = qi ^ 2 * qi ^ (j - i).val := by rw [pow_val_sub_zpow hn i j]
        _ = qi ^ ((2 : ZMod 4) + (j - i)).val := by
          simpa only [show (2 : ZMod 4).val = 2 by decide] using
            (pow_val_add_eq hn (2 : ZMod 4) (j - i)).symm
        _ = qi ^ ((2 : ZMod 4) + j - i).val := by
          congr 2
          ring

private lemma qj_not_mem_zpowers_qi {p : ℕ} [Fact p.Prime]
    (hpodd : p ≠ 2) (a b : ZMod p) (hab : a ^ 2 + b ^ 2 = -1) :
    qj a b hab ∉ Subgroup.zpowers (qi (p := p)) := by
  intro hj
  rcases (Subgroup.mem_zpowers_iff.mp hj) with ⟨k, hk⟩
  have hcomm : qj a b hab * qi = qi * qj a b hab := by
    rw [← hk]
    exact ((Commute.refl (qi (p := p))).zpow_left k).eq
  have hneg : qi * qj a b hab = -(qi * qj a b hab) := by
    calc
      qi * qj a b hab = qj a b hab * qi := hcomm.symm
      _ = -(qi * qj a b hab) := qj_mul_qi a b hab
  have hone : (1 : qdSL p) = -1 := by
    calc
      (1 : qdSL p) = (qi * qj a b hab)⁻¹ * (qi * qj a b hab) := by simp
      _ = (qi * qj a b hab)⁻¹ * (-(qi * qj a b hab)) :=
        congrArg (fun y : qdSL p => (qi * qj a b hab)⁻¹ * y) hneg
      _ = -1 := by rw [mul_neg]; simp
  exact neg_one_ne_one_qdSL hpodd hone.symm

private lemma quaternionToQdSL_injective {p : ℕ} [Fact p.Prime]
    (hpodd : p ≠ 2) (a b : ZMod p) (hab : a ^ 2 + b ^ 2 = -1) :
    Function.Injective (quaternionToQdSL hpodd a b hab) := by
  have hn : orderOf (qi (p := p)) = 4 := qi_order hpodd
  have hpows {i j : ZMod 4}
      (h : (qi (p := p)) ^ i.val = qi ^ j.val) : i = j := by
    apply ZMod.val_injective
    exact pow_injOn_Iio_orderOf (x := qi (p := p))
      (by simpa [hn] using i.val_lt)
      (by simpa [hn] using j.val_lt) h
  rintro (i | i) (j | j) h
  · change qi ^ i.val = qi ^ j.val at h
    congr 1
    exact hpows h
  · exfalso
    change qi ^ i.val = qj a b hab * qi ^ j.val at h
    apply qj_not_mem_zpowers_qi hpodd a b hab
    rw [Subgroup.mem_zpowers_iff]
    refine ⟨(i.val : ℤ) - (j.val : ℤ), ?_⟩
    calc
      qi ^ ((i.val : ℤ) - (j.val : ℤ)) =
          qi ^ (i.val : ℤ) * qi ^ (-(j.val : ℤ)) := by
        rw [sub_eq_add_neg, zpow_add]
      _ = qi ^ i.val * (qi ^ j.val)⁻¹ := by
        rw [zpow_natCast, zpow_neg, zpow_natCast]
      _ = (qj a b hab * qi ^ j.val) * (qi ^ j.val)⁻¹ := by rw [h]
      _ = qj a b hab := by group
  · exfalso
    change qj a b hab * qi ^ i.val = qi ^ j.val at h
    apply qj_not_mem_zpowers_qi hpodd a b hab
    rw [Subgroup.mem_zpowers_iff]
    refine ⟨(j.val : ℤ) - (i.val : ℤ), ?_⟩
    calc
      qi ^ ((j.val : ℤ) - (i.val : ℤ)) =
          qi ^ (j.val : ℤ) * qi ^ (-(i.val : ℤ)) := by
        rw [sub_eq_add_neg, zpow_add]
      _ = qi ^ j.val * (qi ^ i.val)⁻¹ := by
        rw [zpow_natCast, zpow_neg, zpow_natCast]
      _ = (qj a b hab * qi ^ i.val) * (qi ^ i.val)⁻¹ := by rw [h]
      _ = qj a b hab := by group
  · change qj a b hab * qi ^ i.val = qj a b hab * qi ^ j.val at h
    congr 1
    apply hpows
    exact mul_left_cancel h

private lemma quaternionGroupTwo_not_isMulCommutative :
    ¬ IsMulCommutative (QuaternionGroup 2) := by
  intro h
  let : IsMulCommutative (QuaternionGroup 2) := h
  have hcomm := (IsMulCommutative.is_comm
    (M := QuaternionGroup 2)).comm
      (QuaternionGroup.a 1 : QuaternionGroup 2)
      (QuaternionGroup.xa 0 : QuaternionGroup 2)
  simp only [QuaternionGroup.a_mul_xa, QuaternionGroup.xa_mul_a] at hcomm
  have hbad := QuaternionGroup.xa.inj hcomm
  exact (by decide : (-(1 : ZMod 4)) ≠ 1) hbad

private lemma quaternionGroupTwo_not_isCyclic :
    ¬ IsCyclic (QuaternionGroup 2) := by
  intro h
  exact quaternionGroupTwo_not_isMulCommutative h.isMulCommutative

private lemma quaternionGroupTwo_eq_a_two_of_involution
    {x : QuaternionGroup 2} (hx : GorensteinWalter.IsInvolution x) :
    x = QuaternionGroup.a (2 : ZMod 4) := by
  cases x with
  | xa i =>
      have horder : orderOf (QuaternionGroup.xa i : QuaternionGroup 2) = 2 :=
        orderOf_eq_prime hx.2 hx.1
      rw [QuaternionGroup.orderOf_xa] at horder
      norm_num at horder
  | a i =>
      have horder : orderOf (QuaternionGroup.a i : QuaternionGroup 2) = 2 :=
        orderOf_eq_prime hx.2 hx.1
      rw [QuaternionGroup.orderOf_a] at horder
      have hdiv_mul := Nat.div_mul_cancel (Nat.gcd_dvd_left 4 i.val)
      rw [horder] at hdiv_mul
      have hgcd : Nat.gcd 4 i.val = 2 := by omega
      have htwo_dvd : 2 ∣ i.val := by
        obtain ⟨c, hc⟩ := Nat.gcd_dvd_right 4 i.val
        exact ⟨c, by simpa [hgcd] using hc⟩
      obtain ⟨c, hc⟩ := htwo_dvd
      have hilt : i.val < 4 := ZMod.val_lt i
      have hine : i.val ≠ 0 := by
        intro hi0
        apply hx.1
        rw [QuaternionGroup.one_def]
        congr 1
        exact (ZMod.val_eq_zero i).mp hi0
      have hc1 : c = 1 := by omega
      congr 1
      apply ZMod.val_injective
      rw [hc, hc1]
      exact (ZMod.val_natCast_of_lt (n := 4) (a := 2) (by norm_num)).symm

private lemma quaternionGroupTwo_involution_unique
    (x y : QuaternionGroup 2) (hx : GorensteinWalter.IsInvolution x)
    (hy : GorensteinWalter.IsInvolution y) : x = y :=
  (quaternionGroupTwo_eq_a_two_of_involution hx).trans
    (quaternionGroupTwo_eq_a_two_of_involution hy).symm

private lemma quaternionGroupTwo_not_dihedral {k : ℕ} (hk : 1 ≤ k) :
    ¬ Nonempty (QuaternionGroup 2 ≃* DihedralGroup (2 ^ k)) := by
  rintro ⟨e⟩
  have : NeZero (2 ^ k) := ⟨pow_ne_zero k (by norm_num)⟩
  let s0 : DihedralGroup (2 ^ k) := DihedralGroup.sr 0
  let s1 : DihedralGroup (2 ^ k) := DihedralGroup.sr 1
  have hs0 : GorensteinWalter.IsInvolution s0 := by
    constructor
    · intro h
      change DihedralGroup.sr 0 = 1 at h
      rw [DihedralGroup.one_def] at h
      injection h
    · rw [pow_two]
      exact DihedralGroup.sr_mul_self 0
  have hs1 : GorensteinWalter.IsInvolution s1 := by
    constructor
    · intro h
      change DihedralGroup.sr 1 = 1 at h
      rw [DihedralGroup.one_def] at h
      injection h
    · rw [pow_two]
      exact DihedralGroup.sr_mul_self 1
  have hpre0 : GorensteinWalter.IsInvolution (e.symm s0) := by
    constructor
    · intro h
      apply hs0.1
      have := congrArg e h
      simpa using this
    · simpa using congrArg e.symm hs0.2
  have hpre1 : GorensteinWalter.IsInvolution (e.symm s1) := by
    constructor
    · intro h
      apply hs1.1
      have := congrArg e h
      simpa using this
    · simpa using congrArg e.symm hs1.2
  have heq : e.symm s0 = e.symm s1 :=
    quaternionGroupTwo_involution_unique _ _ hpre0 hpre1
  have hs01 : s0 = s1 := e.symm.injective heq
  have h01 : (0 : ZMod (2 ^ k)) = 1 := DihedralGroup.sr.inj hs01
  have hpow : 1 < 2 ^ k := Nat.one_lt_pow (by omega) (by omega)
  have : Fact (1 < 2 ^ k) := ⟨hpow⟩
  have hval := congrArg ZMod.val h01
  norm_num [ZMod.val_zero, ZMod.val_one] at hval

private lemma quaternionGroupTwo_isPGroup : IsPGroup 2 (QuaternionGroup 2) := by
  rw [IsPGroup.iff_card]
  refine ⟨3, ?_⟩
  norm_num [Nat.card_eq_fintype_card, QuaternionGroup.card]

private theorem qdSL_not_hasCyclicOrDihedralSylowTwo
    {p : ℕ} [Fact p.Prime] (hpodd : p ≠ 2) :
    ¬ GorensteinWalter.HasCyclicOrDihedralSylowTwo (qdSL p) := by
  intro hSylow
  obtain ⟨a, b, hab⟩ := exists_qd_parameters (p := p)
  let φ : QuaternionGroup 2 →* qdSL p := quaternionToQdSL hpodd a b hab
  have hφinj : Function.Injective φ := by
    simpa [φ] using quaternionToQdSL_injective hpodd a b hab
  have hR : IsPGroup 2 φ.range :=
    quaternionGroupTwo_isPGroup.of_surjective φ.rangeRestrict
      φ.rangeRestrict_surjective
  obtain ⟨S, hRS⟩ := hR.exists_le_sylow
  have eφ : QuaternionGroup 2 ≃* φ.range :=
    MulEquiv.ofBijective φ.rangeRestrict
      ⟨fun _ _ hxy ↦ hφinj (congrArg Subtype.val hxy), φ.rangeRestrict_surjective⟩
  rcases hSylow S with hScyc | ⟨m, hm, ⟨eS⟩⟩
  · have : IsCyclic S := hScyc
    have hRcyc : IsCyclic φ.range := Subgroup.isCyclic_of_le hRS
    exact quaternionGroupTwo_not_isCyclic ((eφ.isCyclic).mpr hRcyc)
  · let Rsub : Subgroup S := φ.range.subgroupOf (S : Subgroup (qdSL p))
    let T : Subgroup (DihedralGroup (2 ^ m)) := Rsub.map eS.toMonoidHom
    have eRS : φ.range ≃* Rsub := by
      simpa [Rsub] using (Subgroup.subgroupOfEquivOfLe hRS).symm
    have eRT : Rsub ≃* T := by
      simpa [T] using
        (Subgroup.equivMapOfInjective Rsub eS.toMonoidHom eS.injective)
    let eQT : QuaternionGroup 2 ≃* T := eφ.trans (eRS.trans eRT)
    rcases GorensteinWalter.subgroups_dihedral_twoGroup_cyclic_or_dihedral hm T with
      hTcyc | ⟨k, hk, ⟨eTk⟩⟩
    · exact quaternionGroupTwo_not_isCyclic ((eQT.isCyclic).mpr hTcyc)
    · exact quaternionGroupTwo_not_dihedral hk ⟨eQT.trans eTk⟩

private theorem hasCyclicOrDihedralSylowTwo_subgroup
    {G : Type*} [Group G] [Finite G]
    (hG : GorensteinWalter.HasDihedralSylowTwo G) (K : Subgroup G) :
    GorensteinWalter.HasCyclicOrDihedralSylowTwo K := by
  intro S
  rcases Sylow.exists_comap_subtype_eq S with ⟨Q, hQ⟩
  rcases hG Q with ⟨m, hm, ⟨eQ⟩⟩
  have hSleQ : (S : Subgroup K).map K.subtype ≤ (Q : Subgroup G) := by
    rw [← hQ]
    exact Subgroup.map_comap_le K.subtype Q
  let S' : Subgroup G := (S : Subgroup K).map K.subtype
  let S'' : Subgroup (DihedralGroup (2 ^ m)) :=
    (S'.subgroupOf (Q : Subgroup G)).map eQ.toMonoidHom
  have eSS' : S ≃* S' := by
    simpa [S'] using
      (Subgroup.equivMapOfInjective (S : Subgroup K) K.subtype
        Subtype.coe_injective)
  have eS'Q : S' ≃* S'.subgroupOf (Q : Subgroup G) :=
    (Subgroup.subgroupOfEquivOfLe hSleQ).symm
  have eQS'' : S'.subgroupOf (Q : Subgroup G) ≃* S'' := by
    simpa [S''] using
      (Subgroup.equivMapOfInjective (S'.subgroupOf (Q : Subgroup G))
        eQ.toMonoidHom eQ.injective)
  let e : S ≃* S'' := eSS'.trans (eS'Q.trans eQS'')
  rcases GorensteinWalter.subgroups_dihedral_twoGroup_cyclic_or_dihedral hm S'' with
    hcyc | ⟨k, hk, ⟨ek⟩⟩
  · exact Or.inl ((e.isCyclic).mpr hcyc)
  · exact Or.inr ⟨k, hk, ⟨e.trans ek⟩⟩


private lemma dihedralGroup_cases_probe {n : ℕ} (x : DihedralGroup n) :
    (∃ i : ZMod n, x = DihedralGroup.r i) ∨
      ∃ i : ZMod n, x = DihedralGroup.sr i := by
  cases x with
  | r i => exact Or.inl ⟨i, rfl⟩
  | sr i => exact Or.inr ⟨i, rfl⟩

private lemma r_mem_zpowers_r_one_probe {n : ℕ} [NeZero n] (i : ZMod n) :
    DihedralGroup.r i ∈
      Subgroup.zpowers (DihedralGroup.r 1 : DihedralGroup n) := by
  refine ⟨i.val, ?_⟩
  change (DihedralGroup.r 1 : DihedralGroup n) ^ i.val = DihedralGroup.r i
  rw [DihedralGroup.r_one_pow]
  congr 1
  exact ZMod.natCast_zmod_val i

private lemma dihedral_two_group_generated_probe {m : ℕ} :
    Subgroup.zpowers (DihedralGroup.r 1 : DihedralGroup (2 ^ m)) ⊔
      Subgroup.zpowers (DihedralGroup.sr 1 : DihedralGroup (2 ^ m)) = ⊤ := by
  let : NeZero (2 ^ m) := ⟨pow_ne_zero m (by norm_num : 2 ≠ 0)⟩
  apply le_antisymm
  · exact le_top
  · intro x hx
    rcases dihedralGroup_cases_probe x with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · exact (le_sup_left :
          Subgroup.zpowers (DihedralGroup.r 1) ≤
            Subgroup.zpowers (DihedralGroup.r 1) ⊔
              Subgroup.zpowers (DihedralGroup.sr 1))
        (r_mem_zpowers_r_one_probe i)
    · have hsr : DihedralGroup.sr i =
          DihedralGroup.sr 1 * DihedralGroup.r (i - 1) := by
        rw [DihedralGroup.sr_mul_r]
        congr 1
        rw [sub_eq_add_neg]
        abel
      rw [hsr]
      exact Subgroup.mul_mem
        (Subgroup.zpowers (DihedralGroup.r 1) ⊔
          Subgroup.zpowers (DihedralGroup.sr 1))
        ((le_sup_right :
            Subgroup.zpowers (DihedralGroup.sr 1) ≤
              Subgroup.zpowers (DihedralGroup.r 1) ⊔
                Subgroup.zpowers (DihedralGroup.sr 1))
          (Subgroup.mem_zpowers (DihedralGroup.sr 1)))
        ((le_sup_left :
            Subgroup.zpowers (DihedralGroup.r 1) ≤
              Subgroup.zpowers (DihedralGroup.r 1) ⊔
                Subgroup.zpowers (DihedralGroup.sr 1))
          (r_mem_zpowers_r_one_probe (i - 1)))

private theorem cyclic_or_dihedral_of_surjective_dihedral_twoGroup
    {H : Type*} [Group H] [Finite H] {m : ℕ} (_hm : 1 ≤ m)
    (f : DihedralGroup (2 ^ m) →* H) (hf : Function.Surjective f)
    (hH : IsPGroup 2 H) :
    IsCyclic H ∨ ∃ k : ℕ, 1 ≤ k ∧ Nonempty (H ≃* DihedralGroup (2 ^ k)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let ρ : H := f (DihedralGroup.r 1)
  let σ : H := f (DihedralGroup.sr 1)
  have hσ2 : σ ^ 2 = 1 := by
    have hs : (DihedralGroup.sr 1 : DihedralGroup (2 ^ m)) ^ 2 = 1 := by
      rw [pow_two]
      exact DihedralGroup.sr_mul_self 1
    simpa [σ, map_pow] using congrArg f hs
  have hrelD :
      (DihedralGroup.sr 1 : DihedralGroup (2 ^ m)) * DihedralGroup.r 1 *
          (DihedralGroup.sr 1)⁻¹ = (DihedralGroup.r 1)⁻¹ := by
    calc
      (DihedralGroup.sr 1 : DihedralGroup (2 ^ m)) * DihedralGroup.r 1 *
          (DihedralGroup.sr 1)⁻¹ =
          DihedralGroup.sr (1 + 1) * (DihedralGroup.sr 1)⁻¹ := by
            rw [DihedralGroup.sr_mul_r]
      _ = DihedralGroup.sr (1 + 1) * DihedralGroup.sr 1 := by
            rw [DihedralGroup.inv_sr]
      _ = DihedralGroup.r (1 - (1 + 1)) := by
            rw [DihedralGroup.sr_mul_sr]
      _ = DihedralGroup.r (-1) := by congr 1; abel
      _ = (DihedralGroup.r 1)⁻¹ := by rw [DihedralGroup.inv_r]
  have hrel : σ * ρ * σ⁻¹ = ρ⁻¹ := by
    calc
      σ * ρ * σ⁻¹ =
          f ((DihedralGroup.sr 1 : DihedralGroup (2 ^ m)) *
              DihedralGroup.r 1) * f ((DihedralGroup.sr 1)⁻¹) := by
            rw [map_mul, map_inv]
      _ = f ((DihedralGroup.sr 1 : DihedralGroup (2 ^ m)) *
            DihedralGroup.r 1 * (DihedralGroup.sr 1)⁻¹) :=
        (map_mul f _ _).symm
      _ = f ((DihedralGroup.r 1 : DihedralGroup (2 ^ m))⁻¹) :=
        congrArg f hrelD
      _ = (f (DihedralGroup.r 1))⁻¹ := map_inv f _
      _ = ρ⁻¹ := rfl
  have hgen : ⊤ = Subgroup.zpowers ρ ⊔ Subgroup.zpowers σ := by
    apply le_antisymm
    · intro x hx
      obtain ⟨y, rfl⟩ := hf x
      have hy : y ∈
          Subgroup.zpowers (DihedralGroup.r 1 : DihedralGroup (2 ^ m)) ⊔
            Subgroup.zpowers (DihedralGroup.sr 1 : DihedralGroup (2 ^ m)) := by
        rw [dihedral_two_group_generated_probe]
        trivial
      have hfy : f y ∈
          (Subgroup.zpowers (DihedralGroup.r 1 : DihedralGroup (2 ^ m)) ⊔
            Subgroup.zpowers (DihedralGroup.sr 1 : DihedralGroup (2 ^ m))).map f :=
        (Subgroup.mem_map).mpr ⟨y, hy, rfl⟩
      simpa [ρ, σ, Subgroup.map_sup, MonoidHom.map_zpowers] using hfy
    · exact le_top
  rcases GorensteinWalter.isCyclic_or_dihedral_of_generators ρ σ hgen hσ2 hrel with
    hcyc | hdih
  · exact Or.inl hcyc
  · obtain ⟨k, hkorder⟩ := (IsPGroup.iff_orderOf.mp hH) ρ
    by_cases hk0 : k = 0
    · left
      have hcyc1 : IsCyclic (DihedralGroup 1) :=
        isCyclic_of_prime_card (p := 2) (by rw [DihedralGroup.nat_card])
      have e1 : Nonempty (H ≃* DihedralGroup 1) := by
        rw [hkorder, hk0, pow_zero] at hdih
        exact hdih
      exact (e1.some.isCyclic).mpr hcyc1
    · right
      refine ⟨k, Nat.one_le_iff_ne_zero.mpr hk0, ?_⟩
      rw [hkorder] at hdih
      exact hdih

private theorem hasCyclicOrDihedralSylowTwo_mapSurjective
    {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]
    (hG : GorensteinWalter.HasCyclicOrDihedralSylowTwo G)
    (f : G →* H) (hf : Function.Surjective f) :
    GorensteinWalter.HasCyclicOrDihedralSylowTwo H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro S
  rcases Sylow.mapSurjective_surjective (p := 2) (f := f) hf S with ⟨Q, hQ⟩
  have hSm : (Q : Subgroup G).map f = (S : Subgroup H) := by
    rw [← Sylow.coe_mapSurjective hf Q]
    exact congrArg (fun X : Sylow 2 H ↦ (X : Subgroup H)) hQ
  let eMapS : ((Q : Subgroup G).map f) ≃* S :=
    MulEquiv.subgroupCongr hSm
  let g : Q →* S :=
    eMapS.toMonoidHom.comp (f.subgroupMap (Q : Subgroup G))
  have hg : Function.Surjective g :=
    eMapS.surjective.comp (MonoidHom.subgroupMap_surjective f (Q : Subgroup G))
  rcases hG Q with hQcyc | ⟨m, hm, ⟨eQ⟩⟩
  · have : IsCyclic Q := hQcyc
    exact Or.inl (isCyclic_of_surjective g hg)
  · let gD : DihedralGroup (2 ^ m) →* S :=
      g.comp eQ.symm.toMonoidHom
    have hgD : Function.Surjective gD := hg.comp eQ.symm.surjective
    exact cyclic_or_dihedral_of_surjective_dihedral_twoGroup hm gD hgD S.isPGroup'

public theorem qdSL_not_involved_of_hasDihedralSylowTwo
    {G : Type*} [Group G] [Finite G]
    (hG : GorensteinWalter.HasDihedralSylowTwo G)
    {p : ℕ} [Fact p.Prime] (hpodd : p ≠ 2) :
    ¬ Glauberman.Involved (qdSL p) G := by
  rintro ⟨K, N, hN, ⟨e⟩⟩
  let : N.Normal := hN
  have hK : GorensteinWalter.HasCyclicOrDihedralSylowTwo K :=
    hasCyclicOrDihedralSylowTwo_subgroup hG K
  have hKN := hasCyclicOrDihedralSylowTwo_mapSurjective hK
    (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)
  have hSL : GorensteinWalter.HasCyclicOrDihedralSylowTwo (qdSL p) :=
    GorensteinWalter.hasCyclicOrDihedralSylowTwo_of_mulEquiv e.symm hKN
  exact qdSL_not_hasCyclicOrDihedralSylowTwo hpodd hSL


end CFSG.GorensteinWalter
