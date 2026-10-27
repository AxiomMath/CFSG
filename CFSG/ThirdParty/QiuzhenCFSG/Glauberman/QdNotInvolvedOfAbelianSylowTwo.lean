module

public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.Definitions
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.Lemma6_3
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.QdSLPCore
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.QdSLNotInvolvedOfDihedralSylowTwo
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.GroupTheory.SpecificGroups.Quaternion

namespace CFSG
end CFSG
open CFSG

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

/-!
# `Qd(p)` is not involved in a group with Abelian Sylow 2-subgroups

For an odd prime `p`, `Qd(p) = V₂ ⋊ SL₂(p)` contains the special linear group
`SL₂(p)` as a subgroup.  For odd `p`, `SL₂(p)` contains an explicit quaternion
subgroup of order eight (the same explicit matrices used in
`GorensteinWalter/QdSLNotInvolvedOfDihedralSylowTwo.lean`).  Since Abelian Sylow
`2`-subgroups pass to subgroups and quotients, an involvement witness for `Qd(p)`
in a group with Abelian Sylow `2`-subgroups would make `SL₂(p)` a subquotient with
Abelian Sylow `2`-subgroups, contradicting the quaternion obstruction.

This is the independent source subnode used in the proof of Theorem D
(`refs/glauberman-p-stable.tex` L1979–L1981: "Since `p` is odd, `G` has an Abelian
Sylow `2`-subgroup. Hence `Qd(p)` is not involved in `G`.").  The public theorem
below is exactly the requested statement; all helpers are private.  No
`sorry`/`axiom`/`opaque`/compiled evaluation is used.
-/

open scoped MatrixGroups

namespace CFSG.Glauberman

universe u

/-! ## Explicit quaternion subgroup of `SL₂(p)` -/

/-- For every prime `p`, `ZMod p` contains `a,b` with `a² + b² = -1`. -/
private theorem exists_qd_parameters {p : ℕ} [Fact p.Prime] :
    ∃ a b : ZMod p, a ^ 2 + b ^ 2 = -1 := by
  rcases Nat.sq_add_sq_zmodEq p (-1) with ⟨a, b, _ha, _hb, hab⟩
  refine ⟨(a : ZMod p), (b : ZMod p), ?_⟩
  have hc := (ZMod.intCast_eq_intCast_iff
    ((a : ℤ) ^ 2 + (b : ℤ) ^ 2) (-1) p).2 hab
  simpa using hc

/-- The quaternion generator `i` in `SL₂(p)`. -/
private def qi {p : ℕ} [Fact p.Prime] : qdSL p :=
  ⟨!![(0 : ZMod p), -1; 1, 0], by
    simp [Matrix.det_fin_two_of]⟩

/-- The quaternion generator `j` in `SL₂(p)`. -/
private def qj {p : ℕ} [Fact p.Prime]
    (a b : ZMod p) (hab : a ^ 2 + b ^ 2 = -1) : qdSL p :=
  ⟨!![a, b; b, -a], by
    rw [Matrix.det_fin_two_of]
    calc
      a * -a - b * b = -(a ^ 2 + b ^ 2) := by ring
      _ = 1 := by rw [hab]; simp⟩

private lemma qi_sq {p : ℕ} [Fact p.Prime] :
    (qi (p := p)) ^ 2 = -(1 : qdSL p) := by
  apply Subtype.ext
  ext i j
  change ((!![(0 : ZMod p), -1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod p)) ^ 2) i j = _
  fin_cases i <;> fin_cases j <;>
    simp [qi, pow_two, Matrix.mul_apply, Fin.sum_univ_two]

private lemma qj_sq {p : ℕ} [Fact p.Prime]
    (a b : ZMod p) (hab : a ^ 2 + b ^ 2 = -1) :
    (qj a b hab) ^ 2 = -(1 : qdSL p) := by
  apply Subtype.ext
  ext i j
  change ((!![a, b; b, -a] : Matrix (Fin 2) (Fin 2) (ZMod p)) ^ 2) i j = _
  fin_cases i <;> fin_cases j <;>
    simp [qj, pow_two, Matrix.mul_apply, Fin.sum_univ_two] <;>
    ring_nf <;>
    simpa [pow_two, add_comm] using hab

private lemma qi_mul_qj {p : ℕ} [Fact p.Prime]
    (a b : ZMod p) (hab : a ^ 2 + b ^ 2 = -1) :
    qi * qj a b hab = -(qj a b hab * qi) := by
  apply Subtype.ext
  ext i j
  change ((!![(0 : ZMod p), -1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod p)) *
      (!![a, b; b, -a] : Matrix (Fin 2) (Fin 2) (ZMod p))) i j =
    -(((!![a, b; b, -a] : Matrix (Fin 2) (Fin 2) (ZMod p)) *
      (!![(0 : ZMod p), -1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod p))) i j)
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
  haveI : NeZero n := ⟨by rw [← hn]; exact (orderOf_pos ρ).ne'⟩
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
  haveI : NeZero n := ⟨by rw [← hn]; exact (orderOf_pos ρ).ne'⟩
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

/-- The quaternion subgroup of `SL₂(p)` used for odd `p`. -/
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
  letI : IsMulCommutative (QuaternionGroup 2) := h
  have hcomm := (IsMulCommutative.is_comm
    (M := QuaternionGroup 2)).comm
      (QuaternionGroup.a 1 : QuaternionGroup 2)
      (QuaternionGroup.xa 0 : QuaternionGroup 2)
  simp only [QuaternionGroup.a_mul_xa, QuaternionGroup.xa_mul_a] at hcomm
  have hbad := QuaternionGroup.xa.inj hcomm
  exact (by decide : (-(1 : ZMod 4)) ≠ 1) hbad

private lemma quaternionGroupTwo_isPGroup : IsPGroup 2 (QuaternionGroup 2) := by
  rw [IsPGroup.iff_card]
  refine ⟨3, ?_⟩
  norm_num [Nat.card_eq_fintype_card, QuaternionGroup.card]

/-! ## Abelian Sylow 2-subgroups obstruct the quaternion subgroup -/

/-- If `H` is involved in `G` and `G` has Abelian Sylow 2-subgroups, then so
does `H`. -/
private theorem hasAbelianSylow_of_involved
    {H : Type*} [Group H] [Finite H] {G : Type u} [Group G] [Finite G]
    (hG : ∀ T : Sylow 2 G, IsMulCommutative (T : Subgroup G))
    (hInv : Involved H G) :
    ∀ T : Sylow 2 H, IsMulCommutative (T : Subgroup H) := by
  classical
  rcases hInv with ⟨K, N, hN, ⟨e⟩⟩
  letI : N.Normal := hN
  have hK : ∀ P : Sylow 2 K, IsMulCommutative (P : Subgroup K) := by
    intro P
    obtain ⟨R, hRP⟩ := Sylow.exists_comap_subtype_eq P
    have hRcomm : IsMulCommutative (R : Subgroup G) := hG R
    rw [← hRP]
    exact Subgroup.comap_injective_isMulCommutative
      (H := (R : Subgroup G)) K.subtype_injective
  have hKN : ∀ Q : Sylow 2 (K ⧸ N),
      IsMulCommutative (Q : Subgroup (K ⧸ N)) := by
    intro Q
    obtain ⟨P, hPQ⟩ := Sylow.mapSurjective_surjective
      (f := QuotientGroup.mk' N) (hf := QuotientGroup.mk'_surjective N) 2 Q
    letI : IsMulCommutative (P : Subgroup K) := hK P
    rw [← hPQ]
    exact Subgroup.map_isMulCommutative (P : Subgroup K) (QuotientGroup.mk' N)
  intro T
  obtain ⟨Q, hQT⟩ := Sylow.mapSurjective_surjective
    (f := e.toMonoidHom) (hf := e.surjective) 2 T
  letI : IsMulCommutative (Q : Subgroup (K ⧸ N)) := hKN Q
  rw [← hQT]
  exact Subgroup.map_isMulCommutative (Q : Subgroup (K ⧸ N)) e.toMonoidHom

/-- A subgroup of an Abelian subgroup is Abelian. -/
private theorem isMulCommutative_of_le_local {G : Type*} [Group G]
    {A P : Subgroup G} (hPcomm : IsMulCommutative P) (hAP : A ≤ P) :
    IsMulCommutative A := by
  refine (Subgroup.le_centralizer_iff_isMulCommutative (K := A)).1 ?_
  have hPcent : P ≤ Subgroup.centralizer (P : Set G) :=
    (Subgroup.le_centralizer_iff_isMulCommutative (K := P)).2 hPcomm
  have hAcentP : A ≤ Subgroup.centralizer (P : Set G) := hAP.trans hPcent
  have hCge : Subgroup.centralizer (P : Set G) ≤ Subgroup.centralizer (A : Set G) :=
    Subgroup.centralizer_le (show (A : Set G) ⊆ (P : Set G) from hAP)
  exact hAcentP.trans hCge

/-- For odd `p`, `SL₂(p)` has a non-Abelian Sylow 2-subgroup. -/
private theorem qdSL_not_hasAbelianSylowTwo
    {p : ℕ} [Fact p.Prime] (hpodd : p ≠ 2) :
    ¬ ∀ S : Sylow 2 (qdSL p), IsMulCommutative (S : Subgroup (qdSL p)) := by
  intro hSylow
  obtain ⟨a, b, hab⟩ := exists_qd_parameters (p := p)
  let φ : QuaternionGroup 2 →* qdSL p := quaternionToQdSL hpodd a b hab
  have hφinj : Function.Injective φ := quaternionToQdSL_injective hpodd a b hab
  have hR : IsPGroup 2 φ.range :=
    quaternionGroupTwo_isPGroup.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
  obtain ⟨P, hRangeLe⟩ := hR.exists_le_sylow
  have hRcomm : IsMulCommutative φ.range :=
    isMulCommutative_of_le_local (hSylow P) hRangeLe
  let eφ : QuaternionGroup 2 ≃* φ.range :=
    MulEquiv.ofBijective φ.rangeRestrict
      ⟨(fun _ _ hxy => hφinj (congrArg Subtype.val hxy)), φ.rangeRestrict_surjective⟩
  letI : IsMulCommutative φ.range := hRcomm
  have hQcomm : IsMulCommutative (QuaternionGroup 2) := by
    refine ⟨⟨fun x y => ?_⟩⟩
    apply eφ.injective
    rw [map_mul, map_mul]
    exact hRcomm.is_comm.comm (eφ x) (eφ y)
  exact quaternionGroupTwo_not_isMulCommutative hQcomm

/-! ## The public theorem -/

/-- If `p` is odd and every Sylow `2`-subgroup of the finite group `G` is
Abelian, then `Qd(p)` is not involved in `G`. -/
public theorem qd_not_involved_of_abelian_sylow_two {p : ℕ} [Fact p.Prime]
    (hpodd : p ≠ 2) {G : Type u} [Group G] [Finite G]
    (hSylow : ∀ T : Sylow 2 G, IsMulCommutative (T : Subgroup G)) :
    ¬ Involved (Qd p) G := by
  intro hQd
  rcases hQd with ⟨K, N, hN, ⟨e⟩⟩
  letI : N.Normal := hN
  let L : Subgroup (Qd p) :=
    (SemidirectProduct.inr : qdSL p →* Qd p).range
  let eSL : qdSL p ≃* L :=
    MulEquiv.ofBijective
      (SemidirectProduct.inr : qdSL p →* Qd p).rangeRestrict
      ⟨(fun _ _ hxy ↦
        SemidirectProduct.inr_injective (congrArg Subtype.val hxy)),
        (SemidirectProduct.inr : qdSL p →* Qd p).rangeRestrict_surjective⟩
  let L' : Subgroup (K ⧸ N) := L.map e.symm.toMonoidHom
  let eL : L ≃* L' :=
    Subgroup.equivMapOfInjective L e.symm.toMonoidHom e.symm.injective
  have hL' : Involved L' (K ⧸ N) := involved_of_subgroup L'
  have hSLquot : Involved (qdSL p) (K ⧸ N) :=
    (Involved_iff_of_mulEquiv (eSL.trans eL)).mpr hL'
  have hKN : ∀ T : Sylow 2 (K ⧸ N),
      IsMulCommutative (T : Subgroup (K ⧸ N)) := by
    intro T
    obtain ⟨Q, hQT⟩ := Sylow.mapSurjective_surjective
      (f := QuotientGroup.mk' N) (hf := QuotientGroup.mk'_surjective N) 2 T
    obtain ⟨P, hQP⟩ := Sylow.exists_comap_subtype_eq Q
    have hPcomm : IsMulCommutative (P : Subgroup G) := hSylow P
    have hQcomm : IsMulCommutative (Q : Subgroup K) := by
      rw [← hQP]
      exact Subgroup.comap_injective_isMulCommutative
        (H := (P : Subgroup G)) K.subtype_injective
    letI : IsMulCommutative (Q : Subgroup K) := hQcomm
    rw [← hQT]
    exact Subgroup.map_isMulCommutative (Q : Subgroup K) (QuotientGroup.mk' N)
  have hSLabel : ∀ S : Sylow 2 (qdSL p),
      IsMulCommutative (S : Subgroup (qdSL p)) :=
    hasAbelianSylow_of_involved hKN hSLquot
  exact qdSL_not_hasAbelianSylowTwo hpodd hSLabel


end CFSG.Glauberman
