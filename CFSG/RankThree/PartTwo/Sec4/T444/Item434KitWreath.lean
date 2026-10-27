module

public import CFSG.Assembly.Defs
import CFSG.RankThree.PartTwo.Sec5.Tools

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item434Kit

open Subgroup
open scoped Pointwise

variable {H : Type*} [Group H]

@[expose] def vecElt (z : Fin 3 → H) (v : Fin 3 → ZMod 3) : H :=
  z 0 ^ (v 0).val * z 1 ^ (v 1).val * z 2 ^ (v 2).val

structure WreathFacts (z : Fin 3 → H) (t : H) : Prop where
  pow_z : ∀ i, z i ^ 3 = 1
  comm_z : ∀ i j, z i * z j = z j * z i
  inj : ∀ v, vecElt z v = 1 → v = 0
  pow_t : t ^ 3 = 1
  conj0 : t * z 0 * t⁻¹ = z 1
  conj1 : t * z 1 * t⁻¹ = z 2
  conj2 : t * z 2 * t⁻¹ = z 0
  t_ne : ∀ v, vecElt z v ≠ t

@[expose] def baseA (z : Fin 3 → H) : Subgroup H :=
  zpowers (z 0) ⊔ zpowers (z 1) ⊔ zpowers (z 2)

@[expose] def wreathW (z : Fin 3 → H) (t : H) : Subgroup H :=
  baseA z ⊔ zpowers t

section Base

variable {z : Fin 3 → H} {t : H}

theorem pow_val_add {x : H} (hx : x ^ 3 = 1) (a b : ZMod 3) :
    x ^ (a + b).val = x ^ a.val * x ^ b.val := by
  rw [← pow_add, ZMod.val_add]
  conv_rhs => rw [← Nat.mod_add_div (a.val + b.val) 3]
  rw [pow_add, pow_mul, hx, one_pow, mul_one]

theorem commute_pow (hf : WreathFacts z t) (i j : Fin 3) (m n : ℕ) :
    Commute (z i ^ m) (z j ^ n) :=
  Commute.pow_pow (hf.comm_z i j) m n

theorem vecElt_add (hf : WreathFacts z t) (v w : Fin 3 → ZMod 3) :
    vecElt z (v + w) = vecElt z v * vecElt z w := by
  simp only [vecElt, Pi.add_apply, pow_val_add (hf.pow_z _)]
  set p0 := z 0 ^ (v 0).val
  set p1 := z 1 ^ (v 1).val
  set p2 := z 2 ^ (v 2).val
  set q0 := z 0 ^ (w 0).val
  set q1 := z 1 ^ (w 1).val
  set q2 := z 2 ^ (w 2).val
  have h01 : q0 * p1 = p1 * q0 := (commute_pow hf 0 1 _ _).eq
  have h02 : q0 * p2 = p2 * q0 := (commute_pow hf 0 2 _ _).eq
  have h12 : q1 * p2 = p2 * q1 := (commute_pow hf 1 2 _ _).eq
  calc p0 * q0 * (p1 * q1) * (p2 * q2) = p0 * (q0 * p1) * q1 * p2 * q2 := by group
    _ = p0 * p1 * q0 * (q1 * p2) * q2 := by rw [h01]; group
    _ = p0 * p1 * (q0 * p2) * q1 * q2 := by rw [h12]; group
    _ = p0 * p1 * p2 * (q0 * q1 * q2) := by rw [h02]; group

@[expose] def vecHom (hf : WreathFacts z t) : Multiplicative (Fin 3 → ZMod 3) →* H where
  toFun v := vecElt z (Multiplicative.toAdd v)
  map_one' := by simp [vecElt]
  map_mul' u v := vecElt_add hf _ _

theorem vecHom_apply (hf : WreathFacts z t) (v : Multiplicative (Fin 3 → ZMod 3)) :
    vecHom hf v = vecElt z (Multiplicative.toAdd v) :=
  rfl

theorem vecHom_injective (hf : WreathFacts z t) : Function.Injective (vecHom hf) := by
  rw [injective_iff_map_eq_one]
  intro v hv
  exact Multiplicative.toAdd.injective (hf.inj _ hv)

theorem vecElt_injective (hf : WreathFacts z t) {v w : Fin 3 → ZMod 3}
    (h : vecElt z v = vecElt z w) : v = w :=
  Multiplicative.ofAdd.injective (vecHom_injective hf h)

theorem vecElt_single (i : Fin 3) (a : ZMod 3) : vecElt z (Pi.single i a) = z i ^ a.val := by
  fin_cases i <;> simp [vecElt]

theorem vecElt_single_one (i : Fin 3) : vecElt z (Pi.single i 1) = z i := by
  rw [vecElt_single, ZMod.val_one, pow_one]

theorem baseA_eq_range (hf : WreathFacts z t) : baseA z = (vecHom hf).range := by
  apply le_antisymm
  · have hz : ∀ i, z i ∈ (vecHom hf).range := fun i =>
      ⟨Multiplicative.ofAdd (Pi.single i 1), vecElt_single_one i⟩
    exact sup_le (sup_le (zpowers_le.mpr (hz 0)) (zpowers_le.mpr (hz 1))) (zpowers_le.mpr (hz 2))
  · rintro _ ⟨v, rfl⟩
    exact mul_mem (mul_mem (pow_mem (mem_sup_left (mem_sup_left (mem_zpowers _))) _)
      (pow_mem (mem_sup_left (mem_sup_right (mem_zpowers _))) _))
      (pow_mem (mem_sup_right (mem_zpowers _)) _)

theorem mem_baseA_iff (hf : WreathFacts z t) {x : H} : x ∈ baseA z ↔ ∃ v, vecElt z v = x := by
  rw [baseA_eq_range hf]
  exact ⟨fun ⟨v, hv⟩ => ⟨_, hv⟩, fun ⟨v, hv⟩ => ⟨Multiplicative.ofAdd v, hv⟩⟩

theorem vecElt_mem_baseA (hf : WreathFacts z t) (v : Fin 3 → ZMod 3) : vecElt z v ∈ baseA z :=
  (mem_baseA_iff hf).mpr ⟨v, rfl⟩

theorem z_mem_baseA (i : Fin 3) : z i ∈ baseA z := by
  fin_cases i
  · exact mem_sup_left (mem_sup_left (mem_zpowers _))
  · exact mem_sup_left (mem_sup_right (mem_zpowers _))
  · exact mem_sup_right (mem_zpowers _)

theorem card_baseA (hf : WreathFacts z t) : Nat.card (baseA z) = 27 := by
  rw [baseA_eq_range hf, ← Nat.card_congr (MonoidHom.ofInjective (vecHom_injective hf)).toEquiv,
    Nat.card_congr Multiplicative.toAdd, Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card,
    Fintype.card_fin]
  norm_num

theorem isElemAbelian_baseA (hf : WreathFacts z t) : CFSG.Assembly.IsElemAbelian 3 (baseA z) := by
  rw [baseA_eq_range hf]
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, ?_⟩
  · obtain ⟨_, ⟨u, rfl⟩⟩ := a
    obtain ⟨_, ⟨v, rfl⟩⟩ := b
    change vecHom hf u * vecHom hf v = vecHom hf v * vecHom hf u
    rw [← map_mul, ← map_mul, mul_comm]
  · rintro _ ⟨u, rfl⟩
    rw [← map_pow]
    have : u ^ 3 = 1 := by
      apply Multiplicative.toAdd.injective
      ext i
      simp only [toAdd_pow, toAdd_one, Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul]
      rw [show ((3 : ℕ) : ZMod 3) = 0 from rfl, zero_mul]
    rw [this, map_one]

theorem isPGroup_baseA (hf : WreathFacts z t) : IsPGroup 3 (baseA z) :=
  IsPGroup.of_card (n := 3) (by rw [card_baseA hf]; norm_num)

theorem z_ne_one (hf : WreathFacts z t) (i : Fin 3) : z i ≠ 1 := by
  intro h
  have h1 := hf.inj (Pi.single i 1) (by rw [vecElt_single_one, h])
  have := congrFun h1 i
  simp at this

theorem orderOf_z (hf : WreathFacts z t) (i : Fin 3) : orderOf (z i) = 3 :=
  orderOf_eq_prime (hf.pow_z i) (z_ne_one hf i)

theorem z_notMem_zpowers (hf : WreathFacts z t) {i j : Fin 3} (hij : i ≠ j) :
    z j ∉ zpowers (z i) := by
  intro hmem
  obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hmem
  have hk' : z i ^ ((k : ZMod 3).val) = z j := by
    rw [← zpow_natCast, ZMod.val_intCast, ← hk]
    have h3 := zpow_mod_orderOf (z i) k
    rwa [orderOf_z hf i] at h3
  have h1 : vecElt z (Pi.single i (k : ZMod 3)) = vecElt z (Pi.single j 1) := by
    rw [vecElt_single, vecElt_single_one, hk']
  have h2 := congrFun (vecElt_injective hf h1) j
  simp [hij.symm] at h2

theorem isElemAbelian_sup_zpowers [Finite H] (hf : WreathFacts z t) {i j : Fin 3} (hij : i ≠ j) :
    CFSG.Assembly.IsElemAbelian 3 (zpowers (z i) ⊔ zpowers (z j)) ∧
      Nat.card (zpowers (z i) ⊔ zpowers (z j) : Subgroup H) = 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hzi : CFSG.Assembly.IsElemAbelian 3 (zpowers (z i)) := by
    refine ⟨inferInstance, fun x hx => ?_⟩
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hx
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hf.pow_z, one_zpow]
  have hcomm : ∀ a ∈ zpowers (z i), a * z j = z j * a := by
    intro a ha
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp ha
    exact (Commute.zpow_left (hf.comm_z i j) k).eq
  obtain ⟨hab, hcard⟩ := CFSG.RankThree.PartTwo.Sec5.isElemAbelian_sup_zpowers hzi
    (z_notMem_zpowers hf hij) (hf.pow_z j) hcomm
  refine ⟨hab, ?_⟩
  rw [hcard, Nat.card_zpowers, orderOf_z hf i]

theorem sup_zpowers_le_baseA (i j : Fin 3) : zpowers (z i) ⊔ zpowers (z j) ≤ baseA z :=
  sup_le (zpowers_le.mpr (z_mem_baseA i)) (zpowers_le.mpr (z_mem_baseA j))

theorem vecElt_mem_zpowers_of_const (hf : WreathFacts z t) {u : Fin 3 → ZMod 3}
    (h01 : u 0 = u 1) (h12 : u 1 = u 2) : vecElt z u ∈ zpowers (vecElt z ![1, 1, 1]) := by
  have hu : Multiplicative.ofAdd u = (Multiplicative.ofAdd ![1, 1, 1]) ^ (u 0).val := by
    apply Multiplicative.toAdd.injective
    ext i
    fin_cases i <;> simp [h01, h12]
  have h := congrArg (vecHom hf) hu
  rw [map_pow] at h
  change vecElt z u = vecElt z ![1, 1, 1] ^ (u 0).val at h
  rw [h]
  exact pow_mem (mem_zpowers _) _

end Base

section Top

variable {z : Fin 3 → H} {t : H}

theorem conj_vecElt (hf : WreathFacts z t) (v : Fin 3 → ZMod 3) :
    t * vecElt z v * t⁻¹ = vecElt z ![v 2, v 0, v 1] := by
  have hc : ∀ x : H, t * x * t⁻¹ = MulAut.conj t x := fun x => rfl
  rw [hc, vecElt, map_mul, map_mul, map_pow, map_pow, map_pow, ← hc, ← hc, ← hc, hf.conj0,
    hf.conj1, hf.conj2, vecElt]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  have h1 : z 2 ^ (v 1).val * z 0 ^ (v 2).val = z 0 ^ (v 2).val * z 2 ^ (v 1).val :=
    (commute_pow hf 2 0 _ _).eq
  have h2 : z 1 ^ (v 0).val * z 0 ^ (v 2).val = z 0 ^ (v 2).val * z 1 ^ (v 0).val :=
    (commute_pow hf 1 0 _ _).eq
  calc z 1 ^ (v 0).val * z 2 ^ (v 1).val * z 0 ^ (v 2).val =
      z 1 ^ (v 0).val * (z 2 ^ (v 1).val * z 0 ^ (v 2).val) := by group
    _ = z 1 ^ (v 0).val * z 0 ^ (v 2).val * z 2 ^ (v 1).val := by rw [h1]; group
    _ = z 0 ^ (v 2).val * z 1 ^ (v 0).val * z 2 ^ (v 1).val := by rw [h2]

theorem conj_t_mem_baseA (hf : WreathFacts z t) {x : H} (hx : x ∈ baseA z) :
    t * x * t⁻¹ ∈ baseA z := by
  obtain ⟨v, rfl⟩ := (mem_baseA_iff hf).mp hx
  rw [conj_vecElt hf]
  exact vecElt_mem_baseA hf _

theorem t_mem_normalizer (hf : WreathFacts z t) : t ∈ normalizer (baseA z : Set H) := by
  rw [mem_normalizer_iff]
  intro x
  refine ⟨conj_t_mem_baseA hf, fun hx => ?_⟩
  have h2 := conj_t_mem_baseA hf (conj_t_mem_baseA hf hx)
  have ht3 : t * t * t = 1 := by rw [← pow_three', hf.pow_t]
  have h3 : t * (t * (t * x * t⁻¹) * t⁻¹) * t⁻¹ = x := by
    calc t * (t * (t * x * t⁻¹) * t⁻¹) * t⁻¹ = (t * t * t) * x * (t * t * t)⁻¹ := by group
      _ = x := by rw [ht3, one_mul, inv_one, mul_one]
  rw [← h3]
  exact h2

theorem zpowers_t_le_normalizer (hf : WreathFacts z t) :
    zpowers t ≤ normalizer (baseA z : Set H) :=
  zpowers_le.mpr (t_mem_normalizer hf)

theorem t_ne_one (hf : WreathFacts z t) : t ≠ 1 := by
  intro h
  apply hf.t_ne 0
  rw [h]
  simp [vecElt]

theorem orderOf_t (hf : WreathFacts z t) : orderOf t = 3 :=
  orderOf_eq_prime hf.pow_t (t_ne_one hf)

theorem t_notMem_baseA (hf : WreathFacts z t) : t ∉ baseA z := by
  rw [mem_baseA_iff hf]
  rintro ⟨v, hv⟩
  exact hf.t_ne v hv

theorem t_mem_wreathW : t ∈ wreathW z t := mem_sup_right (mem_zpowers _)

theorem isPGroup_wreathW (hf : WreathFacts z t) : IsPGroup 3 (wreathW z t) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact IsPGroup.to_sup_of_normal_left' (isPGroup_baseA hf)
    (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, orderOf_t hf, pow_one]))
    (zpowers_t_le_normalizer hf)

theorem mem_wreathW (hf : WreathFacts z t) {x : H} (hx : x ∈ wreathW z t) :
    ∃ (v : Fin 3 → ZMod 3) (j : Fin 3), x = vecElt z v * t ^ (j : ℕ) := by
  have hx' : x ∈ ((baseA z : Set H) * (zpowers t : Set H)) := by
    rw [← coe_mul_of_right_le_normalizer_left _ _ (zpowers_t_le_normalizer hf)]
    exact hx
  obtain ⟨a, ha, b, hb, rfl⟩ := hx'
  obtain ⟨v, rfl⟩ := (mem_baseA_iff hf).mp ha
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hb
  refine ⟨v, ⟨(k : ZMod 3).val, ZMod.val_lt _⟩, ?_⟩
  change vecElt z v * t ^ k = vecElt z v * t ^ ((k : ZMod 3).val)
  rw [← zpow_natCast, ZMod.val_intCast]
  have h3 := zpow_mod_orderOf t k
  rw [orderOf_t hf] at h3
  rw [h3]

theorem le_card_wreathW [Finite H] (hf : WreathFacts z t) : 81 ≤ Nat.card (wreathW z t) := by
  obtain ⟨k, hk⟩ := (isPGroup_wreathW hf).exists_card_eq
  have hle : baseA z ≤ wreathW z t := le_sup_left
  have hdvd : 3 ^ 3 ∣ 3 ^ k := by
    rw [← hk, show (3 : ℕ) ^ 3 = 27 by norm_num, ← card_baseA hf]
    exact Subgroup.card_dvd_of_le hle
  have hk3 : 3 ≤ k := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp hdvd
  have hk4 : k ≠ 3 := by
    rintro rfl
    apply t_notMem_baseA hf
    have heq : baseA z = wreathW z t :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [hk, card_baseA hf]; norm_num)
    rw [heq]
    exact t_mem_wreathW
  rw [hk]
  calc 81 = 3 ^ 4 := by norm_num
    _ ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)

theorem eq_of_commute (hf : WreathFacts z t) {v : Fin 3 → ZMod 3} {j : Fin 3} (hj : j ≠ 0)
    (h : vecElt z v * t ^ (j : ℕ) = t ^ (j : ℕ) * vecElt z v) : v 0 = v 1 ∧ v 1 = v 2 := by
  have hconj : t ^ (j : ℕ) * vecElt z v * (t ^ (j : ℕ))⁻¹ = vecElt z v := by
    rw [← h, mul_inv_cancel_right]
  have hj12 : (j : ℕ) = 1 ∨ (j : ℕ) = 2 := by
    have hj0 : (j : ℕ) ≠ 0 := fun h0 => hj (Fin.ext h0)
    have := j.isLt
    omega
  rcases hj12 with hj1 | hj2
  · rw [hj1, pow_one, conj_vecElt hf] at hconj
    have h1 := vecElt_injective hf hconj
    have e1 := congrFun h1 1
    have e2 := congrFun h1 2
    simp only [Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons] at e1 e2
    exact ⟨e1, e2⟩
  · rw [hj2, show t ^ 2 * vecElt z v * (t ^ 2)⁻¹ = t * (t * vecElt z v * t⁻¹) * t⁻¹ by
        rw [sq, mul_inv_rev]; simp only [mul_assoc],
      conj_vecElt hf, conj_vecElt hf] at hconj
    have h1 := vecElt_injective hf hconj
    have e0 := congrFun h1 0
    have e1 := congrFun h1 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons] at e0 e1
    exact ⟨e0.symm, e1.symm⟩

theorem eq_baseA_of_le_wreathW (hf : WreathFacts z t) (hW : Nat.card (wreathW z t) = 81)
    {E : Subgroup H} (hEW : E ≤ wreathW z t) (hE : CFSG.Assembly.IsElemAbelian 3 E)
    (hE27 : Nat.card E = 27) : E = baseA z := by
  have hWfin : Finite (wreathW z t) := Nat.finite_of_card_ne_zero (by rw [hW]; norm_num)
  have hEfin : Finite E := Nat.finite_of_card_ne_zero (by rw [hE27]; norm_num)
  have hAfin : Finite (baseA z) := Nat.finite_of_card_ne_zero (by rw [card_baseA hf]; norm_num)
  by_contra hne
  have hnle : ¬ E ≤ baseA z := fun hle =>
    hne (Subgroup.eq_of_le_of_card_ge hle (by rw [hE27, card_baseA hf]))
  obtain ⟨x, hxE, hxA⟩ : ∃ x ∈ E, x ∉ baseA z := by
    by_contra hc
    push Not at hc
    exact hnle hc
  obtain ⟨v, j, rfl⟩ := mem_wreathW hf (hEW hxE)
  have hj : j ≠ 0 := by
    rintro rfl
    apply hxA
    rw [Fin.val_zero, pow_zero, mul_one]
    exact vecElt_mem_baseA hf v
  have hint : baseA z ⊓ E ≤ zpowers (vecElt z ![1, 1, 1]) := by
    rintro b ⟨hbA, hbE⟩
    obtain ⟨u, rfl⟩ := (mem_baseA_iff hf).mp hbA
    have hcomm : vecElt z u * (vecElt z v * t ^ (j : ℕ)) =
        vecElt z v * t ^ (j : ℕ) * vecElt z u :=
      congrArg Subtype.val (hE.1.is_comm.comm ⟨_, hbE⟩ ⟨_, hxE⟩)
    have huv : vecElt z u * vecElt z v = vecElt z v * vecElt z u := by
      rw [← vecElt_add hf, ← vecElt_add hf, add_comm]
    have h2 : vecElt z u * t ^ (j : ℕ) = t ^ (j : ℕ) * vecElt z u := by
      have h3 : vecElt z v * (vecElt z u * t ^ (j : ℕ)) =
          vecElt z v * (t ^ (j : ℕ) * vecElt z u) := by
        rw [← mul_assoc, ← huv, mul_assoc, hcomm, mul_assoc]
      exact mul_left_cancel h3
    obtain ⟨h01, h12⟩ := eq_of_commute hf hj h2
    exact vecElt_mem_zpowers_of_const hf h01 h12
  have hz3 : Nat.card (zpowers (vecElt z ![1, 1, 1])) ≤ 3 := by
    rw [Nat.card_zpowers]
    apply Nat.le_of_dvd (by norm_num)
    exact orderOf_dvd_of_pow_eq_one ((isElemAbelian_baseA hf).2 _ (vecElt_mem_baseA hf _))
  have hcardint : Nat.card (baseA z ⊓ E : Subgroup H) ≤ 3 := by
    have hfin : Finite (zpowers (vecElt z ![1, 1, 1])) := by
      refine Nat.finite_of_card_ne_zero ?_
      rw [Nat.card_zpowers]
      exact (orderOf_pos_iff.mpr (isOfFinOrder_iff_pow_eq_one.mpr ⟨3, by norm_num,
        (isElemAbelian_baseA hf).2 _ (vecElt_mem_baseA hf _)⟩)).ne'
    exact (Subgroup.card_le_of_le hint).trans hz3
  have hrW : (baseA z).relIndex (wreathW z t) = 3 := by
    have hle : baseA z ≤ wreathW z t := le_sup_left
    have h := Subgroup.relIndex_mul_card (H := baseA z) (K := wreathW z t)
    rw [inf_of_le_left hle, card_baseA hf, hW] at h
    omega
  have hrE : (baseA z).relIndex E ≤ 3 := by
    rw [← hrW]
    exact Subgroup.relIndex_le_of_le_right hEW (by rw [hrW]; norm_num)
  have h := Subgroup.relIndex_mul_card (H := baseA z) (K := E)
  rw [hE27] at h
  have : (baseA z).relIndex E * Nat.card (baseA z ⊓ E : Subgroup H) ≤ 3 * 3 :=
    Nat.mul_le_mul hrE hcardint
  omega

end Top

theorem WreathFacts.subtype {z : Fin 3 → H} {t : H} (hf : WreathFacts z t) {K : Subgroup H}
    (hz : ∀ i, z i ∈ K) (ht : t ∈ K) :
    WreathFacts (fun i => (⟨z i, hz i⟩ : K)) ⟨t, ht⟩ := by
  have hvec : ∀ v, ((vecElt (fun i => (⟨z i, hz i⟩ : K)) v : K) : H) = vecElt z v := by
    intro v
    simp [vecElt]
  refine ⟨fun i => Subtype.ext ?_, fun i j => Subtype.ext ?_, fun v hv => hf.inj v ?_,
    Subtype.ext ?_, Subtype.ext ?_, Subtype.ext ?_, Subtype.ext ?_, fun v hv => hf.t_ne v ?_⟩
  · simpa using hf.pow_z i
  · simpa using hf.comm_z i j
  · rw [← hvec, hv, Subgroup.coe_one]
  · simpa using hf.pow_t
  · simpa using hf.conj0
  · simpa using hf.conj1
  · simpa using hf.conj2
  · rw [← hvec, hv]

end CFSG.RankThree.PartTwo.Sec4.Item434Kit
