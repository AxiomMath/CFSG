module

public import CFSG.Monster.B.Short.Extraspecial
public import Mathlib.GroupTheory.SpecificGroups.KleinFour

public section

namespace CFSG.Monster.B.Short

open CFSG Subgroup
open scoped commutatorElement

variable {P : Type*} [Group P]

theorem commutatorElement_mem_commutator (x y : P) : ⁅x, y⁆ ∈ commutator P := by
  rw [_root_.commutator_def]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y)

theorem mem_zpowers_iff_of_orderOf_eq_two {g x : P} (hg : orderOf g = 2) :
    x ∈ zpowers g ↔ x = 1 ∨ x = g := by
  constructor
  · rintro ⟨k, rfl⟩
    have h := zpow_mod_orderOf g k
    rw [hg] at h
    simp only at h ⊢
    rw [← h]
    have : k % (2 : ℕ) = 0 ∨ k % (2 : ℕ) = 1 := by omega
    rcases this with h0 | h1
    · left; rw [h0, zpow_zero]
    · right; rw [h1, zpow_one]
  · rintro (h | h) <;> rw [h]
    · exact one_mem _
    · exact mem_zpowers g

theorem commutatorElement_mul_right_eq (a b c : P) :
    ⁅a, b * c⁆ = ⁅a, b⁆ * (b * ⁅a, c⁆ * b⁻¹) := by
  simp only [commutatorElement_def]; group

theorem commutatorElement_mul_left_eq (a b c : P) :
    ⁅a * b, c⁆ = (a * ⁅b, c⁆ * a⁻¹) * ⁅a, c⁆ := by
  simp only [commutatorElement_def]; group

theorem conj_eq_self_of_mem_center {k : P} (hk : k ∈ center P) (b : P) : b * k * b⁻¹ = k := by
  rw [Subgroup.mem_center_iff.1 hk b, mul_inv_cancel_right]

@[expose] def commHom (hc : commutator P ≤ center P) (x : P) : P →* center P where
  toFun y := ⟨⁅x, y⁆, hc (commutatorElement_mem_commutator x y)⟩
  map_one' := Subtype.ext (commutatorElement_one_right x)
  map_mul' y w := Subtype.ext (by
    simp only [Subgroup.coe_mul]
    rw [commutatorElement_mul_right_eq,
      conj_eq_self_of_mem_center (hc (commutatorElement_mem_commutator x w))])

theorem commHom_apply (hc : commutator P ≤ center P) (x y : P) :
    (commHom hc x y : P) = ⁅x, y⁆ := rfl

theorem ker_commHom (hc : commutator P ≤ center P) (x : P) :
    (commHom hc x).ker = centralizer {x} := by
  ext y
  rw [MonoidHom.mem_ker, Subgroup.mem_centralizer_singleton_iff, ← Subtype.coe_inj,
    commHom_apply, Subgroup.coe_one, commutatorElement_eq_one_iff_mul_comm, eq_comm]

abbrev invCent (r : P) : Subgroup P := centralizer {r}

theorem self_mem_invCent (r : P) : r ∈ invCent r := mem_centralizer_singleton_iff.2 rfl

theorem mem_invCent_of_mem_center {x : P} (hx : x ∈ center P) (r : P) : x ∈ invCent r :=
  mem_centralizer_singleton_iff.2 (mem_center_iff.1 hx r).symm

@[expose] def rD (r : P) : invCent r := ⟨r, self_mem_invCent r⟩

@[expose] def zD {z : P} (hz : z ∈ center P) (r : P) : invCent r := ⟨z, mem_invCent_of_mem_center hz r⟩

theorem rD_mem_center (r : P) : rD r ∈ center (invCent r) := by
  rw [mem_center_iff]
  intro d
  exact Subtype.ext (mem_centralizer_singleton_iff.1 d.2)

theorem zD_mem_center {z : P} (hz : z ∈ center P) (r : P) : zD hz r ∈ center (invCent r) := by
  rw [mem_center_iff]
  intro d
  exact Subtype.ext (mem_center_iff.1 hz d)

instance normal_zpowers_rD (r : P) : (zpowers (rD r)).Normal :=
  normal_of_le_center (zpowers_le.2 (rD_mem_center r))

theorem mem_center_of_center_eq_zpowers {z : P} (hz : center P = zpowers z) : z ∈ center P :=
  hz ▸ mem_zpowers z

section Extraspecial

variable {z : P}

theorem orderOf_z_of_extraspecial (hP : IsExtraspecialPGroup 2 P) (hz : center P = zpowers z) :
    orderOf z = 2 := by
  rw [← Nat.card_zpowers, ← hz, hP.natCard_center]

theorem mem_center_iff_of_extraspecial (hP : IsExtraspecialPGroup 2 P)
    (hz : center P = zpowers z) {x : P} : x ∈ center P ↔ x = 1 ∨ x = z := by
  rw [hz]
  exact mem_zpowers_iff_of_orderOf_eq_two (orderOf_z_of_extraspecial hP hz)

theorem mul_self_eq_one_of_mem_center (hP : IsExtraspecialPGroup 2 P)
    (hz : center P = zpowers z) {x : P} (hx : x ∈ center P) : x * x = 1 := by
  rcases (mem_center_iff_of_extraspecial hP hz).1 hx with rfl | rfl
  · rw [mul_one]
  · rw [← pow_two, ← orderOf_z_of_extraspecial hP hz]
    exact pow_orderOf_eq_one x

theorem sq_mem_center_of_extraspecial (hP : IsExtraspecialPGroup 2 P)
    (hz : center P = zpowers z) (x : P) : x ^ 2 ∈ center P := by
  rw [mem_center_iff]
  intro w
  have hxw := hP.commutator_eq.le (commutatorElement_mem_commutator x w)
  have h1 : ⁅x * x, w⁆ = 1 := by
    rw [commutatorElement_mul_left_eq, conj_eq_self_of_mem_center hxw,
      mul_self_eq_one_of_mem_center hP hz hxw]
  rw [commutatorElement_eq_one_iff_mul_comm, ← pow_two] at h1
  exact h1.symm

theorem commutatorElement_eq_one_or_eq (hP : IsExtraspecialPGroup 2 P)
    (hz : center P = zpowers z) (x y : P) : ⁅x, y⁆ = 1 ∨ ⁅x, y⁆ = z :=
  (mem_center_iff_of_extraspecial hP hz).1
    (hP.commutator_eq.le (commutatorElement_mem_commutator x y))

theorem range_commHom_eq_top (hP : IsExtraspecialPGroup 2 P) {x : P} (hx : x ∉ center P) :
    (commHom hP.commutator_eq.le x).range = ⊤ := by
  have : Fact (Nat.card (center P)).Prime := ⟨by rw [hP.natCard_center]; exact Nat.prime_two⟩
  refine (Subgroup.eq_bot_or_eq_top_of_prime_card _).resolve_left fun hbot => hx ?_
  rw [mem_center_iff]
  intro y
  have hy : commHom hP.commutator_eq.le x y = 1 := by
    have : commHom hP.commutator_eq.le x y ∈ (commHom hP.commutator_eq.le x).range := ⟨y, rfl⟩
    rw [hbot, Subgroup.mem_bot] at this
    exact this
  have h2 := congrArg Subtype.val hy
  rw [commHom_apply, Subgroup.coe_one, commutatorElement_eq_one_iff_mul_comm] at h2
  exact h2.symm

theorem card_invCent_mul_two (hP : IsExtraspecialPGroup 2 P) {x : P} (hx : x ∉ center P) :
    Nat.card (invCent x) * 2 = Nat.card P := by
  have h := (commHom hP.commutator_eq.le x).ker.card_mul_index
  rw [Subgroup.index_ker, range_commHom_eq_top hP hx, Subgroup.card_top, hP.natCard_center,
    ker_commHom] at h
  exact h

variable {r : P}

theorem mul_self_eq_one_of_orderOf (hr : orderOf r = 2) : r * r = 1 := by
  rw [← pow_two, ← hr]
  exact pow_orderOf_eq_one r

theorem mem_center_invCent_iff [Finite P] (hP : IsExtraspecialPGroup 2 P) (hz : center P = zpowers z)
    (hr : orderOf r = 2) (hrZ : r ∉ center P) (x : invCent r) :
    x ∈ center (invCent r) ↔ (x : P) = 1 ∨ (x : P) = z ∨ (x : P) = r ∨ (x : P) = z * r := by
  have hzc : z ∈ center P := mem_center_of_center_eq_zpowers hz
  constructor
  · intro hx
    by_cases hxZ : (x : P) ∈ center P
    · rcases (mem_center_iff_of_extraspecial hP hz).1 hxZ with h | h
      · exact .inl h
      · exact .inr (.inl h)
    · right; right
      have hle : invCent r ≤ invCent (x : P) := by
        intro d hd
        rw [mem_centralizer_singleton_iff]
        exact congrArg Subtype.val (mem_center_iff.1 hx ⟨d, hd⟩)
      have heq : invCent r = invCent (x : P) := by
        refine Subgroup.eq_of_le_of_card_ge hle ?_
        have h1 := card_invCent_mul_two hP hrZ
        have h2 := card_invCent_mul_two hP hxZ
        omega
      have hcomm : ∀ y : P, ⁅(x : P), y⁆ = ⁅r, y⁆ := by
        intro y
        by_cases hy : ⁅r, y⁆ = 1
        · have hyr : y ∈ invCent r :=
            mem_centralizer_singleton_iff.2 (commutatorElement_eq_one_iff_mul_comm.1 hy).symm
          have hyx : y ∈ invCent (x : P) := heq ▸ hyr
          rw [hy, commutatorElement_eq_one_iff_mul_comm]
          exact (mem_centralizer_singleton_iff.1 hyx).symm
        · have hyr : y ∉ invCent r := fun h =>
            hy (commutatorElement_eq_one_iff_mul_comm.2 (mem_centralizer_singleton_iff.1 h).symm)
          have hyx : y ∉ invCent (x : P) := heq ▸ hyr
          have hxy : ⁅(x : P), y⁆ ≠ 1 := fun h =>
            hyx (mem_centralizer_singleton_iff.2 (commutatorElement_eq_one_iff_mul_comm.1 h).symm)
          rw [(commutatorElement_eq_one_or_eq hP hz _ y).resolve_left hxy,
            (commutatorElement_eq_one_or_eq hP hz r y).resolve_left hy]
      have hxr : (x : P) * r ∈ center P := by
        rw [mem_center_iff]
        intro y
        have hry := hP.commutator_eq.le (commutatorElement_mem_commutator r y)
        have h1 : ⁅(x : P) * r, y⁆ = 1 := by
          rw [commutatorElement_mul_left_eq, conj_eq_self_of_mem_center hry, hcomm y,
            mul_self_eq_one_of_mem_center hP hz hry]
        rw [commutatorElement_eq_one_iff_mul_comm] at h1
        exact h1.symm
      have hrr := mul_self_eq_one_of_orderOf hr
      rcases (mem_center_iff_of_extraspecial hP hz).1 hxr with h | h
      · left
        calc (x : P) = (x : P) * r * r := by rw [mul_assoc, hrr, mul_one]
          _ = r := by rw [h, one_mul]
      · right
        calc (x : P) = (x : P) * r * r := by rw [mul_assoc, hrr, mul_one]
          _ = z * r := by rw [h]
  · rintro (h | h | h | h)
    · rw [show x = 1 from Subtype.ext h]
      exact one_mem _
    · rw [show x = zD hzc r from Subtype.ext h]
      exact zD_mem_center hzc r
    · rw [show x = rD r from Subtype.ext h]
      exact rD_mem_center r
    · rw [show x = zD hzc r * rD r from Subtype.ext h]
      exact mul_mem (zD_mem_center hzc r) (rD_mem_center r)

theorem distinct_of_extraspecial (hP : IsExtraspecialPGroup 2 P) (hz : center P = zpowers z)
    (hr : orderOf r = 2) (hrZ : r ∉ center P) :
    z ≠ 1 ∧ r ≠ 1 ∧ z ≠ r ∧ z * r ≠ 1 ∧ z ≠ z * r ∧ r ≠ z * r := by
  have hzc : z ∈ center P := mem_center_of_center_eq_zpowers hz
  have hz2 := orderOf_z_of_extraspecial hP hz
  have hz1 : z ≠ 1 := fun h => by rw [h, orderOf_one] at hz2; exact absurd hz2 (by norm_num)
  have hr1 : r ≠ 1 := fun h => by rw [h, orderOf_one] at hr; exact absurd hr (by norm_num)
  refine ⟨hz1, hr1, fun h => hrZ (h ▸ hzc), fun h => hrZ ?_, fun h => hr1 ?_, fun h => hz1 ?_⟩
  · rw [eq_inv_of_mul_eq_one_right h]
    exact inv_mem hzc
  · exact (mul_eq_left.1 h.symm)
  · exact (mul_eq_right.1 h.symm)

theorem center_invCent_eq_closure [Finite P] (hP : IsExtraspecialPGroup 2 P) (hz : center P = zpowers z)
    (hr : orderOf r = 2) (hrZ : r ∉ center P) :
    center (invCent r) = closure {zD (mem_center_of_center_eq_zpowers hz) r, rD r} := by
  have hzc : z ∈ center P := mem_center_of_center_eq_zpowers hz
  apply le_antisymm
  · intro x hx
    rcases (mem_center_invCent_iff hP hz hr hrZ x).1 hx with h | h | h | h
    · rw [show x = 1 from Subtype.ext h]
      exact one_mem _
    · rw [show x = zD hzc r from Subtype.ext h]
      exact subset_closure (Set.mem_insert _ _)
    · rw [show x = rD r from Subtype.ext h]
      exact subset_closure (Set.mem_insert_of_mem _ rfl)
    · rw [show x = zD hzc r * rD r from Subtype.ext h]
      exact mul_mem (subset_closure (Set.mem_insert _ _))
        (subset_closure (Set.mem_insert_of_mem _ rfl))
  · rw [closure_le]
    rintro _ (rfl | rfl)
    · exact zD_mem_center hzc r
    · exact rD_mem_center r

theorem natCard_center_invCent [Finite P] (hP : IsExtraspecialPGroup 2 P) (hz : center P = zpowers z)
    (hr : orderOf r = 2) (hrZ : r ∉ center P) : Nat.card (center (invCent r)) = 4 := by
  have hzc : z ∈ center P := mem_center_of_center_eq_zpowers hz
  obtain ⟨hz1, hr1, hzr, hzr1, hz_zr, hr_zr⟩ := distinct_of_extraspecial hP hz hr hrZ
  have himage : Subtype.val '' (center (invCent r) : Set (invCent r)) =
      ({1, z, r, z * r} : Set P) := by
    ext y
    simp only [Set.mem_image, SetLike.mem_coe, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (mem_center_invCent_iff hP hz hr hrZ x).1 hx
    · intro hy
      have hyD : y ∈ invCent r := by
        rcases hy with rfl | rfl | rfl | rfl
        · exact one_mem _
        · exact mem_invCent_of_mem_center hzc r
        · exact self_mem_invCent _
        · exact mul_mem (mem_invCent_of_mem_center hzc _) (self_mem_invCent _)
      exact ⟨⟨y, hyD⟩, (mem_center_invCent_iff hP hz hr hrZ ⟨y, hyD⟩).2 hy, rfl⟩
  have h1 : Nat.card (center (invCent r)) = ((center (invCent r) : Set (invCent r))).ncard :=
    Nat.card_coe_set_eq _
  rw [h1, ← Set.ncard_image_of_injective _ Subtype.val_injective, himage,
    Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem, Set.ncard_pair hr_zr]
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hzr, hz_zr⟩
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hz1.symm, hr1.symm, hzr1.symm⟩

theorem isKleinFour_center_invCent [Finite P] (hP : IsExtraspecialPGroup 2 P) (hz : center P = zpowers z)
    (hr : orderOf r = 2) (hrZ : r ∉ center P) : IsKleinFour (center (invCent r)) where
  card_four := natCard_center_invCent hP hz hr hrZ
  exponent_two := by
    have hzc : z ∈ center P := mem_center_of_center_eq_zpowers hz
    have : Nontrivial (center (invCent r)) := by
      rw [← Finite.one_lt_card_iff_nontrivial, natCard_center_invCent hP hz hr hrZ]
      norm_num
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rw [Monoid.exponent_eq_prime_iff Nat.prime_two]
    intro g hg
    refine orderOf_eq_prime ?_ hg
    have hz2 : z * z = 1 := mul_self_eq_one_of_mem_center hP hz hzc
    have hrr := mul_self_eq_one_of_orderOf hr
    have key : ((g : invCent r) : P) * ((g : invCent r) : P) = 1 := by
      rcases (mem_center_invCent_iff hP hz hr hrZ g.1).1 g.2 with h | h | h | h <;> rw [h]
      · rw [mul_one]
      · exact hz2
      · exact hrr
      · have hrz : r * z = z * r := mem_center_iff.1 hzc r
        calc z * r * (z * r) = z * (r * z) * r := by simp only [mul_assoc]
          _ = z * (z * r) * r := by rw [hrz]
          _ = (z * z) * (r * r) := by simp only [mul_assoc]
          _ = 1 := by rw [hz2, hrr, mul_one]
    have h1 : (g : invCent r) ^ 2 = 1 :=
      Subtype.ext (by rw [Subgroup.coe_pow, pow_two, key, Subgroup.coe_one])
    exact Subtype.ext (by rw [Subgroup.coe_pow, h1, Subgroup.coe_one])

theorem orderOf_zD (hP : IsExtraspecialPGroup 2 P) (hz : center P = zpowers z) (r : P) :
    orderOf (zD (mem_center_of_center_eq_zpowers hz) r) = 2 :=
  (Subgroup.orderOf_mk z _).trans (orderOf_z_of_extraspecial hP hz)

theorem orderOf_rD (hr : orderOf r = 2) : orderOf (rD r) = 2 :=
  (Subgroup.orderOf_mk r _).trans hr

theorem natCard_invCent {n : ℕ} (hP : IsExtraspecialPGroup 2 P)
    (hcard : Nat.card P = 2 ^ (1 + 2 * n)) (hrZ : r ∉ center P) :
    Nat.card (invCent r) = 2 ^ (2 * n) := by
  have h := card_invCent_mul_two hP hrZ
  rw [hcard, pow_add, pow_one, mul_comm] at h
  exact Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 2) h

theorem commutator_invCent [Finite P] {n : ℕ} (hn : 2 ≤ n) (hP : IsExtraspecialPGroup 2 P)
    (hcard : Nat.card P = 2 ^ (1 + 2 * n)) (hz : center P = zpowers z) (hr : orderOf r = 2)
    (hrZ : r ∉ center P) :
    commutator (invCent r) = zpowers (zD (mem_center_of_center_eq_zpowers hz) r) := by
  have hle : commutator (invCent r) ≤ zpowers (zD (mem_center_of_center_eq_zpowers hz) r) := by
    rw [_root_.commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [mem_zpowers_iff_of_orderOf_eq_two (orderOf_zD hP hz r)]
    rcases commutatorElement_eq_one_or_eq hP hz (a : P) (b : P) with h | h
    · exact .inl (Subtype.ext h)
    · exact .inr (Subtype.ext h)
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [Nat.card_zpowers, orderOf_zD hP hz r]
  have hdvd : Nat.card (commutator (invCent r)) ∣ 2 := by
    have := Subgroup.card_dvd_of_le hle
    rwa [Nat.card_zpowers, orderOf_zD hP hz r] at this
  rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h1 | h2
  · exfalso
    have hbot : commutator (invCent r) = ⊥ := Subgroup.eq_bot_of_card_eq _ h1
    have htop : center (invCent r) = ⊤ := by
      rw [eq_top_iff]
      intro y _
      rw [mem_center_iff]
      intro x
      have hxy := commutatorElement_mem_commutator x y
      rw [hbot, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hxy
      exact hxy
    have h4 := natCard_center_invCent hP hz hr hrZ
    rw [htop, Subgroup.card_top, natCard_invCent hP hcard hrZ] at h4
    have : 2 ^ 4 ≤ 2 ^ (2 * n) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  · rw [h2]

theorem mk_zD_ne_one (hP : IsExtraspecialPGroup 2 P) (hz : center P = zpowers z)
    (hr : orderOf r = 2) (hrZ : r ∉ center P) :
    (QuotientGroup.mk (zD (mem_center_of_center_eq_zpowers hz) r) :
      invCent r ⧸ zpowers (rD r)) ≠ 1 := by
  obtain ⟨hz1, -, hzr, -⟩ := distinct_of_extraspecial hP hz hr hrZ
  intro h
  rw [QuotientGroup.eq_one_iff, mem_zpowers_iff_of_orderOf_eq_two (orderOf_rD hr)] at h
  rcases h with h | h
  · exact hz1 (congrArg Subtype.val h)
  · exact hzr (congrArg Subtype.val h)

theorem orderOf_mk_zD (hP : IsExtraspecialPGroup 2 P) (hz : center P = zpowers z)
    (hr : orderOf r = 2) (hrZ : r ∉ center P) :
    orderOf (QuotientGroup.mk (zD (mem_center_of_center_eq_zpowers hz) r) :
      invCent r ⧸ zpowers (rD r)) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine orderOf_eq_prime ?_ (mk_zD_ne_one hP hz hr hrZ)
  rw [← QuotientGroup.mk_pow, ← orderOf_zD hP hz r, pow_orderOf_eq_one, QuotientGroup.mk_one]

theorem natCard_quot_invCent {n : ℕ} (hn : 2 ≤ n) (hP : IsExtraspecialPGroup 2 P)
    (hcard : Nat.card P = 2 ^ (1 + 2 * n)) (hr : orderOf r = 2) (hrZ : r ∉ center P) :
    Nat.card (invCent r ⧸ zpowers (rD r)) = 2 ^ (2 * n - 1) := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (zpowers (rD r))
  rw [natCard_invCent hP hcard hrZ, Nat.card_zpowers, orderOf_rD hr,
    show 2 * n = (2 * n - 1) + 1 by omega, pow_succ] at h
  rw [show 2 * n - 1 = (2 * n - 1) + 1 - 1 by omega]
  exact (Nat.eq_of_mul_eq_mul_right (by norm_num) h).symm

theorem center_quot_invCent [Finite P] (hP : IsExtraspecialPGroup 2 P) (hz : center P = zpowers z)
    (hr : orderOf r = 2) (hrZ : r ∉ center P) :
    center (invCent r ⧸ zpowers (rD r)) =
      zpowers (QuotientGroup.mk (zD (mem_center_of_center_eq_zpowers hz) r)) := by
  have hzc : z ∈ center P := mem_center_of_center_eq_zpowers hz
  obtain ⟨-, hr1, hzr, -⟩ := distinct_of_extraspecial hP hz hr hrZ
  apply le_antisymm
  · intro x hx
    obtain ⟨e, rfl⟩ := QuotientGroup.mk_surjective x
    have hcomm : ∀ d : invCent r, ⁅e, d⁆ = 1 := by
      intro d
      have h1 : (QuotientGroup.mk' (zpowers (rD r)) ⁅e, d⁆) = 1 := by
        rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
        exact (mem_center_iff.1 hx (QuotientGroup.mk d)).symm
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
        mem_zpowers_iff_of_orderOf_eq_two (orderOf_rD hr)] at h1
      rcases h1 with h1 | h1
      · exact h1
      · exfalso
        have h2 : ((⁅e, d⁆ : invCent r) : P) = r := congrArg Subtype.val h1
        rcases commutatorElement_eq_one_or_eq hP hz (e : P) (d : P) with h3 | h3
        · exact hr1 (h2.symm.trans h3)
        · exact hzr (h3.symm.trans h2)
    have he : e ∈ center (invCent r) := by
      rw [mem_center_iff]
      intro d
      exact ((commutatorElement_eq_one_iff_mul_comm.1 (hcomm d))).symm
    rcases (mem_center_invCent_iff hP hz hr hrZ e).1 he with h | h | h | h
    · rw [show e = 1 from Subtype.ext h, QuotientGroup.mk_one]
      exact one_mem _
    · rw [show e = zD hzc r from Subtype.ext h]
      exact mem_zpowers _
    · rw [show e = rD r from Subtype.ext h,
        (QuotientGroup.eq_one_iff (rD r)).2 (mem_zpowers _)]
      exact one_mem _
    · rw [show e = zD hzc r * rD r from Subtype.ext h, QuotientGroup.mk_mul,
        (QuotientGroup.eq_one_iff (rD r)).2 (mem_zpowers _), mul_one]
      exact mem_zpowers _
  · rw [zpowers_le]
    exact Subgroup.map_center_le_center (QuotientGroup.mk'_surjective (zpowers (rD r)))
      ⟨zD hzc r, zD_mem_center hzc r, rfl⟩

theorem commutator_quot_invCent [Finite P] {n : ℕ} (hn : 2 ≤ n) (hP : IsExtraspecialPGroup 2 P)
    (hcard : Nat.card P = 2 ^ (1 + 2 * n)) (hz : center P = zpowers z) (hr : orderOf r = 2)
    (hrZ : r ∉ center P) :
    commutator (invCent r ⧸ zpowers (rD r)) =
      zpowers (QuotientGroup.mk (zD (mem_center_of_center_eq_zpowers hz) r)) := by
  rw [_root_.commutator_def,
    ← Subgroup.map_top_of_surjective (QuotientGroup.mk' (zpowers (rD r)))
      (QuotientGroup.mk'_surjective _),
    ← Subgroup.map_commutator, ← _root_.commutator_def, commutator_invCent hn hP hcard hz hr hrZ,
    MonoidHom.map_zpowers]
  rfl

theorem frattini_quot_invCent [Finite P] {n : ℕ} (hn : 2 ≤ n) (hP : IsExtraspecialPGroup 2 P)
    (hcard : Nat.card P = 2 ^ (1 + 2 * n)) (hz : center P = zpowers z) (hr : orderOf r = 2)
    (hrZ : r ∉ center P) :
    frattini (invCent r ⧸ zpowers (rD r)) =
      zpowers (QuotientGroup.mk (zD (mem_center_of_center_eq_zpowers hz) r)) := by
  have hzc : z ∈ center P := mem_center_of_center_eq_zpowers hz
  have : Finite (invCent r ⧸ zpowers (rD r)) := inferInstance
  have : Fact (IsPGroup 2 (invCent r ⧸ zpowers (rD r))) :=
    ⟨IsPGroup.of_card (natCard_quot_invCent hn hP hcard hr hrZ)⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [frattini_eq_closure_commutator_union_powers (p := 2)]
  apply le_antisymm
  · rw [closure_le]
    rintro x (hx | ⟨y, rfl⟩)
    · rwa [commutator_quot_invCent hn hP hcard hz hr hrZ] at hx
    · obtain ⟨d, rfl⟩ := QuotientGroup.mk_surjective y
      dsimp only
      rw [← QuotientGroup.mk_pow]
      rcases (mem_center_iff_of_extraspecial hP hz).1
          (sq_mem_center_of_extraspecial hP hz (d : P)) with h | h
      · rw [show d ^ 2 = 1 from Subtype.ext (by rw [Subgroup.coe_pow, h, Subgroup.coe_one]),
          QuotientGroup.mk_one]
        exact one_mem _
      · rw [show d ^ 2 = zD hzc r from Subtype.ext (by rw [Subgroup.coe_pow, h]; rfl)]
        exact mem_zpowers _
  · rw [← commutator_quot_invCent hn hP hcard hz hr hrZ]
    exact fun x hx => subset_closure (Or.inl hx)

end Extraspecial

theorem extraspecial_involution_centralizer_quotient [Finite P] {n : ℕ} (hn : 2 ≤ n)
    (hP : IsExtraspecialPGroup 2 P) (hcard : Nat.card P = 2 ^ (1 + 2 * n)) {z : P}
    (hz : center P = zpowers z) {r : P} (hr : orderOf r = 2) (hrZ : r ∉ center P) :
    Nat.card (invCent r) = 2 ^ (2 * n) ∧
    center (invCent r) = closure {zD (mem_center_of_center_eq_zpowers hz) r, rD r} ∧
    Nonempty (center (invCent r) ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) ∧
    commutator (invCent r) = zpowers (zD (mem_center_of_center_eq_zpowers hz) r) ∧
    IsExtraspecialPGroup 2 (invCent r ⧸ zpowers (rD r)) ∧
    Nat.card (invCent r ⧸ zpowers (rD r)) = 2 ^ (2 * n - 1) ∧
    center (invCent r ⧸ zpowers (rD r)) =
      zpowers (QuotientGroup.mk (zD (mem_center_of_center_eq_zpowers hz) r)) ∧
    commutator (invCent r ⧸ zpowers (rD r)) =
      zpowers (QuotientGroup.mk (zD (mem_center_of_center_eq_zpowers hz) r)) ∧
    frattini (invCent r ⧸ zpowers (rD r)) =
      zpowers (QuotientGroup.mk (zD (mem_center_of_center_eq_zpowers hz) r)) := by
  have hK : IsKleinFour (center (invCent r)) := isKleinFour_center_invCent hP hz hr hrZ
  have hC : center (invCent r ⧸ zpowers (rD r)) =
      zpowers (QuotientGroup.mk (zD (mem_center_of_center_eq_zpowers hz) r)) :=
    center_quot_invCent hP hz hr hrZ
  refine ⟨natCard_invCent hP hcard hrZ, center_invCent_eq_closure hP hz hr hrZ,
    ⟨(Classical.choice IsKleinFour.nonempty_mulEquiv).trans
      (MulEquiv.prodMultiplicative (ZMod 2) (ZMod 2))⟩,
    commutator_invCent hn hP hcard hz hr hrZ, ⟨?_, ?_, ?_, ?_⟩,
    natCard_quot_invCent hn hP hcard hr hrZ, hC, commutator_quot_invCent hn hP hcard hz hr hrZ,
    frattini_quot_invCent hn hP hcard hz hr hrZ⟩
  · exact IsPGroup.of_card (natCard_quot_invCent hn hP hcard hr hrZ)
  · rw [commutator_quot_invCent hn hP hcard hz hr hrZ, hC]
  · rw [frattini_quot_invCent hn hP hcard hz hr hrZ, hC]
  · rw [hC, Nat.card_zpowers, orderOf_mk_zD hP hz hr hrZ]

end CFSG.Monster.B.Short
