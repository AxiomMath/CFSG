module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.FieldTheory.Finite.Basic

public section

namespace CFSG.StandardType

variable {G : Type} [Group G]

theorem conj_inv_mem_of_mem_normalizer {A : Subgroup G} {z : G}
    (hz : z ∈ Subgroup.normalizer (A : Set G)) {a : G} (ha : a ∈ A) : z⁻¹ * a * z ∈ A := by
  have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hz) a).mp ha
  rwa [inv_inv] at this

@[expose] def ggCommHom (A : Subgroup G) [IsMulCommutative A] (z : G)
    (hz : z ∈ Subgroup.normalizer (A : Set G)) : A →* A where
  toFun a := ⟨(a : G)⁻¹ * (z⁻¹ * a * z),
    A.mul_mem (A.inv_mem a.2) (conj_inv_mem_of_mem_normalizer hz a.2)⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := by
    apply Subtype.ext
    have hx := conj_inv_mem_of_mem_normalizer hz a.2
    have hy := conj_inv_mem_of_mem_normalizer hz b.2
    have hc : ((a : G)⁻¹ * (z⁻¹ * a * z)) * (b : G)⁻¹ =
        (b : G)⁻¹ * ((a : G)⁻¹ * (z⁻¹ * a * z)) :=
      setLike_mul_comm (A.mul_mem (A.inv_mem a.2) hx) (A.inv_mem b.2)
    show ((a : G) * b)⁻¹ * (z⁻¹ * (a * b) * z) =
      ((a : G)⁻¹ * (z⁻¹ * a * z)) * ((b : G)⁻¹ * (z⁻¹ * b * z))
    calc ((a : G) * b)⁻¹ * (z⁻¹ * (a * b) * z) =
        (b : G)⁻¹ * ((a : G)⁻¹ * (z⁻¹ * a * z)) * (z⁻¹ * b * z) := by group
      _ = ((a : G)⁻¹ * (z⁻¹ * a * z)) * (b : G)⁻¹ * (z⁻¹ * b * z) := by rw [hc]
      _ = ((a : G)⁻¹ * (z⁻¹ * a * z)) * ((b : G)⁻¹ * (z⁻¹ * b * z)) := by group

theorem ggCommHom_apply (A : Subgroup G) [IsMulCommutative A] (z : G)
    (hz : z ∈ Subgroup.normalizer (A : Set G)) (a : A) :
    ((ggCommHom A z hz a : A) : G) = (a : G)⁻¹ * (z⁻¹ * a * z) :=
  rfl

theorem ker_ggCommHom (A : Subgroup G) [IsMulCommutative A] (z : G)
    (hz : z ∈ Subgroup.normalizer (A : Set G)) :
    (ggCommHom A z hz).ker = (Subgroup.centralizer {z}).subgroupOf A := by
  ext a
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    have h' : (a : G)⁻¹ * (z⁻¹ * a * z) = 1 := congrArg Subtype.val h
    have : z⁻¹ * a * z = a := by
      calc z⁻¹ * a * z = (a : G) * ((a : G)⁻¹ * (z⁻¹ * a * z)) := by group
        _ = a := by rw [h', mul_one]
    calc (a : G) * z = z * (z⁻¹ * a * z) := by group
      _ = z * a := by rw [this]
  · intro h
    apply Subtype.ext
    show (a : G)⁻¹ * (z⁻¹ * a * z) = 1
    calc (a : G)⁻¹ * (z⁻¹ * a * z) = (a : G)⁻¹ * (z⁻¹ * (a * z)) := by group
      _ = (a : G)⁻¹ * (z⁻¹ * (z * a)) := by rw [h]
      _ = 1 := by group

theorem orderOf_eq_of_card_le [Finite G] {p : ℕ} [hp : Fact p.Prime] {Q R : Subgroup G}
    (hQ : IsPGroup p Q) (hRQ : R ≤ Q) (hR : Nat.card R ≤ p) {r : G} (hr : r ∈ R) (hr1 : r ≠ 1) :
    orderOf r = p ∧ R = Subgroup.zpowers r := by
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hQ) ⟨r, hRQ hr⟩
  rw [Subgroup.orderOf_mk] at hk
  have hdvd : orderOf r ∣ Nat.card R := by
    rw [← Subgroup.orderOf_mk r hr]
    exact orderOf_dvd_natCard _
  have hpos : 0 < Nat.card R := Nat.card_pos
  have hle : p ^ k ≤ p := (hk ▸ Nat.le_of_dvd hpos hdvd).trans hR
  have hk1 : k ≤ 1 := by
    by_contra hk1
    have : p ^ 2 ≤ p ^ k := Nat.pow_le_pow_right hp.out.pos (by omega)
    have : p < p ^ 2 := by nlinarith [hp.out.two_le]
    omega
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hr1 (orderOf_eq_one_iff.mp (by simpa using hk))
  have hko : orderOf r = p := by
    rw [hk, show k = 1 by omega, pow_one]
  refine ⟨hko, (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hr) ?_).symm⟩
  rw [Nat.card_zpowers, hko]
  exact hR

theorem conj_eq_self_of_mem_zpowers {p : ℕ} [hp : Fact p.Prime] {r z : G} (hr : orderOf r = p)
    (hz : z ^ p = 1) (hmem : z⁻¹ * r * z ∈ Subgroup.zpowers r) : z⁻¹ * r * z = r := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have hiter : ∀ j : ℕ, (z ^ j)⁻¹ * r * z ^ j = r ^ (k ^ j) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have hc : ∀ m : ℤ, z⁻¹ * r ^ m * z = (z⁻¹ * r * z) ^ m := by
        intro m
        have := map_zpow (MulAut.conj z⁻¹) r m
        simpa [MulAut.conj_apply] using this
      calc (z ^ (j + 1))⁻¹ * r * z ^ (j + 1) = z⁻¹ * ((z ^ j)⁻¹ * r * z ^ j) * z := by group
        _ = z⁻¹ * r ^ (k ^ j) * z := by rw [ih]
        _ = (z⁻¹ * r * z) ^ (k ^ j) := hc _
        _ = (r ^ k) ^ (k ^ j) := by rw [hk]
        _ = r ^ (k ^ (j + 1)) := by rw [← zpow_mul, pow_succ, mul_comm]
  have hp1 := hiter p
  rw [hz, inv_one, one_mul, mul_one] at hp1
  have h1 : r ^ (k ^ p - 1) = 1 := by
    rw [zpow_sub, ← hp1, zpow_one, mul_inv_cancel]
  have hdvd : (p : ℤ) ∣ k ^ p - 1 := by
    have := orderOf_dvd_iff_zpow_eq_one.mpr h1
    rwa [hr] at this
  have hz1 : ((k ^ p - 1 : ℤ) : ZMod p) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hdvd
  push_cast at hz1
  rw [ZMod.pow_card] at hz1
  have hdvd' : (p : ℤ) ∣ k - 1 := by
    have : ((k - 1 : ℤ) : ZMod p) = 0 := by push_cast; exact hz1
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp this
  have hk1 : r ^ (k - 1) = 1 := by
    rw [← hr] at hdvd'
    exact orderOf_dvd_iff_zpow_eq_one.mp hdvd'
  rw [← hk, show k = (k - 1) + 1 by ring, zpow_add, hk1, one_mul, zpow_one]

theorem conj_comm_eq_of_card_le [Finite G] {p : ℕ} [hp : Fact p.Prime] {Q A : Subgroup G}
    {z e : G} (hAQ : A ≤ Q) (hAc : IsMulCommutative A) (hzA : z ∈ Subgroup.normalizer (A : Set G))
    (hQp : IsPGroup p Q) (hzp : z ^ p = 1)
    (hcard : Nat.card Q ≤ p * Nat.card ↥(Q ⊓ Subgroup.centralizer {z})) (he : e ∈ A) :
    z⁻¹ * (e⁻¹ * (z⁻¹ * e * z)) * z = e⁻¹ * (z⁻¹ * e * z) := by
  set φ := ggCommHom A z hzA with hφ
  have hQidx : (Subgroup.centralizer {z}).relIndex Q ≤ p := by
    have h1 := Subgroup.relIndex_mul_card (Subgroup.centralizer {z}) Q
    rw [inf_comm] at h1
    have hpos : 0 < Nat.card ↥(Q ⊓ Subgroup.centralizer {z}) := Nat.card_pos
    exact Nat.le_of_mul_le_mul_right (h1 ▸ hcard) hpos
  have : (Subgroup.centralizer {z}).IsFiniteRelIndex Q := Subgroup.isFiniteRelIndex_of_finiteIndex
  have hAidx : (Subgroup.centralizer {z}).relIndex A ≤ p :=
    (Subgroup.relIndex_le_of_le_right hAQ Subgroup.relIndex_ne_zero).trans hQidx
  have hrange : Nat.card φ.range ≤ p := by
    rw [← Subgroup.index_ker, hφ, ker_ggCommHom]
    exact hAidx
  set R : Subgroup G := φ.range.map A.subtype with hR
  have hRcard : Nat.card R ≤ p := by
    rw [hR, Subgroup.card_map_of_injective A.subtype_injective]
    exact hrange
  have hRQ : R ≤ Q := (Subgroup.map_subtype_le _).trans hAQ
  set r : G := e⁻¹ * (z⁻¹ * e * z) with hr
  have hrR : r ∈ R := ⟨φ ⟨e, he⟩, ⟨⟨e, he⟩, rfl⟩, rfl⟩
  by_cases hr1 : r = 1
  · rw [hr1]
    group
  obtain ⟨hro, hRz⟩ := orderOf_eq_of_card_le hQp hRQ hRcard hrR hr1
  have he' : z⁻¹ * e * z ∈ A := conj_inv_mem_of_mem_normalizer hzA he
  have hzr : z⁻¹ * r * z ∈ R := by
    refine ⟨φ ⟨z⁻¹ * e * z, he'⟩, ⟨⟨z⁻¹ * e * z, he'⟩, rfl⟩, ?_⟩
    show (z⁻¹ * e * z)⁻¹ * (z⁻¹ * (z⁻¹ * e * z) * z) = z⁻¹ * r * z
    rw [hr]
    group
  rw [hRz] at hzr
  exact conj_eq_self_of_mem_zpowers hro hzp hzr

end CFSG.StandardType
