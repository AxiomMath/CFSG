module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.GroupTheory.NoncommCoprod
public import Mathlib.GroupTheory.SpecificGroups.Quaternion
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.Quasithin.S143

open QuaternionGroup

theorem q8_commutator_central (x y z : QuaternionGroup 2) :
    x * y * x⁻¹ * y⁻¹ * z = z * (x * y * x⁻¹ * y⁻¹) := by
  revert x y z
  decide

theorem q8_sq_central (x z : QuaternionGroup 2) : x * x * z = z * (x * x) := by
  revert x z
  decide

theorem q8_card_center : Nat.card (Subgroup.center (QuaternionGroup 2)) = 2 := by
  rw [Nat.card_eq_fintype_card]
  decide

theorem q8_card : Nat.card (QuaternionGroup 2) = 8 := by
  rw [Nat.card_eq_fintype_card, QuaternionGroup.card]

theorem q8_gen (x : QuaternionGroup 2) :
    ∃ m : Fin 4, ∃ n : Fin 2, x = a 1 ^ (m : ℕ) * xa 0 ^ (n : ℕ) := by
  revert x
  decide

theorem commutator_central_of_mulEquiv {C : Type*} [Group C] (e : C ≃* QuaternionGroup 2)
    (x y z : C) : x * y * x⁻¹ * y⁻¹ * z = z * (x * y * x⁻¹ * y⁻¹) := by
  apply e.injective
  simp only [map_mul, map_inv]
  exact q8_commutator_central _ _ _

theorem sq_central_of_mulEquiv {C : Type*} [Group C] (e : C ≃* QuaternionGroup 2) (x z : C) :
    x * x * z = z * (x * x) := by
  apply e.injective
  simp only [map_mul]
  exact q8_sq_central _ _

structure Q8SqData (P : Type*) [Group P] where
  A : Subgroup P
  B : Subgroup P
  comm : A ≤ Subgroup.centralizer (B : Set P)
  sup : A ⊔ B = ⊤
  eA : A ≃* QuaternionGroup 2
  eB : B ≃* QuaternionGroup 2
  card : Nat.card P = 32

namespace Q8SqData

variable {P : Type*} [Group P] (d : Q8SqData P)

theorem mul_comm_of_mem {a b : P} (ha : a ∈ d.A) (hb : b ∈ d.B) : a * b = b * a :=
  ((Subgroup.mem_centralizer_iff.mp (d.comm ha)) b hb).symm

def swap : Q8SqData P where
  A := d.B
  B := d.A
  comm := fun _ hb => Subgroup.mem_centralizer_iff.mpr fun _ ha => d.mul_comm_of_mem ha hb
  sup := by rw [sup_comm]; exact d.sup
  eA := d.eB
  eB := d.eA
  card := d.card

def prodHom : d.A × d.B →* P :=
  d.A.subtype.noncommCoprod d.B.subtype fun a b =>
    show Commute (d.A.subtype a) (d.B.subtype b) from d.mul_comm_of_mem a.2 b.2

theorem prodHom_apply (s : d.A × d.B) : d.prodHom s = (s.1 : P) * (s.2 : P) := by
  simp [prodHom]

theorem prodHom_surjective : Function.Surjective d.prodHom := by
  rw [← MonoidHom.range_eq_top, prodHom, MonoidHom.noncommCoprod_range, Subgroup.range_subtype,
    Subgroup.range_subtype, d.sup]

theorem exists_mul (x : P) : ∃ a ∈ d.A, ∃ b ∈ d.B, x = a * b := by
  obtain ⟨⟨a, b⟩, rfl⟩ := d.prodHom_surjective x
  exact ⟨a, a.2, b, b.2, rfl⟩

theorem inf_le_center : d.A ⊓ d.B ≤ Subgroup.center P := by
  intro x hx
  rw [Subgroup.mem_center_iff]
  intro y
  obtain ⟨a, ha, b, hb, rfl⟩ := d.exists_mul y
  have h1 : a * x = x * a := d.mul_comm_of_mem ha hx.2
  have h2 : x * b = b * x := d.mul_comm_of_mem hx.1 hb
  calc a * b * x = a * (b * x) := by rw [mul_assoc]
    _ = a * (x * b) := by rw [h2]
    _ = a * x * b := by rw [mul_assoc]
    _ = x * a * b := by rw [h1]
    _ = x * (a * b) := by rw [mul_assoc]

theorem normal_B : d.B.Normal := by
  refine ⟨fun n hn g => ?_⟩
  obtain ⟨a, ha, b, hb, rfl⟩ := d.exists_mul g
  have hbn : b * n * b⁻¹ ∈ d.B := d.B.mul_mem (d.B.mul_mem hb hn) (d.B.inv_mem hb)
  have h2 := d.mul_comm_of_mem ha hbn
  have e : a * b * n * (a * b)⁻¹ = b * n * b⁻¹ := by
    calc a * b * n * (a * b)⁻¹ = a * (b * n * b⁻¹) * a⁻¹ := by group
      _ = (b * n * b⁻¹) * a * a⁻¹ := by rw [h2]
      _ = b * n * b⁻¹ := by group
  rw [e]
  exact hbn

theorem card_A : Nat.card d.A = 8 := (Nat.card_congr d.eA.toEquiv).trans q8_card

theorem card_B : Nat.card d.B = 8 := (Nat.card_congr d.eB.toEquiv).trans q8_card

theorem card_inf : Nat.card ↥(d.A ⊓ d.B) = 2 := by
  have := d.normal_B
  have h1 : d.B.relIndex (d.A ⊔ d.B) = d.B.relIndex d.A := Subgroup.relIndex_sup_right d.A d.B
  rw [d.sup, Subgroup.relIndex_top_right] at h1
  have h2 : d.B.index = 4 := by
    have := Subgroup.card_mul_index d.B
    rw [d.card_B, d.card] at this
    omega
  have h3 := Subgroup.relIndex_mul_card d.B d.A
  rw [← h1, h2, d.card_A] at h3
  rw [inf_comm]
  omega

theorem mem_B_of_central {a : P} (ha : a ∈ d.A) (hc : ∀ a' ∈ d.A, a * a' = a' * a) : a ∈ d.B := by
  have : Finite d.A := Nat.finite_of_card_ne_zero (by rw [d.card_A]; norm_num)
  have hZ : Nat.card (Subgroup.center d.A) = 2 :=
    (Nat.card_congr (Subgroup.centerCongr d.eA).toEquiv).trans q8_card_center
  have hD'card : Nat.card ((d.A ⊓ d.B).subgroupOf d.A) = 2 := by
    rw [← d.card_inf]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hle : (d.A ⊓ d.B).subgroupOf d.A ≤ Subgroup.center d.A := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (d.mul_comm_of_mem y.2 (Subgroup.mem_subgroupOf.mp hx).2)
  have heq : (d.A ⊓ d.B).subgroupOf d.A = Subgroup.center d.A :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hZ, hD'card])
  have hmem : (⟨a, ha⟩ : d.A) ∈ (d.A ⊓ d.B).subgroupOf d.A := by
    rw [heq, Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (hc y y.2).symm
  exact (Subgroup.mem_subgroupOf.mp hmem).2

theorem mem_A_of_central {b : P} (hb : b ∈ d.B) (hc : ∀ b' ∈ d.B, b * b' = b' * b) : b ∈ d.A :=
  d.swap.mem_B_of_central hb hc

theorem center_eq : Subgroup.center P = d.A ⊓ d.B := by
  refine le_antisymm ?_ d.inf_le_center
  intro x hx
  rw [Subgroup.mem_center_iff] at hx
  obtain ⟨a, ha, b, hb, rfl⟩ := d.exists_mul x
  have haB : a ∈ d.B := by
    refine d.mem_B_of_central ha fun a' ha' => ?_
    have h1 := hx a'
    have h2 : b * a' = a' * b := (d.mul_comm_of_mem ha' hb).symm
    have h3 : a' * a * b = a * a' * b := by
      calc a' * a * b = a' * (a * b) := by rw [mul_assoc]
        _ = a * b * a' := h1
        _ = a * (b * a') := by rw [mul_assoc]
        _ = a * (a' * b) := by rw [h2]
        _ = a * a' * b := by rw [mul_assoc]
    exact (mul_right_cancel h3).symm
  have hbA : b ∈ d.A := by
    refine d.mem_A_of_central hb fun b' hb' => ?_
    have h1 := hx b'
    have h2 : a * b' = b' * a := d.mul_comm_of_mem ha hb'
    have h3 : a * (b' * b) = a * (b * b') := by
      calc a * (b' * b) = a * b' * b := by rw [mul_assoc]
        _ = b' * a * b := by rw [h2]
        _ = b' * (a * b) := by rw [mul_assoc]
        _ = a * b * b' := h1
        _ = a * (b * b') := by rw [mul_assoc]
    exact (mul_left_cancel h3).symm
  exact (d.A ⊓ d.B).mul_mem ⟨ha, haB⟩ ⟨hbA, hb⟩

include d in
theorem card_center : Nat.card (Subgroup.center P) = 2 := by
  rw [d.center_eq]
  exact d.card_inf

theorem mem_center_of_central_A {a : P} (ha : a ∈ d.A) (hc : ∀ a' ∈ d.A, a * a' = a' * a) :
    a ∈ Subgroup.center P :=
  d.inf_le_center ⟨ha, d.mem_B_of_central ha hc⟩

theorem mem_center_of_central_B {b : P} (hb : b ∈ d.B) (hc : ∀ b' ∈ d.B, b * b' = b' * b) :
    b ∈ Subgroup.center P :=
  d.inf_le_center ⟨d.mem_A_of_central hb hc, hb⟩

theorem commutator_mem_center_A {a a' : P} (ha : a ∈ d.A) (ha' : a' ∈ d.A) :
    a * a' * a⁻¹ * a'⁻¹ ∈ Subgroup.center P := by
  refine d.mem_center_of_central_A
    (d.A.mul_mem (d.A.mul_mem (d.A.mul_mem ha ha') (d.A.inv_mem ha)) (d.A.inv_mem ha'))
    fun a'' ha'' => ?_
  exact congrArg Subtype.val
    (commutator_central_of_mulEquiv d.eA ⟨a, ha⟩ ⟨a', ha'⟩ ⟨a'', ha''⟩)

theorem commutator_mem_center_B {b b' : P} (hb : b ∈ d.B) (hb' : b' ∈ d.B) :
    b * b' * b⁻¹ * b'⁻¹ ∈ Subgroup.center P :=
  d.swap.commutator_mem_center_A hb hb'

theorem sq_mem_center_A {a : P} (ha : a ∈ d.A) : a * a ∈ Subgroup.center P :=
  d.mem_center_of_central_A (d.A.mul_mem ha ha) fun a'' ha'' =>
    congrArg Subtype.val (sq_central_of_mulEquiv d.eA ⟨a, ha⟩ ⟨a'', ha''⟩)

theorem sq_mem_center_B {b : P} (hb : b ∈ d.B) : b * b ∈ Subgroup.center P :=
  d.swap.sq_mem_center_A hb

include d in
theorem commutator_mem_center (x y : P) : x * y * x⁻¹ * y⁻¹ ∈ Subgroup.center P := by
  obtain ⟨⟨a, b⟩, rfl⟩ := d.prodHom_surjective x
  obtain ⟨⟨a', b'⟩, rfl⟩ := d.prodHom_surjective y
  have e : d.prodHom ((a, b) * (a', b') * (a, b)⁻¹ * (a', b')⁻¹) =
      ((a : P) * a' * (a : P)⁻¹ * (a' : P)⁻¹) * ((b : P) * b' * (b : P)⁻¹ * (b' : P)⁻¹) := by
    rw [prodHom_apply]
    rfl
  simp only [map_mul, map_inv] at e
  rw [e]
  exact (Subgroup.center P).mul_mem (d.commutator_mem_center_A a.2 a'.2)
    (d.commutator_mem_center_B b.2 b'.2)

include d in
theorem sq_mem_center (x : P) : x * x ∈ Subgroup.center P := by
  obtain ⟨⟨a, b⟩, rfl⟩ := d.prodHom_surjective x
  have e : d.prodHom ((a, b) * (a, b)) = ((a : P) * a) * ((b : P) * b) := by
    rw [prodHom_apply]
    rfl
  rw [map_mul] at e
  rw [e]
  exact (Subgroup.center P).mul_mem (d.sq_mem_center_A a.2) (d.sq_mem_center_B b.2)

def gens : Fin 4 → P :=
  ![((d.eA.symm (QuaternionGroup.a 1) : d.A) : P), ((d.eA.symm (QuaternionGroup.xa 0) : d.A) : P),
    ((d.eB.symm (QuaternionGroup.a 1) : d.B) : P), ((d.eB.symm (QuaternionGroup.xa 0) : d.B) : P)]

theorem closure_gens : Subgroup.closure (Set.range d.gens) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  have h0 : d.gens 0 ∈ Subgroup.closure (Set.range d.gens) := Subgroup.subset_closure ⟨0, rfl⟩
  have h1 : d.gens 1 ∈ Subgroup.closure (Set.range d.gens) := Subgroup.subset_closure ⟨1, rfl⟩
  have h2 : d.gens 2 ∈ Subgroup.closure (Set.range d.gens) := Subgroup.subset_closure ⟨2, rfl⟩
  have h3 : d.gens 3 ∈ Subgroup.closure (Set.range d.gens) := Subgroup.subset_closure ⟨3, rfl⟩
  obtain ⟨⟨s, t⟩, rfl⟩ := d.prodHom_surjective x
  rw [prodHom_apply]
  refine (Subgroup.closure _).mul_mem ?_ ?_
  · obtain ⟨m, n, hmn⟩ := q8_gen (d.eA s)
    have e : s = d.eA.symm (QuaternionGroup.a 1) ^ (m : ℕ) *
        d.eA.symm (QuaternionGroup.xa 0) ^ (n : ℕ) := by
      have := congrArg d.eA.symm hmn
      rwa [MulEquiv.symm_apply_apply, map_mul, map_pow, map_pow] at this
    rw [e]
    exact (Subgroup.closure _).mul_mem ((Subgroup.closure _).pow_mem h0 _)
      ((Subgroup.closure _).pow_mem h1 _)
  · obtain ⟨m, n, hmn⟩ := q8_gen (d.eB t)
    have e : t = d.eB.symm (QuaternionGroup.a 1) ^ (m : ℕ) *
        d.eB.symm (QuaternionGroup.xa 0) ^ (n : ℕ) := by
      have := congrArg d.eB.symm hmn
      rwa [MulEquiv.symm_apply_apply, map_mul, map_pow, map_pow] at this
    rw [e]
    exact (Subgroup.closure _).mul_mem ((Subgroup.closure _).pow_mem h2 _)
      ((Subgroup.closure _).pow_mem h3 _)

end Q8SqData

section Abstract

variable {P : Type*} [Group P]

def commToCenter (hc : ∀ x y : P, x * y * x⁻¹ * y⁻¹ ∈ Subgroup.center P) (v : P) :
    P →* Subgroup.center P where
  toFun w := ⟨w * v * w⁻¹ * v⁻¹, hc w v⟩
  map_one' := Subtype.ext (by simp)
  map_mul' w w' := by
    apply Subtype.ext
    have h1 := Subgroup.mem_center_iff.mp (hc w' v) w
    have h2 := Subgroup.mem_center_iff.mp (hc w v) (w' * v * w'⁻¹ * v⁻¹)
    show w * w' * v * (w * w')⁻¹ * v⁻¹ = (w * v * w⁻¹ * v⁻¹) * (w' * v * w'⁻¹ * v⁻¹)
    calc w * w' * v * (w * w')⁻¹ * v⁻¹
        = w * (w' * v * w'⁻¹ * v⁻¹) * (v * w⁻¹ * v⁻¹) := by group
      _ = (w' * v * w'⁻¹ * v⁻¹) * w * (v * w⁻¹ * v⁻¹) := by rw [h1]
      _ = (w' * v * w'⁻¹ * v⁻¹) * (w * v * w⁻¹ * v⁻¹) := by group
      _ = (w * v * w⁻¹ * v⁻¹) * (w' * v * w'⁻¹ * v⁻¹) := h2

theorem mem_ker_commToCenter (hc : ∀ x y : P, x * y * x⁻¹ * y⁻¹ ∈ Subgroup.center P) {v w : P} :
    w ∈ (commToCenter hc v).ker ↔ w * v = v * w := by
  rw [MonoidHom.mem_ker, Subtype.ext_iff]
  show w * v * w⁻¹ * v⁻¹ = 1 ↔ w * v = v * w
  rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul]

theorem card_centralizer_of_not_mem_center (hcard : Nat.card P = 32)
    (hZ : Nat.card (Subgroup.center P) = 2)
    (hc : ∀ x y : P, x * y * x⁻¹ * y⁻¹ ∈ Subgroup.center P) {v : P} (hv : v ∉ Subgroup.center P) :
    Nat.card (Subgroup.centralizer ({v} : Set P)) = 16 := by
  have hker : (commToCenter hc v).ker = Subgroup.centralizer ({v} : Set P) := by
    ext w
    rw [mem_ker_commToCenter, Subgroup.mem_centralizer_singleton_iff]
  have hrange : Nat.card (commToCenter hc v).range = 2 := by
    have hdvd : Nat.card (commToCenter hc v).range ∣ Nat.card (Subgroup.center P) :=
      Subgroup.card_subgroup_dvd_card _
    have hne : Nat.card (commToCenter hc v).range ≠ 1 := by
      intro h1
      rw [Subgroup.card_eq_one] at h1
      apply hv
      rw [Subgroup.mem_center_iff]
      intro g
      have hg : commToCenter hc v g = 1 := Subgroup.mem_bot.mp (h1 ▸ ⟨g, rfl⟩)
      exact (mem_ker_commToCenter hc).mp hg
    rw [hZ] at hdvd
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact absurd h hne
    · exact h
  have := Subgroup.card_ker_mul_card_range (commToCenter hc v)
  rw [hker, hrange, hcard] at this
  omega

theorem exists_inner_of_gens (hcard : Nat.card P = 32) (hZ : Nat.card (Subgroup.center P) = 2)
    (hc : ∀ x y : P, x * y * x⁻¹ * y⁻¹ ∈ Subgroup.center P) (g : Fin 4 → P)
    (hg : Subgroup.closure (Set.range g) = ⊤) (φ : P →* P)
    (hφ : ∀ u, φ u * u⁻¹ ∈ Subgroup.center P) : ∃ w : P, ∀ u, φ u = w * u * w⁻¹ := by
  have : Finite P := Nat.finite_of_card_ne_zero (by omega)
  let Θ : P →* (Fin 4 → Subgroup.center P) := MonoidHom.pi fun k => commToCenter hc (g k)
  have hkerΘ : Θ.ker = Subgroup.center P := by
    ext w
    rw [MonoidHom.mem_ker, Subgroup.mem_center_iff]
    constructor
    · intro h x
      have hk : ∀ k, w * g k = g k * w := fun k => (mem_ker_commToCenter hc).mp (congrFun h k)
      have hle : Set.range g ⊆ Subgroup.centralizer ({w} : Set P) := by
        rintro _ ⟨k, rfl⟩
        rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
        exact (hk k).symm
      have hx : x ∈ Subgroup.centralizer ({w} : Set P) := by
        have := (Subgroup.closure_le _).mpr hle
        rw [hg] at this
        exact this (Subgroup.mem_top x)
      rwa [Subgroup.mem_centralizer_singleton_iff] at hx
    · intro h
      funext k
      exact (mem_ker_commToCenter hc (v := g k) (w := w)).mpr (h (g k)).symm
  have hrange : Nat.card Θ.range = 16 := by
    have := Subgroup.card_ker_mul_card_range Θ
    rw [hkerΘ, hZ, hcard] at this
    omega
  have hcardPi : Nat.card (Fin 4 → Subgroup.center P) = 16 := by
    rw [Nat.card_fun, hZ]
    simp
  have htop : Θ.range = ⊤ := Subgroup.eq_top_of_card_eq _ (by rw [hrange, hcardPi])
  obtain ⟨w, hw⟩ : ∃ w, Θ w = fun k => ⟨φ (g k) * (g k)⁻¹, hφ (g k)⟩ := by
    have hmem : (fun k => (⟨φ (g k) * (g k)⁻¹, hφ (g k)⟩ : Subgroup.center P)) ∈ Θ.range := by
      rw [htop]
      exact Subgroup.mem_top _
    exact hmem
  refine ⟨w, ?_⟩
  have hgen : ∀ k, φ (g k) = w * g k * w⁻¹ := by
    intro k
    have h2 := congrArg Subtype.val (congrFun hw k)
    exact (mul_right_cancel h2).symm
  have heq : Set.EqOn φ (MulAut.conj w).toMonoidHom (Set.range g) := by
    rintro _ ⟨k, rfl⟩
    simpa using hgen k
  intro u
  have := MonoidHom.eqOn_closure heq
  rw [hg] at this
  simpa using this (Subgroup.mem_top u)

end Abstract

end CFSG.Quasithin.S143
