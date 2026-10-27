module

public import CFSG.LocalAnalysis.StandardType.GGUSixTwoTorus
public import Mathlib.Algebra.Module.Submodule.EqLocus
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import CFSG.LocalAnalysis.StandardType.GGUSixTwoTransvection
public import CFSG.LocalAnalysis.GLTheoremA.CatA.H81Orth.Weights
public import CFSG.GF2Type.Smith1979.CaseI25Weights
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Group.Subgroup.ZPowers.Lemmas
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.GroupTheory.Perm.Support

public section

namespace CFSG.StandardType.USixTwo

open CFSG.Assembly Matrix

variable {K : Type} [Field K]

@[expose]
noncomputable def unitOmega [Finite K] {ω : K} (hω : ω ^ 2 + ω + 1 = 0) : Kˣ :=
  Units.mk0 ω (omega_ne_zero hω)

theorem unitOmega_cube [Finite K] {ω : K} (hω : ω ^ 2 + ω + 1 = 0) : unitOmega hω ^ 3 = 1 := by
  ext
  simp [unitOmega, Units.val_pow_eq_pow_val, omega_cube hω]

theorem unitOmega_ne_one [Finite K] (hK : Nat.card K = 4) {ω : K}
    (hω : ω ^ 2 + ω + 1 = 0) : unitOmega hω ≠ 1 := by
  intro h
  apply omega_ne_one hK hω
  have := congrArg (fun x : Kˣ => (x : K)) h
  simpa [unitOmega] using this

theorem card_units_three [Finite K] (hK : Nat.card K = 4) : Nat.card Kˣ = 3 := by
  rw [Nat.card_units, hK]

theorem orderOf_unitOmega [Finite K] (hK : Nat.card K = 4) {ω : K}
    (hω : ω ^ 2 + ω + 1 = 0) : orderOf (unitOmega hω) = 3 :=
  orderOf_eq_prime (unitOmega_cube hω) (unitOmega_ne_one hK hω)

theorem zpowers_unitOmega_eq_top [Finite K] (hK : Nat.card K = 4) {ω : K}
    (hω : ω ^ 2 + ω + 1 = 0) : Subgroup.zpowers (unitOmega hω) = ⊤ := by
  apply Subgroup.eq_top_of_card_eq
  rw [Nat.card_zpowers, orderOf_unitOmega hK hω, card_units_three hK]

@[expose]
noncomputable def coeffEquiv [Finite K] (hK : Nat.card K = 4) {ω : K}
    (hω : ω ^ 2 + ω + 1 = 0) : Multiplicative (ZMod 3) ≃* Kˣ :=
  zmodMulEquivOfGenerator (g := unitOmega hω)
    (fun x => by rw [zpowers_unitOmega_eq_top hK hω]; exact Subgroup.mem_top x)
    (card_units_three hK)

theorem coeffEquiv_one [Finite K] (hK : Nat.card K = 4) {ω : K}
    (hω : ω ^ 2 + ω + 1 = 0) :
    coeffEquiv hK hω (Multiplicative.ofAdd 1) = unitOmega hω :=
  zmodMulEquivOfGenerator_apply_ofAdd_one _ _

abbrev T4 : Type := ZMod 3 × ZMod 3 × ZMod 3 × ZMod 3

@[expose] def expLift (u : T4) : Fin 6 → ZMod 3 :=
  ![u.1, u.2.1, u.2.2.1, u.2.2.2, -(u.1 + u.2.1 + u.2.2.1 + u.2.2.2), 0]

theorem sum_expLift (u : T4) : ∑ i, expLift u i = 0 := by
  rw [show (∑ i, expLift u i) = u.1 + u.2.1 + u.2.2.1 + u.2.2.2 +
      -(u.1 + u.2.1 + u.2.2.1 + u.2.2.2) by
    simp [expLift, Fin.sum_univ_six]]
  abel

@[expose]
def sumZeroAdd : AddSubgroup (Fin 6 → ZMod 3) where
  carrier := {y | ∑ i, y i = 0}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    simp only [Set.mem_setOf_eq, Pi.add_apply]
    rw [Finset.sum_add_distrib, hx, hy, add_zero]
  neg_mem' := by
    intro x hx
    simp only [Set.mem_setOf_eq, Pi.neg_apply] at hx ⊢
    calc ∑ i, -x i = ∑ i, (2 : ZMod 3) * x i := by
          apply Finset.sum_congr rfl
          intro i _
          rw [show (2 : ZMod 3) = -1 by decide]
          exact (neg_one_mul (x i)).symm
      _ = (2 : ZMod 3) * ∑ i, x i := by rw [Finset.mul_sum]
      _ = 0 := by rw [hx, mul_zero]

@[expose]
def sumZeroSubgroup : Subgroup (Multiplicative (Fin 6 → ZMod 3)) :=
  sumZeroAdd.toSubgroup

theorem mem_sumZeroSubgroup_iff {x : Multiplicative (Fin 6 → ZMod 3)} :
    x ∈ sumZeroSubgroup ↔ ∑ i, Multiplicative.toAdd x i = 0 := Iff.rfl

@[expose]
noncomputable def coeffVec [Finite K] (hK : Nat.card K = 4) {ω : K}
    (hω : ω ^ 2 + ω + 1 = 0) :
    Multiplicative (Fin 6 → ZMod 3) →* (Fin 6 → Kˣ) where
  toFun x i := coeffEquiv hK hω (Multiplicative.ofAdd (Multiplicative.toAdd x i))
  map_one' := by
    funext i
    simp
  map_mul' x y := by
    funext i
    show coeffEquiv hK hω (Multiplicative.ofAdd (Multiplicative.toAdd (x * y) i)) =
      coeffEquiv hK hω (Multiplicative.ofAdd (Multiplicative.toAdd x i)) *
      coeffEquiv hK hω (Multiplicative.ofAdd (Multiplicative.toAdd y i))
    rw [show Multiplicative.toAdd (x * y) i =
      Multiplicative.toAdd x i + Multiplicative.toAdd y i from rfl]
    rw [ofAdd_add, map_mul]

theorem prod_coeffVec [Finite K] (hK : Nat.card K = 4) {ω : K}
    (hω : ω ^ 2 + ω + 1 = 0) (x : Multiplicative (Fin 6 → ZMod 3)) :
    ∏ i, coeffVec hK hω x i =
      coeffEquiv hK hω (Multiplicative.ofAdd (∑ i, Multiplicative.toAdd x i)) := by
  change (∏ i, coeffEquiv hK hω (Multiplicative.ofAdd (Multiplicative.toAdd x i))) =
    coeffEquiv hK hω (Multiplicative.ofAdd (∑ i, Multiplicative.toAdd x i))
  rw [← map_prod, ofAdd_sum]

@[expose]
noncomputable def torLift [Finite K] (hK : Nat.card K = 4) {ω : K}
    (hω : ω ^ 2 + ω + 1 = 0) (x : sumZeroSubgroup) :
    ↥(LargeEvenSUGroup (Fin 6) K (2 ^ 1)) :=
  ⟨TauCeti.diagGL (coeffVec hK hω (x : Multiplicative (Fin 6 → ZMod 3))), by
    rw [mem_SU_iff (fieldDataFour hK)]
    constructor
    · rw [← Matrix.GeneralLinearGroup.val_det_apply, TauCeti.det_diagGL]
      rw [prod_coeffVec]
      have hx : ∑ i, Multiplicative.toAdd (x : Multiplicative (Fin 6 → ZMod 3)) i = 0 :=
        mem_sumZeroSubgroup_iff.mp x.2
      rw [hx]
      simp
    · exact diagGL_map_transpose_mul_eq_one hK _⟩

@[expose]
noncomputable def torHom [Finite K] (hK : Nat.card K = 4) {ω : K}
    (hω : ω ^ 2 + ω + 1 = 0) :
    sumZeroSubgroup →* ↥(torU K) where
  toFun x := ⟨LargeEvenProjMk _ (torLift hK hω x), by
    rw [torU]
    refine Subgroup.mem_map.mpr ⟨torLift hK hω x, ?_, rfl⟩
    rw [torSU, Subgroup.mem_comap, TauCeti.mem_diagonalTorus_iff]
    change Matrix.IsDiag (((torLift hK hω x : ↥(LargeEvenSUGroup (Fin 6) K (2 ^ 1))) :
      GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)
    simp only [torLift]
    rw [TauCeti.diagGL_coe]
    exact Matrix.isDiag_diagonal
      (fun i => (coeffVec hK hω (x : Multiplicative (Fin 6 → ZMod 3)) i : K))⟩
  map_one' := by
    apply Subtype.ext
    change LargeEvenProjMk _ (torLift hK hω 1) = 1
    have h1 : torLift hK hω 1 = 1 := by
      apply Subtype.ext
      change TauCeti.diagGL (coeffVec hK hω (1 : Multiplicative (Fin 6 → ZMod 3))) = 1
      rw [show coeffVec hK hω (1 : Multiplicative (Fin 6 → ZMod 3)) = 1 from
        map_one (coeffVec hK hω), map_one]
    rw [h1, map_one]
  map_mul' x y := by
    have hlift : torLift hK hω (x * y) = torLift hK hω x * torLift hK hω y := by
      apply Subtype.ext
      change TauCeti.diagGL (coeffVec hK hω ((x * y : sumZeroSubgroup) : _)) =
        TauCeti.diagGL (coeffVec hK hω (x : _)) * TauCeti.diagGL (coeffVec hK hω (y : _))
      have hc : coeffVec hK hω ((x * y : sumZeroSubgroup) : Multiplicative (Fin 6 → ZMod 3)) =
          coeffVec hK hω (x : Multiplicative (Fin 6 → ZMod 3)) *
            coeffVec hK hω (y : Multiplicative (Fin 6 → ZMod 3)) :=
        map_mul (coeffVec hK hω) (x : Multiplicative (Fin 6 → ZMod 3))
          (y : Multiplicative (Fin 6 → ZMod 3))
      rw [hc, map_mul]
    apply Subtype.ext
    change LargeEvenProjMk _ (torLift hK hω (x * y)) =
      LargeEvenProjMk _ (torLift hK hω x) * LargeEvenProjMk _ (torLift hK hω y)
    rw [hlift, map_mul]

end CFSG.StandardType.USixTwo

namespace CFSG.StandardType.USixTwo

namespace TorHomKernel

open CFSG.Assembly Matrix

variable {K : Type} [Field K] [Finite K] {ω : K}
variable (hK : Nat.card K = 4) (hω : ω ^ 2 + ω + 1 = 0)

@[expose]
def constSubgroup : Subgroup ↥sumZeroSubgroup where
  carrier := {x | ∃ c : ZMod 3,
    ∀ i, Multiplicative.toAdd (x : Multiplicative (Fin 6 → ZMod 3)) i = c}
  one_mem' := ⟨0, by intro i; simp⟩
  mul_mem' := by
    rintro x y ⟨c, hc⟩ ⟨d, hd⟩
    refine ⟨c + d, fun i => ?_⟩
    simp only [Subgroup.coe_mul, Pi.mul_apply, toAdd_mul, Pi.add_apply, hc i, hd i]
  inv_mem' := by
    rintro x ⟨c, hc⟩
    refine ⟨-c, fun i => ?_⟩
    simp only [Subgroup.coe_inv, Pi.inv_apply, toAdd_inv, Pi.neg_apply, hc i]
    rfl

theorem torHom_eq_one_iff (x : ↥sumZeroSubgroup) :
    torHom hK hω x = 1 ↔ x ∈ constSubgroup := by
  constructor
  · intro h
    have hval : LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1)) (torLift hK hω x) = 1 := by
      have := congrArg Subtype.val h
      simpa [torHom] using this
    have hker : (QuotientGroup.mk (torLift hK hω x) :
        LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))) = 1 := by
      simpa [LargeEvenProjMk, QuotientGroup.mk'] using hval
    have hmem : torLift hK hω x ∈
        (LargeEvenScalars (Fin 6) K).subgroupOf (LargeEvenSUGroup (Fin 6) K (2 ^ 1)) :=
      (QuotientGroup.eq_one_iff (torLift hK hω x)).mp hker
    rw [Subgroup.mem_subgroupOf, largeEvenScalars_def] at hmem
    obtain ⟨c, hc⟩ := hmem
    have hentry : ∀ i, coeffVec hK hω (x : Multiplicative (Fin 6 → ZMod 3)) i = c := by
      intro i
      have h := congrArg (fun g : GL (Fin 6) K =>
        ((g : Matrix (Fin 6) (Fin 6) K) i i)) hc
      have h' : (c : K) = (coeffVec hK hω (x : Multiplicative (Fin 6 → ZMod 3)) i : K) := by
        simp only [torLift, TauCeti.diagGL_coe, Matrix.GeneralLinearGroup.coe_scalar,
          Matrix.scalar_apply, Matrix.diagonal_apply_eq] at h
        exact h
      exact Units.ext h'.symm
    refine ⟨Multiplicative.toAdd (x : Multiplicative (Fin 6 → ZMod 3)) 0, fun i => ?_⟩
    have hcoe : coeffEquiv hK hω (Multiplicative.ofAdd
        (Multiplicative.toAdd (x : Multiplicative (Fin 6 → ZMod 3)) 0)) =
        coeffEquiv hK hω (Multiplicative.ofAdd
          (Multiplicative.toAdd (x : Multiplicative (Fin 6 → ZMod 3)) i)) := by
      change coeffVec hK hω (x : Multiplicative (Fin 6 → ZMod 3)) 0 =
        coeffVec hK hω (x : Multiplicative (Fin 6 → ZMod 3)) i
      rw [hentry 0, hentry i]
    have := (coeffEquiv hK hω).injective hcoe
    simpa using congrArg Multiplicative.toAdd this.symm
  · rintro ⟨c, hc⟩
    apply Subtype.ext
    change LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1)) (torLift hK hω x) = 1
    have hmem : torLift hK hω x ∈
        (LargeEvenScalars (Fin 6) K).subgroupOf (LargeEvenSUGroup (Fin 6) K (2 ^ 1)) := by
      rw [Subgroup.mem_subgroupOf, largeEvenScalars_def]
      refine MonoidHom.mem_range.mpr ⟨coeffEquiv hK hω (Multiplicative.ofAdd c), ?_⟩
      apply Units.ext
      ext i j
      have hdiag : (((torLift hK hω x : ↥(LargeEvenSUGroup (Fin 6) K (2 ^ 1))) :
          GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) i j =
          (Matrix.diagonal (fun i =>
            (coeffEquiv hK hω (Multiplicative.ofAdd c) : K))) i j := by
        rw [show ((torLift hK hω x : ↥(LargeEvenSUGroup (Fin 6) K (2 ^ 1))) :
            GL (Fin 6) K) = TauCeti.diagGL
              (coeffVec hK hω (x : Multiplicative (Fin 6 → ZMod 3))) from rfl]
        rw [TauCeti.diagGL_coe]
        by_cases hij : i = j
        · subst hij
          rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq]
          change (coeffEquiv hK hω (Multiplicative.ofAdd
            (Multiplicative.toAdd (x : Multiplicative (Fin 6 → ZMod 3)) i)) : K) =
            (coeffEquiv hK hω (Multiplicative.ofAdd c) : K)
          rw [hc i]
        · rw [Matrix.diagonal_apply_ne _ hij, Matrix.diagonal_apply_ne _ hij]
      rw [hdiag]
      rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
    have hker : (QuotientGroup.mk (torLift hK hω x) :
        LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))) = 1 :=
      (QuotientGroup.eq_one_iff (torLift hK hω x)).mpr hmem
    simpa [LargeEvenProjMk, QuotientGroup.mk'] using hker

end TorHomKernel

end CFSG.StandardType.USixTwo

namespace CFSG.StandardType.USixTwo.TorHomKernel

open CFSG.Assembly Matrix

variable {K : Type} [Field K] [Finite K] {ω : K}
variable (hK : Nat.card K = 4) (hω : ω ^ 2 + ω + 1 = 0)

theorem torHom_surjective : Function.Surjective (torHom hK hω) := by
  intro a
  obtain ⟨A, hA, hAeq⟩ := Subgroup.mem_map.mp a.2
  have hdiag : (A : GL (Fin 6) K) ∈ TauCeti.diagonalTorus K 6 := by
    rw [torSU, Subgroup.mem_comap] at hA
    exact hA
  obtain ⟨t, ht⟩ := TauCeti.mem_diagonalTorus_iff_exists_diagGL.mp hdiag
  have hdetmat : ((A : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).det = 1 :=
    ((mem_SU_iff (fieldDataFour hK)).mp A.2).1
  rw [← ht, TauCeti.diagGL_coe, Matrix.det_diagonal] at hdetmat
  let x : Fin 6 → ZMod 3 := fun i =>
    Multiplicative.toAdd ((coeffEquiv hK hω).symm (t i))
  have hxcoe : ∀ i, coeffEquiv hK hω (Multiplicative.ofAdd (x i)) = t i := by
    intro i
    simp [x]
  have hdet_units : ∏ i, t i = 1 := by
    apply Units.ext
    simpa using hdetmat
  have hprod : ∏ i, coeffEquiv hK hω (Multiplicative.ofAdd (x i)) = 1 := by
    simpa [hxcoe] using hdet_units
  have hsum_eq : coeffEquiv hK hω (Multiplicative.ofAdd (∑ i, x i)) = 1 := by
    refine (prod_coeffVec hK hω (Multiplicative.ofAdd x)).symm.trans ?_
    simpa [coeffVec] using hprod
  have hsum : ∑ i, x i = 0 := by
    have h1 : Multiplicative.ofAdd (∑ i, x i) =
        (Multiplicative.ofAdd (0 : ZMod 3) : Multiplicative (ZMod 3)) := by
      apply (coeffEquiv hK hω).injective
      simpa using hsum_eq
    have := congrArg Multiplicative.toAdd h1
    simpa using this
  let xS : ↥sumZeroSubgroup := ⟨Multiplicative.ofAdd x, mem_sumZeroSubgroup_iff.mpr hsum⟩
  refine ⟨xS, ?_⟩
  apply Subtype.ext
  change LargeEvenProjMk _ (torLift hK hω xS) = a.1
  have hxst : torLift hK hω xS = A := by
    apply Subtype.ext
    change TauCeti.diagGL (coeffVec hK hω (Multiplicative.ofAdd x)) = (A : GL (Fin 6) K)
    rw [← ht]
    congr 1
    funext i
    change coeffEquiv hK hω (Multiplicative.ofAdd (x i)) = t i
    exact hxcoe i
  rw [hxst]
  exact hAeq

end CFSG.StandardType.USixTwo.TorHomKernel

namespace CFSG.StandardType.USixTwo.TorHyperplanes

@[expose]
def delta0 : Fin 6 → ZMod 3 := ![1, 0, 0, 0, 0, -1]
@[expose]
def delta1 : Fin 6 → ZMod 3 := ![0, 1, 0, 0, 0, -1]
@[expose]
def delta2 : Fin 6 → ZMod 3 := ![0, 0, 1, 0, 0, -1]
@[expose]
def delta3 : Fin 6 → ZMod 3 := ![0, 0, 0, 1, 0, -1]
@[expose]
def delta4 : Fin 6 → ZMod 3 := ![0, 0, 0, 0, 1, -1]

theorem sum_delta0 : ∑ i, delta0 i = 0 := by
  simp [delta0, Fin.sum_univ_six]
  decide
theorem sum_delta1 : ∑ i, delta1 i = 0 := by
  simp [delta1, Fin.sum_univ_six]
  decide
theorem sum_delta2 : ∑ i, delta2 i = 0 := by
  simp [delta2, Fin.sum_univ_six]
  decide
theorem sum_delta3 : ∑ i, delta3 i = 0 := by
  simp [delta3, Fin.sum_univ_six]
  decide
theorem sum_delta4 : ∑ i, delta4 i = 0 := by
  simp [delta4, Fin.sum_univ_six]
  decide

theorem delta0_mem : Multiplicative.ofAdd delta0 ∈ sumZeroSubgroup := sum_delta0
theorem delta1_mem : Multiplicative.ofAdd delta1 ∈ sumZeroSubgroup := sum_delta1
theorem delta2_mem : Multiplicative.ofAdd delta2 ∈ sumZeroSubgroup := sum_delta2
theorem delta3_mem : Multiplicative.ofAdd delta3 ∈ sumZeroSubgroup := sum_delta3
theorem delta4_mem : Multiplicative.ofAdd delta4 ∈ sumZeroSubgroup := sum_delta4

theorem expLift_injective : Function.Injective expLift := by
  intro u v h
  have h0 : u.1 = v.1 := by simpa [expLift] using congrFun h (0 : Fin 6)
  have h1 : u.2.1 = v.2.1 := by simpa [expLift] using congrFun h (1 : Fin 6)
  have h2 : u.2.2.1 = v.2.2.1 := by simpa [expLift] using congrFun h (2 : Fin 6)
  have h3 : u.2.2.2 = v.2.2.2 := by simpa [expLift] using congrFun h (3 : Fin 6)
  exact Prod.ext h0 (Prod.ext h1 (Prod.ext h2 h3))

@[expose] noncomputable def fS (u : T4) : ↥sumZeroSubgroup →* Multiplicative (ZMod 3) where
  toFun x := Multiplicative.ofAdd
    (∑ i, expLift u i * Multiplicative.toAdd (x : Multiplicative (Fin 6 → ZMod 3)) i)
  map_one' := by
    simp
  map_mul' x y := by
    simp only [Subgroup.coe_mul, Pi.mul_apply, toAdd_mul, Pi.add_apply, mul_add,
      Finset.sum_add_distrib, ofAdd_add]

theorem fS_apply (u : T4) (x : ↥sumZeroSubgroup) :
    fS u x = Multiplicative.ofAdd
      (∑ i, expLift u i * Multiplicative.toAdd (x : Multiplicative (Fin 6 → ZMod 3)) i) :=
  rfl

theorem expLift_delta0 (u : T4) : ∑ i, expLift u i * delta0 i = expLift u 0 := by
  simp [expLift, delta0, Fin.sum_univ_six]
theorem expLift_delta1 (u : T4) : ∑ i, expLift u i * delta1 i = expLift u 1 := by
  simp [expLift, delta1, Fin.sum_univ_six]
theorem expLift_delta2 (u : T4) : ∑ i, expLift u i * delta2 i = expLift u 2 := by
  simp [expLift, delta2, Fin.sum_univ_six]
theorem expLift_delta3 (u : T4) : ∑ i, expLift u i * delta3 i = expLift u 3 := by
  simp [expLift, delta3, Fin.sum_univ_six]
theorem expLift_delta4 (u : T4) : ∑ i, expLift u i * delta4 i = expLift u 4 := by
  simp [expLift, delta4, Fin.sum_univ_six]

theorem fS_ne_one_of_ne_zero {u : T4} (hu : u ≠ 0) : fS u ≠ 1 := by
  intro h
  apply hu
  apply expLift_injective
  funext i
  fin_cases i
  · have hd : fS u ⟨Multiplicative.ofAdd delta0, delta0_mem⟩ = 1 := by
      rw [h]
      rfl
    simp only [fS_apply, toAdd_ofAdd] at hd
    rw [expLift_delta0] at hd
    have h0 : expLift u 0 = 0 := by
      simpa using congrArg Multiplicative.toAdd hd
    simpa [expLift] using h0
  · have hd : fS u ⟨Multiplicative.ofAdd delta1, delta1_mem⟩ = 1 := by
      rw [h]
      rfl
    simp only [fS_apply, toAdd_ofAdd] at hd
    rw [expLift_delta1] at hd
    have h0 : expLift u 1 = 0 := by
      simpa using congrArg Multiplicative.toAdd hd
    simpa [expLift] using h0
  · have hd : fS u ⟨Multiplicative.ofAdd delta2, delta2_mem⟩ = 1 := by
      rw [h]
      rfl
    simp only [fS_apply, toAdd_ofAdd] at hd
    rw [expLift_delta2] at hd
    have h0 : expLift u 2 = 0 := by
      simpa using congrArg Multiplicative.toAdd hd
    simpa [expLift] using h0
  · have hd : fS u ⟨Multiplicative.ofAdd delta3, delta3_mem⟩ = 1 := by
      rw [h]
      rfl
    simp only [fS_apply, toAdd_ofAdd] at hd
    rw [expLift_delta3] at hd
    have h0 : expLift u 3 = 0 := by
      simpa using congrArg Multiplicative.toAdd hd
    simpa [expLift] using h0
  · change expLift u 4 = expLift 0 4
    have hd : fS u ⟨Multiplicative.ofAdd delta4, delta4_mem⟩ = 1 := by
      rw [h]
      rfl
    simp only [fS_apply, toAdd_ofAdd] at hd
    rw [expLift_delta4] at hd
    have h0 : expLift u 4 = 0 := by
      simpa using congrArg Multiplicative.toAdd hd
    rw [show expLift 0 4 = 0 by
      simp [expLift]
      exact neg_zero]
    exact h0
  · simp [expLift]

end CFSG.StandardType.USixTwo.TorHyperplanes

namespace CFSG.StandardType.USixTwo.TorHyperplanes

open CFSG.Assembly Matrix

variable {K : Type} [Field K] [Finite K] {ω : K}
variable (hK : Nat.card K = 4) (hω : ω ^ 2 + ω + 1 = 0)

theorem ker_le_fS_ker (u : T4) : (torHom hK hω).ker ≤ (fS u).ker := by
  intro x hx
  rw [MonoidHom.mem_ker] at hx ⊢
  rw [CFSG.StandardType.USixTwo.TorHomKernel.torHom_eq_one_iff hK hω] at hx
  obtain ⟨c, hc⟩ := hx
  rw [fS_apply]
  have hsum : ∑ i, expLift u i *
      Multiplicative.toAdd (x : Multiplicative (Fin 6 → ZMod 3)) i = 0 := by
    calc ∑ i, expLift u i * Multiplicative.toAdd (x : Multiplicative (Fin 6 → ZMod 3)) i
        = (∑ i, expLift u i) * c := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro i _
          rw [hc i]
      _ = 0 := by rw [sum_expLift, zero_mul]
  rw [hsum]
  simp

@[expose]
noncomputable def fQ (u : T4) :
    (↥sumZeroSubgroup ⧸ (torHom hK hω).ker) →* Multiplicative (ZMod 3) :=
  QuotientGroup.lift (N := (torHom hK hω).ker) (φ := fS u) (ker_le_fS_ker hK hω u)

@[expose]
noncomputable def torChart :
    (↥sumZeroSubgroup ⧸ (torHom hK hω).ker) ≃* ↥(torU K) :=
  QuotientGroup.quotientKerEquivOfSurjective (torHom hK hω)
    (CFSG.StandardType.USixTwo.TorHomKernel.torHom_surjective hK hω)

@[expose]
noncomputable def Hfun (u : T4) : Subgroup ↥(torU K) :=
  (fQ hK hω u).ker.map (torChart hK hω).toMonoidHom

theorem fQ_ne_one {u : T4} (hu : u ≠ 0) : fQ hK hω u ≠ 1 := by
  intro h
  apply fS_ne_one_of_ne_zero hu
  ext x
  have := congrArg
    (fun f : (↥sumZeroSubgroup ⧸ (torHom hK hω).ker) →* Multiplicative (ZMod 3) =>
      f (QuotientGroup.mk x)) h
  simpa [fQ] using this

theorem fQ_range_eq_top {u : T4} (hu : u ≠ 0) : (fQ hK hω u).range = ⊤ := by
  haveI : Fact (Nat.card (Multiplicative (ZMod 3))).Prime := by
    rw [show Nat.card (Multiplicative (ZMod 3)) = 3 by simp]
    exact ⟨by norm_num⟩
  rcases Subgroup.eq_bot_or_eq_top_of_prime_card (fQ hK hω u).range with h | h
  · exact absurd ((MonoidHom.range_eq_bot_iff).mp h) (fQ_ne_one hK hω hu)
  · exact h

theorem Hfun_index {u : T4} (hu : u ≠ 0) : (Hfun hK hω u).index = 3 := by
  have hrange := fQ_range_eq_top hK hω hu
  have hker : (fQ hK hω u).ker.index = 3 := by
    rw [Subgroup.index_ker, hrange, Subgroup.card_top]
    simp [Nat.card_zmod]
  have hmap := Subgroup.index_map_equiv (H := (fQ hK hω u).ker) (e := torChart hK hω)
  simpa [Hfun] using hmap.trans hker

end CFSG.StandardType.USixTwo.TorHyperplanes

namespace CFSG.StandardType.USixTwo.TorHyperplanes

open CFSG.Assembly Matrix

variable {K : Type} [Field K] [Finite K] {ω : K}
variable (hK : Nat.card K = 4) (hω : ω ^ 2 + ω + 1 = 0)

@[expose] def smulT4 (c : ZMod 3) (u : T4) : T4 := (c * u.1, c * u.2.1, c * u.2.2.1, c * u.2.2.2)

theorem expLift_smul (c : ZMod 3) (u : T4) (i : Fin 6) :
    expLift (smulT4 c u) i = c * expLift u i := by
  fin_cases i
  · simp [expLift, smulT4]
  · simp [expLift, smulT4]
  · simp [expLift, smulT4]
  · simp [expLift, smulT4]
  · simp [expLift, smulT4]
    rw [show c * -(u.1 + u.2.1 + u.2.2.1 + u.2.2.2) =
      -(c * (u.1 + u.2.1 + u.2.2.1 + u.2.2.2)) from mul_neg c _]
    congr 1
    rw [mul_add, mul_add, mul_add]
  · simp [expLift, smulT4]

theorem fS_smul_ker {c : ZMod 3} (hc : c ≠ 0) (u : T4) :
    (fS (smulT4 c u)).ker = (fS u).ker := by
  ext x
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker, fS_apply, fS_apply]
  have hdot : ∑ i, expLift (smulT4 c u) i *
      Multiplicative.toAdd (x : Multiplicative (Fin 6 → ZMod 3)) i =
      c * ∑ i, expLift u i *
        Multiplicative.toAdd (x : Multiplicative (Fin 6 → ZMod 3)) i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [expLift_smul]
    ring
  rw [hdot]
  constructor
  · intro h
    have h' := congrArg Multiplicative.toAdd h
    simp only [toAdd_ofAdd, toAdd_one] at h'
    rcases mul_eq_zero.mp h' with hc0 | h0
    · exact absurd hc0 hc
    · rw [h0]
      simp
  · intro h
    have h0 : ∑ i, expLift u i *
        Multiplicative.toAdd (x : Multiplicative (Fin 6 → ZMod 3)) i = 0 := by
      have := congrArg Multiplicative.toAdd h
      simpa using this
    rw [h0, mul_zero]
    simp

theorem fQ_smul_ker {c : ZMod 3} (hc : c ≠ 0) (u : T4) :
    (fQ hK hω (smulT4 c u)).ker = (fQ hK hω u).ker := by
  rw [fQ, fQ, QuotientGroup.ker_lift, QuotientGroup.ker_lift, fS_smul_ker hc]

theorem Hfun_smul {c : ZMod 3} (hc : c ≠ 0) (u : T4) :
    Hfun hK hω (smulT4 c u) = Hfun hK hω u := by
  rw [Hfun, Hfun, fQ_smul_ker hK hω hc]

end CFSG.StandardType.USixTwo.TorHyperplanes

namespace CFSG.StandardType.USixTwo.TorConj

open CFSG.Assembly Matrix
open CFSG.StandardType.USixTwo.TorHyperplanes

variable {K : Type} [Field K] [Finite K] {ω : K}
variable (hK : Nat.card K = 4) (hω : ω ^ 2 + ω + 1 = 0)

@[expose] def permX (σ : Equiv.Perm (Fin 6)) (x : ↥sumZeroSubgroup) : ↥sumZeroSubgroup :=
  ⟨Multiplicative.ofAdd (fun i =>
      Multiplicative.toAdd (x : Multiplicative (Fin 6 → ZMod 3)) (σ.symm i)), by
    rw [mem_sumZeroSubgroup_iff]
    have hx : ∑ i, Multiplicative.toAdd (x : Multiplicative (Fin 6 → ZMod 3)) i = 0 :=
      mem_sumZeroSubgroup_iff.mp x.2
    simp only [toAdd_ofAdd]
    rw [← hx]
    exact Equiv.sum_comp σ.symm
      (fun i => Multiplicative.toAdd (x : Multiplicative (Fin 6 → ZMod 3)) i)⟩

@[expose] noncomputable def Psigma (σ : Equiv.Perm (Fin 6)) :
    LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)) :=
  LargeEvenProjMk _ (permGLSU hK σ)

theorem coe_permX (σ : Equiv.Perm (Fin 6)) (x : ↥sumZeroSubgroup) (i : Fin 6) :
    Multiplicative.toAdd (permX σ x : Multiplicative (Fin 6 → ZMod 3)) i =
      Multiplicative.toAdd (x : Multiplicative (Fin 6 → ZMod 3)) (σ.symm i) := rfl

theorem torHom_conj (σ : Equiv.Perm (Fin 6)) (x : ↥sumZeroSubgroup) :
    Psigma (K := K) hK σ * torHom hK hω x * (Psigma (K := K) hK σ)⁻¹ =
      torHom hK hω (permX σ x) := by
  change LargeEvenProjMk _ (permGLSU hK σ) *
      LargeEvenProjMk _ (torLift hK hω x) *
      (LargeEvenProjMk _ (permGLSU hK σ))⁻¹ =
    LargeEvenProjMk _ (torLift hK hω (permX σ x))
  rw [← map_inv, ← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  change (permGLSU hK σ : GL (Fin 6) K) * (torLift hK hω x : GL (Fin 6) K) *
      (permGLSU hK σ : GL (Fin 6) K)⁻¹ =
    (torLift hK hω (permX σ x) : GL (Fin 6) K)
  rw [coe_permGLSU]
  rw [show (torLift hK hω x : GL (Fin 6) K) =
      TauCeti.diagGL (coeffVec hK hω (x : Multiplicative (Fin 6 → ZMod 3))) from rfl]
  rw [show (torLift hK hω (permX σ x) : GL (Fin 6) K) =
      TauCeti.diagGL (coeffVec hK hω (permX σ x : Multiplicative (Fin 6 → ZMod 3)))
      from rfl]
  rw [TauCeti.mul_diagGL_of_coe_eq_permMatrix (g := TauCeti.permutationGL σ) (π := σ⁻¹)
    (TauCeti.permutationGL_coe _)]
  rw [mul_assoc, mul_inv_cancel, mul_one]
  rfl

end CFSG.StandardType.USixTwo.TorConj

namespace CFSG.StandardType.USixTwo.TorConj

open CFSG.Assembly Matrix
open CFSG.StandardType.USixTwo.TorHyperplanes

@[expose] def toT4 (y : Fin 6 → ZMod 3) : T4 := (y 0 - y 5, y 1 - y 5, y 2 - y 5, y 3 - y 5)

@[expose] def permY (σ : Equiv.Perm (Fin 6)) (y : Fin 6 → ZMod 3) : Fin 6 → ZMod 3 :=
  fun i => y (σ i)

@[expose] def permU (σ : Equiv.Perm (Fin 6)) (u : T4) : T4 :=
  toT4 (permY σ (expLift u))

private theorem neg_sum_sub_last {z : Fin 6 → ZMod 3}
    (h4 : z 4 = -(z 0 + z 1 + z 2 + z 3 + z 5)) :
    -((z 0 - z 5) + (z 1 - z 5) + (z 2 - z 5) + (z 3 - z 5)) = z 4 - z 5 := by
  rw [h4]
  have h3 : z 5 + z 5 + z 5 = 0 := by
    have h : ∀ a : ZMod 3, a + a + a = 0 := by decide
    exact h (z 5)
  have hsum : z 5 + (z 5 + z 5) = 0 := by
    rw [show z 5 + (z 5 + z 5) = z 5 + z 5 + z 5 by abel]
    exact h3
  have h2 : z 5 = -(z 5 + z 5) := eq_neg_of_add_eq_zero_left hsum
  calc -((z 0 - z 5) + (z 1 - z 5) + (z 2 - z 5) + (z 3 - z 5))
      = -(z 0 + z 1 + z 2 + z 3) + ((z 5 + z 5 + z 5) + z 5) := by abel
    _ = -(z 0 + z 1 + z 2 + z 3) + z 5 := by
        conv_lhs => rw [h3]
        abel
    _ = -(z 0 + z 1 + z 2 + z 3) + (-(z 5 + z 5)) := by
        conv_lhs => rw [h2]
    _ = -(z 0 + z 1 + z 2 + z 3 + z 5) - z 5 := by
        rw [show -(z 0 + z 1 + z 2 + z 3 + z 5) - z 5 =
            -(z 0 + z 1 + z 2 + z 3) + (-(z 5 + z 5)) by abel]

theorem expLift_toT4 {z : Fin 6 → ZMod 3} (hz : ∑ i, z i = 0) (i : Fin 6) :
    expLift (toT4 z) i = z i - z 5 := by
  have hz' : z 0 + z 1 + z 2 + z 3 + z 4 + z 5 = 0 := by
    simpa [Fin.sum_univ_six] using hz
  have h4 : z 4 = -(z 0 + z 1 + z 2 + z 3 + z 5) := by
    have h : z 4 + (z 0 + z 1 + z 2 + z 3 + z 5) = 0 := by
      rw [show z 4 + (z 0 + z 1 + z 2 + z 3 + z 5) =
          z 0 + z 1 + z 2 + z 3 + z 4 + z 5 by abel]
      exact hz'
    calc z 4 = z 4 + (z 0 + z 1 + z 2 + z 3 + z 5) -
          (z 0 + z 1 + z 2 + z 3 + z 5) := by abel
      _ = 0 - (z 0 + z 1 + z 2 + z 3 + z 5) := by rw [h]
      _ = -(z 0 + z 1 + z 2 + z 3 + z 5) := by abel
  fin_cases i
  · simp [expLift, toT4]
  · simp [expLift, toT4]
  · simp [expLift, toT4]
  · simp [expLift, toT4]
  · simp [expLift, toT4]
    exact neg_sum_sub_last h4
  · simp [expLift, toT4]

theorem fS_permU (σ : Equiv.Perm (Fin 6)) (u : T4) (x : ↥sumZeroSubgroup) :
    fS (permU σ u) x = fS u (permX σ x) := by
  set xi : Fin 6 → ZMod 3 := fun i =>
    Multiplicative.toAdd (x : Multiplicative (Fin 6 → ZMod 3)) i with hxi
  have hx : ∑ i, xi i = 0 := mem_sumZeroSubgroup_iff.mp x.2
  have hsum : ∑ i, permY σ (expLift u) i = 0 :=
    (Equiv.sum_comp σ (expLift u)).trans (sum_expLift u)
  have hlift : ∀ i, expLift (permU σ u) i = expLift u (σ i) - expLift u (σ 5) := by
    intro i
    simpa [permU, permY] using expLift_toT4 hsum i
  rw [fS_apply, fS_apply]
  apply Multiplicative.ofAdd.injective
  simp only [coe_permX]
  calc ∑ i, expLift (permU σ u) i * xi i
      = ∑ i, (expLift u (σ i) - expLift u (σ 5)) * xi i := by
        exact Finset.sum_congr rfl fun i _ => by rw [hlift i]
    _ = ∑ i, expLift u (σ i) * xi i := by
        rw [show ∑ i, (expLift u (σ i) - expLift u (σ 5)) * xi i =
            ∑ i, (expLift u (σ i) * xi i + (-expLift u (σ 5)) * xi i) by
          apply Finset.sum_congr rfl
          intro i _
          rw [sub_eq_add_neg, add_mul]
          abel]
        rw [Finset.sum_add_distrib]
        rw [show ∑ i, (-expLift u (σ 5)) * xi i = 0 by
          rw [← Finset.mul_sum, hx, mul_zero]]
        rw [add_zero]
    _ = ∑ i, expLift u i * xi (σ.symm i) := by
        rw [← Equiv.sum_comp σ (fun i => expLift u i * xi (σ.symm i))]
        simp

end CFSG.StandardType.USixTwo.TorConj

namespace CFSG.StandardType.USixTwo.TorConj

open CFSG.StandardType.USixTwo.TorHyperplanes

@[expose] def delta (j : Fin 5) : Fin 6 → ZMod 3 := ![delta0, delta1, delta2, delta3, delta4] j

theorem sum_delta (j : Fin 5) : ∑ i, delta j i = 0 := by
  fin_cases j <;> simp [delta, sum_delta0, sum_delta1, sum_delta2, sum_delta3, sum_delta4]

theorem delta_mem (j : Fin 5) : Multiplicative.ofAdd (delta j) ∈ sumZeroSubgroup :=
  sum_delta j

@[expose] def s01 : Equiv.Perm (Fin 6) := Equiv.swap 0 1

end CFSG.StandardType.USixTwo.TorConj

namespace CFSG.StandardType.USixTwo.TorConj

open CFSG.StandardType.USixTwo.TorHyperplanes

@[expose] def s12 : Equiv.Perm (Fin 6) := Equiv.swap 1 2
@[expose] def s23 : Equiv.Perm (Fin 6) := Equiv.swap 2 3
@[expose] def s34 : Equiv.Perm (Fin 6) := Equiv.swap 3 4
@[expose] def s45 : Equiv.Perm (Fin 6) := Equiv.swap 4 5

end CFSG.StandardType.USixTwo.TorConj

namespace CFSG.StandardType.USixTwo.TorConj

open CFSG.Assembly Matrix
open CFSG.StandardType.USixTwo.TorHyperplanes

variable {K : Type} [Field K] [Finite K] {ω : K}
variable (hK : Nat.card K = 4) (hω : ω ^ 2 + ω + 1 = 0)

theorem permX_invol_of (σ : Equiv.Perm (Fin 6)) (hσ : ∀ i, σ (σ i) = i)
    (x : ↥sumZeroSubgroup) : permX σ (permX σ x) = x := by
  have hsymm : σ.symm = σ := by
    apply Equiv.ext
    intro i
    exact (Equiv.symm_apply_eq σ).mpr (hσ i).symm
  apply Subtype.ext
  funext i
  simp [permX, hsymm, hσ]

theorem torChart_mk (x : ↥sumZeroSubgroup) :
    torChart hK hω (QuotientGroup.mk x) = torHom hK hω x := by
  simp [torChart, QuotientGroup.quotientKerEquivOfSurjective, QuotientGroup.kerLift_mk]

theorem mem_map_inclusion_conj {P : LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))}
    {H : Subgroup ↥(torU K)} {x : LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))} :
    x ∈ (H.map ((torU K).subtype)).map
        (MulAut.conj P).toMonoidHom ↔
      ∃ a ∈ H, P * (a : LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))) * P⁻¹ = x := by
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨h, hh, hx⟩
    rw [Subgroup.mem_map] at hh
    obtain ⟨a, ha, rfl⟩ := hh
    exact ⟨a, ha, by simpa [MulAut.conj_apply] using hx⟩
  · rintro ⟨a, ha, hx⟩
    exact ⟨↑a, ⟨a, ha, rfl⟩, by simpa [MulAut.conj_apply] using hx⟩

theorem Hfun_conj_of_invol {σ : Equiv.Perm (Fin 6)}
    (hinv : ∀ x : ↥sumZeroSubgroup, permX σ (permX σ x) = x)
    (u : T4) :
    ((Hfun hK hω u).map ((torU K).subtype)).map
        (MulAut.conj (Psigma (K := K) hK σ)).toMonoidHom =
      (Hfun hK hω (permU σ u)).map ((torU K).subtype) := by
  let P := Psigma (K := K) hK σ
  let Q := torChart hK hω
  ext x
  rw [mem_map_inclusion_conj]
  constructor
  · rintro ⟨a, ha, hx⟩
    rw [Hfun, Subgroup.mem_map] at ha
    obtain ⟨q, hq, rfl⟩ := ha
    have hq0 : fS u (Quotient.out q) = 1 := by
      have h := hq
      have h' : fQ hK hω u q = 1 := by simpa [MonoidHom.mem_ker] using h
      rw [← show QuotientGroup.mk (Quotient.out q) = q from Quotient.out_eq' q] at h'
      rw [fQ, QuotientGroup.lift_mk] at h'
      exact h'
    set x0 := Quotient.out q
    have hq_out : QuotientGroup.mk x0 = q := Quotient.out_eq' q
    have hQ : Q q = torHom hK hω x0 := by
      rw [← hq_out]
      exact torChart_mk hK hω x0
    have hx' : x = ↑(torHom hK hω (permX σ x0)) := by
      rw [← hx]
      change P * ↑(Q q) * P⁻¹ = ↑(torHom hK hω (permX σ x0))
      rw [hQ, torHom_conj hK hω σ x0]
    rw [hx']
    rw [Subgroup.mem_map]
    refine ⟨torHom hK hω (permX σ x0), ?_, rfl⟩
    rw [Hfun, Subgroup.mem_map]
    refine ⟨QuotientGroup.mk (permX σ x0), ?_, torChart_mk hK hω _⟩
    change fQ hK hω (permU σ u) (QuotientGroup.mk (permX σ x0)) = 1
    rw [fQ, QuotientGroup.lift_mk]
    rw [fS_permU σ u (permX σ x0), hinv x0]
    exact hq0
  · rintro ⟨b, hb, hb_eq⟩
    simp only [Hfun, Subgroup.mem_map] at hb
    obtain ⟨q, hq, haQ⟩ := hb
    have hq' : fS (permU σ u) (Quotient.out q) = 1 := by
      have h := hq
      have h' : fQ hK hω (permU σ u) q = 1 := by simpa [MonoidHom.mem_ker] using h
      rw [← show QuotientGroup.mk (Quotient.out q) = q from Quotient.out_eq' q] at h'
      rw [fQ, QuotientGroup.lift_mk] at h'
      exact h'
    set x0 := Quotient.out q
    have hq_out : QuotientGroup.mk x0 = q := Quotient.out_eq' q
    have hb_tor : (b : ↥(torU K)) = torHom hK hω x0 := by
      rw [← haQ, ← hq_out]
      exact torChart_mk hK hω x0
    refine ⟨Q (QuotientGroup.mk (permX σ x0)), ?_, ?_⟩
    · rw [Hfun, Subgroup.mem_map]
      refine ⟨QuotientGroup.mk (permX σ x0), ?_, torChart_mk hK hω _⟩
      change fQ hK hω u (QuotientGroup.mk (permX σ x0)) = 1
      rw [fQ, QuotientGroup.lift_mk]
      rw [← fS_permU σ u x0]
      exact hq'
    · rw [← hb_eq]
      change P * ↑(Q (QuotientGroup.mk (permX σ x0))) * P⁻¹ = ↑b
      rw [torChart_mk hK hω (permX σ x0), torHom_conj hK hω σ (permX σ x0), hinv x0]
      rw [show (↑b : LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))) =
        ↑(torHom hK hω x0) from by rw [hb_tor]]

end CFSG.StandardType.USixTwo.TorConj

namespace CFSG.StandardType.USixTwo.TorConj

open CFSG.StandardType.USixTwo.TorHyperplanes

variable {K : Type} [Field K] [Finite K] {ω : K}
variable (hK : Nat.card K = 4) (hω : ω ^ 2 + ω + 1 = 0)

theorem Hfun_conj_s01 (u : T4) :
    ((Hfun hK hω u).map ((torU K).subtype)).map
        (MulAut.conj (Psigma (K := K) hK s01)).toMonoidHom =
      (Hfun hK hω (permU s01 u)).map ((torU K).subtype) :=
  Hfun_conj_of_invol hK hω (permX_invol_of s01 (by decide)) u

theorem Hfun_conj_s12 (u : T4) :
    ((Hfun hK hω u).map ((torU K).subtype)).map
        (MulAut.conj (Psigma (K := K) hK s12)).toMonoidHom =
      (Hfun hK hω (permU s12 u)).map ((torU K).subtype) :=
  Hfun_conj_of_invol hK hω (permX_invol_of s12 (by decide)) u

theorem Hfun_conj_s23 (u : T4) :
    ((Hfun hK hω u).map ((torU K).subtype)).map
        (MulAut.conj (Psigma (K := K) hK s23)).toMonoidHom =
      (Hfun hK hω (permU s23 u)).map ((torU K).subtype) :=
  Hfun_conj_of_invol hK hω (permX_invol_of s23 (by decide)) u

theorem Hfun_conj_s34 (u : T4) :
    ((Hfun hK hω u).map ((torU K).subtype)).map
        (MulAut.conj (Psigma (K := K) hK s34)).toMonoidHom =
      (Hfun hK hω (permU s34 u)).map ((torU K).subtype) :=
  Hfun_conj_of_invol hK hω (permX_invol_of s34 (by decide)) u

theorem Hfun_conj_s45 (u : T4) :
    ((Hfun hK hω u).map ((torU K).subtype)).map
        (MulAut.conj (Psigma (K := K) hK s45)).toMonoidHom =
      (Hfun hK hω (permU s45 u)).map ((torU K).subtype) :=
  Hfun_conj_of_invol hK hω (permX_invol_of s45 (by decide)) u

end CFSG.StandardType.USixTwo.TorConj

namespace CFSG.StandardType.USixTwo.ModuleProof

open CFSG.Assembly
open CFSG.LocalAnalysis.GLTheoremA.H81Orth.Wt
open CFSG.StandardType.USixTwo.TorHyperplanes
open CFSG.StandardType.USixTwo.TorConj

variable {K : Type} [Field K] [Finite K] {ω : K}
variable (hK : Nat.card K = 4) (hω : ω ^ 2 + ω + 1 = 0)
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
variable (ρ : LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)) →* (V ≃ₗ[ZMod 2] V))

noncomputable instance torUCommGroup : CommGroup ↥(torU K) :=
{ (inferInstance : Group ↥(torU K)) with
  mul_comm := by
    intro a b
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul]
    obtain ⟨A, hA, hAeq⟩ := Subgroup.mem_map.mp a.2
    obtain ⟨B, hB, hBeq⟩ := Subgroup.mem_map.mp b.2
    rw [← hAeq, ← hBeq]
    have hcomm : A * B = B * A := by
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul]
      apply Units.ext
      change ((A : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *
          ((B : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) =
        ((B : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *
          ((A : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)
      have hAdiag : (((A : GL (Fin 6) K)) : Matrix (Fin 6) (Fin 6) K).IsDiag := by
        rw [torSU, Subgroup.mem_comap, TauCeti.mem_diagonalTorus_iff] at hA
        exact hA
      have hBdiag : (((B : GL (Fin 6) K)) : Matrix (Fin 6) (Fin 6) K).IsDiag := by
        rw [torSU, Subgroup.mem_comap, TauCeti.mem_diagonalTorus_iff] at hB
        exact hB
      rw [← hAdiag.diagonal_diag, ← hBdiag.diagonal_diag,
        Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
      congr 1
      funext i
      exact mul_comm _ _
    rw [← map_mul, ← map_mul, hcomm] }

@[expose] noncomputable def repTor :
    Representation (ZMod 2) ↥(torU K) V where
  toFun a := (ρ a : V →ₗ[ZMod 2] V)
  map_one' := by
    ext v
    simp
  map_mul' a b := by
    ext v
    change ρ (a * b) v = ρ a (ρ b v)
    rw [map_mul]
    rfl

theorem repTor_apply (a : ↥(torU K)) (v : V) : repTor ρ a v = ρ a v := rfl

attribute [irreducible] repTor

include hK hω in
theorem torU_pow_three (a : ↥(torU K)) : a ^ 3 = 1 := by
  obtain ⟨x, rfl⟩ := CFSG.StandardType.USixTwo.TorHomKernel.torHom_surjective hK hω a
  rw [← map_pow]
  have hx : x ^ 3 = 1 := by
    apply Subtype.ext
    change Multiplicative.toAdd ((x : Multiplicative (Fin 6 → ZMod 3)) ^ 3) =
      Multiplicative.toAdd (1 : Multiplicative (Fin 6 → ZMod 3))
    rw [toAdd_pow, toAdd_one]
    ext i
    simp [show (3 : ZMod 3) = 0 by decide]
  rw [hx, map_one]

theorem fixedSpace_zpowers_eq_eqLocus (a : ↥(torU K)) :
    fixedSpace (repTor ρ) (Subgroup.zpowers a) =
      LinearMap.eqLocus (ρ a : V →ₗ[ZMod 2] V) LinearMap.id := by
  ext v
  rw [mem_fixedSpace, LinearMap.mem_eqLocus]
  constructor
  · intro h
    have h' := h a (Subgroup.mem_zpowers a)
    rwa [repTor_apply] at h'
  · intro h u hu
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
    have h' : (ρ a) v = v := by simpa using h
    have hinv : (ρ a)⁻¹ v = v := by
      calc (ρ a)⁻¹ v = (ρ a)⁻¹ ((ρ a) v) := by rw [h']
        _ = v := (ρ a).symm_apply_apply v
    have hz : ∀ m : ℤ, (ρ a ^ m) v = v := by
      intro m
      induction m using Int.induction_on with
      | zero => simp
      | succ i ih =>
        rw [zpow_add_one, LinearEquiv.mul_apply, h', ih]
      | pred i ih =>
        rw [zpow_sub_one, LinearEquiv.mul_apply, hinv, ih]
    rw [repTor_apply, Subgroup.coe_zpow, map_zpow]
    exact hz n

include hK hω in
theorem finrank_eqLocus_eq (a : ↥(torU K))
    [DecidablePred (fun H : Hyperplane ↥(torU K) 3 => a ∈ H.1)]
    (T : Finset (Hyperplane ↥(torU K) 3))
    (hT : ∀ H : Hyperplane ↥(torU K) 3,
      H ∈ T ↔ weightSpace (repTor ρ) H.1 ≠ ⊥) :
    Module.finrank (ZMod 2) (LinearMap.eqLocus (ρ a : V →ₗ[ZMod 2] V) LinearMap.id) =
      Module.finrank (ZMod 2) (fixedSpace (repTor ρ) ⊤) +
        ∑ H ∈ T.filter (fun H => a ∈ H.1),
          Module.finrank (ZMod 2) (weightSpace (repTor ρ) H.1) := by
  classical
  have h := finrank_fixedSpace_eq (ρ := repTor ρ) (p := 3) (hp := by norm_num)
    (hA := torU_pow_three hK hω) (hpK := by decide) (hT := hT) (U := Subgroup.zpowers a)
  rw [fixedSpace_zpowers_eq_eqLocus (ρ := ρ) (a := a)] at h
  rw [h]
  have hfilter : T.filter (fun H => Subgroup.zpowers a ≤ H.1) =
      T.filter (fun H => a ∈ H.1) := by
    apply Finset.filter_congr
    intro H _
    exact Subgroup.zpowers_le
  rw [hfilter]

include hK hω in
theorem eSub_eq_smith (H : Subgroup ↥(torU K)) :
    eSub H = CFSG.GF2Type.Smith1979.LemmaW.eSub H := by
  classical
  haveI : Finite ↥(torU K) := Nat.finite_of_card_ne_zero (by rw [card_torU hK]; norm_num)
  haveI : Fintype H := Fintype.ofFinite _
  haveI : Fintype ↥(⊤ : Subgroup ↥(torU K)) := Fintype.ofFinite _
  have hodd : Odd (Nat.card H) :=
    Odd.of_dvd_nat (by rw [card_torU hK]; decide) (Subgroup.card_subgroup_dvd_card H)
  rw [eSub, CFSG.GF2Type.Smith1979.LemmaW.eSub,
    ZMod.natCast_eq_one_iff_odd.mpr hodd, inv_one, one_smul]

include hK hω in
theorem weightSpace_eq_smith (H : Subgroup ↥(torU K)) :
    weightSpace (repTor ρ) H =
      CFSG.GF2Type.Smith1979.LemmaW.weightSpace (repTor ρ) H := by
  rw [weightSpace, CFSG.GF2Type.Smith1979.LemmaW.weightSpace,
    eSub_eq_smith hK hω H, eSub_eq_smith hK hω ⊤]

include hK hω in
theorem even_finrank_weightSpace (H : Subgroup ↥(torU K)) :
    Even (Module.finrank (ZMod 2) (weightSpace (repTor ρ) H)) := by
  haveI : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  rw [weightSpace_eq_smith hK hω]
  exact CFSG.GF2Type.Smith1979.LemmaW.even_finrank_weightSpace (ρ := repTor ρ)
    (torU_pow_three hK hω) H

theorem Psigma_inv (σ : Equiv.Perm (Fin 6)) :
    Psigma (K := K) hK σ⁻¹ = (Psigma (K := K) hK σ)⁻¹ := by
  change LargeEvenProjMk _ (permGLSU hK σ⁻¹) =
    (LargeEvenProjMk _ (permGLSU hK σ))⁻¹
  rw [← map_inv]
  congr 1
  apply Subtype.ext
  change (permGLSU hK σ⁻¹ : GL (Fin 6) K) = ((permGLSU hK σ : GL (Fin 6) K))⁻¹
  simpa using congrArg (fun x : ↥(LargeEvenSUGroup (Fin 6) K (2 ^ 1)) =>
    (x : GL (Fin 6) K)) (permGLSU_inv hK σ)

include hK hω in
theorem conj_mem_torU (σ : Equiv.Perm (Fin 6)) (a : ↥(torU K)) :
    Psigma (K := K) hK σ * (a : LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))) *
        (Psigma (K := K) hK σ)⁻¹ ∈ torU K := by
  obtain ⟨x, rfl⟩ := CFSG.StandardType.USixTwo.TorHomKernel.torHom_surjective hK hω a
  rw [torHom_conj hK hω σ x]
  exact (torHom hK hω (permX σ x)).2

include hK hω in
@[expose]
noncomputable def conjAutTor (σ : Equiv.Perm (Fin 6)) :
    ↥(torU K) ≃* ↥(torU K) where
  toFun a :=
    ⟨Psigma (K := K) hK σ * (a : LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))) *
        (Psigma (K := K) hK σ)⁻¹, conj_mem_torU hK hω σ a⟩
  invFun a :=
    ⟨Psigma (K := K) hK σ⁻¹ * (a : LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))) *
        (Psigma (K := K) hK σ⁻¹)⁻¹, conj_mem_torU hK hω σ⁻¹ a⟩
  left_inv a := by
    apply Subtype.ext
    change Psigma (K := K) hK σ⁻¹ *
        (Psigma (K := K) hK σ * (a : LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))) *
          (Psigma (K := K) hK σ)⁻¹) * (Psigma (K := K) hK σ⁻¹)⁻¹ =
      (a : LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
    rw [Psigma_inv hK σ]
    group
  right_inv a := by
    apply Subtype.ext
    change Psigma (K := K) hK σ *
        (Psigma (K := K) hK σ⁻¹ * (a : LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))) *
          (Psigma (K := K) hK σ⁻¹)⁻¹) * (Psigma (K := K) hK σ)⁻¹ =
      (a : LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
    rw [Psigma_inv hK σ]
    group
  map_mul' a b := by
    apply Subtype.ext
    change Psigma (K := K) hK σ *
        ((a : LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))) *
          (b : LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))) *
        (Psigma (K := K) hK σ)⁻¹ =
      (Psigma (K := K) hK σ * (a : LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))) *
          (Psigma (K := K) hK σ)⁻¹) *
        (Psigma (K := K) hK σ * (b : LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))) *
          (Psigma (K := K) hK σ)⁻¹)
    group

theorem finrank_weightSpace_conj (σ : Equiv.Perm (Fin 6))
    (H : Subgroup ↥(torU K)) :
    Module.finrank (ZMod 2) (weightSpace (repTor ρ)
        (H.map (conjAutTor hK hω σ).toMonoidHom)) =
      Module.finrank (ZMod 2) (weightSpace (repTor ρ) H) := by
  rw [weightSpace_eq_smith hK hω, weightSpace_eq_smith hK hω]
  let b : V ≃ₗ[ZMod 2] V := ρ (Psigma (K := K) hK σ)
  have hb : ∀ (a : ↥(torU K)) (v : V),
      (repTor ρ) (conjAutTor hK hω σ a) (b v) = b ((repTor ρ) a v) := by
    intro a v
    rw [repTor_apply, repTor_apply]
    change ρ (conjAutTor hK hω σ a) (ρ (Psigma (K := K) hK σ) v) =
      ρ (Psigma (K := K) hK σ) (ρ a v)
    change ρ (Psigma (K := K) hK σ * (a : LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))) *
        (Psigma (K := K) hK σ)⁻¹) (ρ (Psigma (K := K) hK σ) v) =
      ρ (Psigma (K := K) hK σ) (ρ a v)
    rw [map_mul, map_mul, map_inv]
    change (ρ (Psigma (K := K) hK σ) * ρ a * (ρ (Psigma (K := K) hK σ))⁻¹)
      (ρ (Psigma (K := K) hK σ) v) = ρ (Psigma (K := K) hK σ) (ρ a v)
    simp [LinearEquiv.mul_apply]
  exact CFSG.GF2Type.Smith1979.LemmaW.finrank_weightSpace_map (ρ := repTor ρ)
    (torU_pow_three hK hω) (b := b) (σ := conjAutTor hK hω σ) hb H

end CFSG.StandardType.USixTwo.ModuleProof

namespace CFSG.StandardType.USixTwo.OrbitProof

open CFSG.Assembly
open CFSG.StandardType.USixTwo
open CFSG.StandardType.USixTwo.TorHyperplanes
open CFSG.StandardType.USixTwo.TorConj

@[expose] def lineCanon (u : T4) : T4 :=
  if u.1 ≠ 0 then smulT4 u.1⁻¹ u
  else if u.2.1 ≠ 0 then smulT4 u.2.1⁻¹ u
  else if u.2.2.1 ≠ 0 then smulT4 u.2.2.1⁻¹ u
  else if u.2.2.2 ≠ 0 then smulT4 u.2.2.2⁻¹ u
  else 0

@[expose] def lineReps : Finset T4 :=
  (Finset.univ.filter (fun u : T4 => u ≠ 0)).image lineCanon

@[expose] def lineStep (σ : Equiv.Perm (Fin 6)) (u : T4) : T4 :=
  lineCanon (CFSG.StandardType.USixTwo.TorConj.permU σ u)

@[expose] def stepSet (u : T4) : Finset T4 :=
  {lineStep s01 u, lineStep s12 u, lineStep s23 u, lineStep s34 u, lineStep s45 u}

@[expose] def reach (base : T4) : ℕ → Finset T4
  | 0 => {base}
  | n + 1 => reach base n ∪ (reach base n).biUnion stepSet

@[expose] def base₁ : T4 := (1, 1, 1, 0)
@[expose] def base₂ : T4 := (0, 0, 0, 1)
@[expose] def base₃ : T4 := (1, 1, 2, 2)

@[expose] def O₁ : Finset T4 := reach base₁ 6
@[expose] def O₂ : Finset T4 := reach base₂ 6
@[expose] def O₃ : Finset T4 := reach base₃ 6

theorem O₁_card : O₁.card = 10 := by decide +kernel
theorem O₂_card : O₂.card = 15 := by decide +kernel
theorem O₃_card : O₃.card = 15 := by decide +kernel
theorem lineReps_partition : lineReps = O₁ ∪ O₂ ∪ O₃ := by decide +kernel
theorem O₁_disjoint_O₂ : Disjoint O₁ O₂ := by decide +kernel
theorem O₁_disjoint_O₃ : Disjoint O₁ O₃ := by decide +kernel
theorem O₂_disjoint_O₃ : Disjoint O₂ O₃ := by decide +kernel
theorem O₁_threeA_count : (O₁.filter (fun u => u.1 = u.2.1)).card = 4 := by decide +kernel
theorem O₂_threeA_count : (O₂.filter (fun u => u.1 = u.2.1)).card = 6 := by decide +kernel
theorem O₃_threeA_count : (O₃.filter (fun u => u.1 = u.2.1)).card = 3 := by decide +kernel

end CFSG.StandardType.USixTwo.OrbitProof

end
