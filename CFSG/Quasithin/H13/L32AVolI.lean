module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Action.Concrete
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.GroupTheory.Nilpotent
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

namespace CFSG.Quasithin.H6

open scoped MatrixGroups

abbrev Γ : Type := SL(3, ZMod 2)

abbrev V3 : Type := Fin 3 → ZMod 2

@[expose] def Lp : Subgroup Γ := MulAction.stabilizer Γ (![1, 0, 0] : V3)

@[expose] def IsLl (g : Γ) : Prop :=
  (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) 2 0 = 0 ∧ (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) 2 1 = 0

instance : DecidablePred IsLl := fun _ => inferInstanceAs (Decidable (_ ∧ _))

theorem isLl_mul : ∀ g h : Γ, IsLl g → IsLl h → IsLl (g * h) := by
  decide +kernel

theorem isLl_inv : ∀ g : Γ, IsLl g → IsLl g⁻¹ := by
  decide +kernel

@[expose] def Ll : Subgroup Γ where
  carrier := {g | IsLl g}
  one_mem' := by decide
  mul_mem' {g h} hg hh := isLl_mul g h hg hh
  inv_mem' {g} hg := isLl_inv g hg

@[expose] def borel : Subgroup Γ := Lp ⊓ Ll

@[expose] def stSub : AddSubgroup (Matrix (Fin 3) (Fin 3) (ZMod 2)) :=
  (Matrix.traceAddMonoidHom (Fin 3) (ZMod 2)).ker

abbrev St : Type := ↥stSub

instance : AddCommGroup St := AddSubgroup.toAddCommGroup stSub

theorem mem_stSub {A : Matrix (Fin 3) (Fin 3) (ZMod 2)} : A ∈ stSub ↔ A.trace = 0 := Iff.rfl

instance : DecidablePred (· ∈ stSub) := fun _ => decidable_of_iff _ mem_stSub.symm

theorem trace_conj (g : Γ) (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) :
    ((g : Matrix (Fin 3) (Fin 3) (ZMod 2)) * A *
      ((g⁻¹ : Γ) : Matrix (Fin 3) (Fin 3) (ZMod 2))).trace = A.trace := by
  rw [Matrix.trace_mul_cycle, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
    Matrix.SpecialLinearGroup.coe_one, Matrix.one_mul]

@[expose] def stSmul (g : Γ) (A : St) : St :=
  ⟨(g : Matrix (Fin 3) (Fin 3) (ZMod 2)) * A.1 * ((g⁻¹ : Γ) : Matrix (Fin 3) (Fin 3) (ZMod 2)),
    mem_stSub.mpr (by rw [trace_conj]; exact mem_stSub.mp A.2)⟩

instance : SMul Γ St := ⟨stSmul⟩

theorem coe_smul_st (g : Γ) (A : St) :
    ((g • A : St) : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
      (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) * A * ((g⁻¹ : Γ) : Matrix (Fin 3) (Fin 3) (ZMod 2)) :=
  rfl

instance : DistribMulAction Γ St where
  one_smul A := Subtype.ext (by rw [coe_smul_st]; simp)
  mul_smul g h A := Subtype.ext (by
    rw [coe_smul_st, coe_smul_st, coe_smul_st, mul_inv_rev, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_mul]
    simp only [Matrix.mul_assoc])
  smul_zero g := Subtype.ext (by rw [coe_smul_st]; simp)
  smul_add g A B := Subtype.ext (by
    rw [coe_smul_st, AddSubgroup.coe_add, AddSubgroup.coe_add, coe_smul_st, coe_smul_st,
      Matrix.mul_add, Matrix.add_mul])

@[expose] def vecOf (i : Fin 8) : V3 :=
  ![((i : ℕ) % 2 : ℕ), ((i : ℕ) / 2 % 2 : ℕ), ((i : ℕ) / 4 % 2 : ℕ)]

@[expose] def idxOf (v : V3) : Fin 8 :=
  ⟨(v 0).val + 2 * (v 1).val + 4 * (v 2).val, by
    have h0 := (v 0).isLt
    have h1 := (v 1).isLt
    have h2 := (v 2).isLt
    simp only [ZMod.val] at h0 h1 h2 ⊢
    omega⟩

theorem idxOf_vecOf : ∀ i : Fin 8, idxOf (vecOf i) = i := by decide

theorem vecOf_idxOf : ∀ v : V3, vecOf (idxOf v) = v := by decide

@[expose] def vecEquiv : Fin 8 ≃ V3 where
  toFun := vecOf
  invFun := idxOf
  left_inv := idxOf_vecOf
  right_inv := vecOf_idxOf

@[expose] def permOf (g : Γ) : Equiv.Perm (Fin 8) :=
  (vecEquiv.trans (MulAction.toPerm (g⁻¹ : Γ))).trans vecEquiv.symm

theorem permOf_apply (g : Γ) (i : Fin 8) : permOf g i = idxOf (g⁻¹ • vecOf i) := rfl

theorem permOf_zero (g : Γ) : permOf g 0 = 0 := by
  rw [permOf_apply, show vecOf 0 = 0 by decide, smul_zero]
  decide

@[expose] def coreSub : AddSubgroup (Fin 8 → ZMod 2) :=
  (Pi.evalAddMonoidHom (fun _ : Fin 8 => ZMod 2) 0).ker ⊓
    (∑ i, Pi.evalAddMonoidHom (fun _ : Fin 8 => ZMod 2) i).ker

abbrev Core : Type := ↥coreSub

instance : AddCommGroup Core := AddSubgroup.toAddCommGroup coreSub

theorem mem_coreSub {f : Fin 8 → ZMod 2} : f ∈ coreSub ↔ f 0 = 0 ∧ ∑ i, f i = 0 := by
  simp [coreSub, AddMonoidHom.mem_ker]

instance : DecidablePred (· ∈ coreSub) := fun _ => decidable_of_iff _ mem_coreSub.symm

@[expose] def coreSmul (g : Γ) (f : Core) : Core :=
  ⟨fun i => f.1 (permOf g i), by
    rw [mem_coreSub]
    refine ⟨by rw [permOf_zero]; exact (mem_coreSub.mp f.2).1, ?_⟩
    rw [Equiv.sum_comp (permOf g) f.1]
    exact (mem_coreSub.mp f.2).2⟩

instance : SMul Γ Core := ⟨coreSmul⟩

theorem coe_smul_core (g : Γ) (f : Core) (i : Fin 8) : (g • f : Core).1 i = f.1 (permOf g i) :=
  rfl

theorem permOf_mul (g h : Γ) (i : Fin 8) : permOf (g * h) i = permOf h (permOf g i) := by
  rw [permOf_apply, permOf_apply, permOf_apply, vecOf_idxOf, mul_inv_rev, mul_smul]

instance : DistribMulAction Γ Core where
  one_smul f := Subtype.ext (funext fun i => by
    rw [coe_smul_core, permOf_apply, inv_one, one_smul, idxOf_vecOf])
  mul_smul g h f := Subtype.ext (funext fun i => by
    rw [coe_smul_core, coe_smul_core, coe_smul_core, permOf_mul])
  smul_zero g := Subtype.ext (funext fun i => rfl)
  smul_add g f f' := Subtype.ext (funext fun i => rfl)

abbrev ρV : Γ →* AddMonoid.End V3 := DistribMulAction.toAddMonoidEnd Γ V3

abbrev ρSt : Γ →* AddMonoid.End St := DistribMulAction.toAddMonoidEnd Γ St

abbrev ρCore : Γ →* AddMonoid.End Core := DistribMulAction.toAddMonoidEnd Γ Core

@[expose] def prodRep {M N : Type} [AddGroup M] [AddGroup N] (ρ : Γ →* AddMonoid.End M)
    (σ : Γ →* AddMonoid.End N) : Γ →* AddMonoid.End (M × N) where
  toFun g := (ρ g).prodMap (σ g)
  map_one' := by
    rw [map_one, map_one]
    rfl
  map_mul' g h := by
    rw [map_mul, map_mul]
    rfl

theorem prodRep_apply {M N : Type} [AddGroup M] [AddGroup N] (ρ : Γ →* AddMonoid.End M)
    (σ : Γ →* AddMonoid.End N) (g : Γ) (x : M × N) : prodRep ρ σ g x = (ρ g x.1, σ g x.2) := rfl

@[expose] def IsoMod {M N : Type} [AddGroup M] [AddGroup N] (ρ : Γ →* AddMonoid.End M)
    (σ : Γ →* AddMonoid.End N) : Prop :=
  ∃ f : N →+ M, Function.Bijective f ∧ ∀ (g : Γ) (x : N), f (σ g x) = ρ g (f x)

@[expose] def VolI_H_6_3 : Prop :=
  (∀ (M : Type) [AddGroup M] [Finite M] (ρ : Γ →* AddMonoid.End M), (∀ m : M, m + m = 0) →
    ∀ f : M →+ St, Function.Surjective f → (∀ (g : Γ) (m : M), f (ρ g m) = ρSt g (f m)) →
      ∃ s : St →+ M, (∀ x, f (s x) = x) ∧ ∀ (g : Γ) (x : St), s (ρSt g x) = ρ g (s x)) ∧
  (∀ (M : Type) [AddGroup M] [Finite M] (ρ : Γ →* AddMonoid.End M), (∀ m : M, m + m = 0) →
    ∀ f : St →+ M, Function.Injective f → (∀ (g : Γ) (x : St), f (ρSt g x) = ρ g (f x)) →
      ∃ p : M →+ St, (∀ x, p (f x) = x) ∧ ∀ (g : Γ) (m : M), p (ρ g m) = ρSt g (p m)) ∧
  (∃ B : St →+ St →+ ZMod 2, (∀ x : St, (∀ y, B x y = 0) → x = 0) ∧
    ∀ (g : Γ) (x y : St), B (ρSt g x) (ρSt g y) = B x y) ∧
  (∀ α : Γ ≃* Γ, IsoMod ρSt (ρSt.comp α.toMonoidHom)) ∧
  (∀ x : Γ, x ∈ Lp ∨ x ∈ Ll → x ^ 3 = 1 → x ≠ 1 → Nat.card {m : St // ρSt x m = m} = 4) ∧
  (∃ m : St, m ≠ 0 ∧ (∀ t ∈ borel, ρSt t m = m) ∧
    ∀ m' : St, m' ≠ 0 → (∀ t ∈ borel, ρSt t m' = m') → m' = m) ∧
  (∀ m : St, m ≠ 0 → (∀ t ∈ borel, ρSt t m = m) → ∀ g : Γ, ρSt g m = m → g ∈ borel) ∧
  AddSubgroup.closure {y : St | ∃ g ∈ Ll, ∃ m : St, y = ρSt g m - m} = ⊤ ∧
  AddSubgroup.closure {y : St | ∃ g ∈ Lp, ∃ m : St, y = ρSt g m - m} = ⊤

@[expose] def VolI_H_6_5 : Prop :=
  ∀ (M : Type) [AddGroup M] [Finite M] (ρ : Γ →* AddMonoid.End M), (∀ m : M, m + m = 0) →
    (∀ g : Γ, (∀ m : M, ρ g m = m) → g = 1) →
    ∀ m : M, (∀ t ∈ borel, ρ t m = m) →
      AddSubgroup.closure (Set.range fun g : Γ => ρ g m) = ⊤ →
      Nat.card ↥(AddSubgroup.closure {y | ∃ g ∈ Ll, ρ g m = y}) = 4 →
      (∃ f : Core × St →+ M, Function.Surjective f ∧
        ∀ (g : Γ) (x : Core × St), f (prodRep ρCore ρSt g x) = ρ g (f x)) ∧
      (IsoMod ρ ρCore ∨ IsoMod ρ ρSt ∨ IsoMod ρ ρV ∨ IsoMod ρ (prodRep ρV ρSt) ∨
        IsoMod ρ (prodRep ρCore ρSt))

end CFSG.Quasithin.H6
