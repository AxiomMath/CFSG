module

public import CFSG.LocalAnalysis.StandardType.GGQTwoLin
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Data.Matrix.Mul

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module QTwoLin

abbrev GGBCV (n : ℕ) : Type := Fin n → ZMod 3

instance ggBCModule (n : ℕ) : @Module (ZMod 3) (Fin n → ZMod 3) _ (AddCommGroup.toAddCommMonoid) :=
  Pi.module _ _ _

@[expose] def ggBCWt {n : ℕ} (v : GGBCV n) : ℕ := (Finset.univ.filter fun i => v i ≠ 0).card

@[expose] def ggBCRoots (n : ℕ) : Set (GGBCV n) := {v | 1 ≤ ggBCWt v ∧ ggBCWt v ≤ 2}

@[expose] noncomputable def ggBCDot {n : ℕ} (c : GGBCV n) : Module.Dual (ZMod 3) (GGBCV n) :=
  ∑ i, c i • LinearMap.proj i

@[expose] noncomputable def ggBCRefl {n : ℕ} (c : GGBCV n) (hc : c ⬝ᵥ c ≠ 0) :
    GGBCV n ≃ₗ[ZMod 3] GGBCV n :=
  Module.reflection (show ((2 / (c ⬝ᵥ c)) • ggBCDot c) c = 2 by
    simp only [LinearMap.smul_apply, ggBCDot, LinearMap.sum_apply, LinearMap.proj_apply,
      smul_eq_mul]
    rw [show (∑ i, c i * c i) = c ⬝ᵥ c from rfl]
    field_simp)

@[expose] def ggBCReflSet {n : ℕ} (S : Set (GGBCV n)) : Set (GGBCV n ≃ₗ[ZMod 3] GGBCV n) :=
  {t | ∃ c ∈ S, ∃ hc : c ⬝ᵥ c ≠ 0, t = ggBCRefl c hc}

@[expose] noncomputable def ggBCW (n : ℕ) : Subgroup (GGBCV n ≃ₗ[ZMod 3] GGBCV n) :=
  Subgroup.closure (ggBCReflSet (ggBCRoots n))

@[expose] def ggBCRootsLam1 (n : ℕ) [NeZero n] : Set (GGBCV n) :=
  {v | v ∈ ggBCRoots n ∧ v 0 = 0}

@[expose] def ggBCRootsLamN (n : ℕ) : Set (GGBCV n) := {v | ggBCWt v = 2 ∧ ∑ i, v i = 0}

end CFSG.StandardType

end
