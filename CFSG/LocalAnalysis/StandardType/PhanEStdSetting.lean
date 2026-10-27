module

public import CFSG.LocalAnalysis.StandardType.PhanEStdFlip
public import CFSG.LocalAnalysis.StandardType.PhanEBridgeDefs
public import CFSG.LieType.Steinberg.PartB
public import CFSG.ClassicalInvolution.WeakCT.Sides
public import CFSG.ClassicalInvolution.WeakCT.Torus
public import CFSG.ClassicalInvolution.WeakCT.Main
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanEDefs

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE

open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem CFSG.LieType.Steinberg
  CFSG.LieType.Chevalley.CosetBuilding CFSG.Monster.B.Geometry CFSG.LieType.Universal.Unitary
  CFSG.LieType.BorelTits CFSG.ClassicalGroups.Unitary
open scoped MatrixGroups

section Fixed

variable {K : Type} [Group K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K}
  {w₀ : (coxeterMatrix D.isFiniteType).Group} (F : FrobData D n H w₀)

@[expose] def stdTau (n₀ : K) : K →* K :=
  (MulAut.conj n₀).toMonoidHom.comp F.φ

theorem stdTau_apply (n₀ g : K) : stdTau F n₀ g = n₀ * F.φ g * n₀⁻¹ :=
  rfl

@[expose] def stdFix (n₀ : K) : Subgroup K :=
  (stdTau F n₀).eqLocus (MonoidHom.id K)

theorem mem_stdFix_iff (n₀ g : K) : g ∈ stdFix F n₀ ↔ n₀ * F.φ g * n₀⁻¹ = g :=
  Iff.rfl

@[expose] def frobFix : Subgroup K :=
  F.φ.eqLocus (MonoidHom.id K)

theorem mem_frobFix_iff (g : K) : g ∈ frobFix F ↔ F.φ g = g :=
  Iff.rfl

end Fixed

section SL

variable {Fld : Type} [Field Fld] (θ : Fld →+* Fld)

@[expose] def slSigma (m : ℕ) : SL(m, Fld) →* SL(m, Fld) where
  toFun A := (Matrix.SpecialLinearGroup.transpose (Matrix.SpecialLinearGroup.map θ A))⁻¹
  map_one' := by
    refine Subtype.ext ?_
    simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.SpecialLinearGroup.coe_transpose]
  map_mul' A B := by
    refine Subtype.ext ?_
    simp only [Matrix.SpecialLinearGroup.coe_inv, Matrix.SpecialLinearGroup.coe_transpose,
      map_mul, Matrix.SpecialLinearGroup.coe_mul, Matrix.transpose_mul,
      Matrix.adjugate_mul_distrib]

theorem coe_slSigma (m : ℕ) (A : SL(m, Fld)) :
    ((slSigma θ m A : SL(m, Fld)) : Matrix (Fin m) (Fin m) Fld) =
      Matrix.adjugate (Matrix.transpose ((A : Matrix (Fin m) (Fin m) Fld).map θ)) :=
  rfl

@[expose] def slSU (m : ℕ) : Subgroup SL(m, Fld) :=
  (slSigma θ m).eqLocus (MonoidHom.id _)

theorem mem_slSU_iff (m : ℕ) (A : SL(m, Fld)) : A ∈ slSU θ m ↔ slSigma θ m A = A :=
  Iff.rfl

end SL

section SU

variable {Kf : Type} [Field Kf] [Finite Kf] {f : ℕ} [CharP Kf 2] {Fld : Type} [Field Fld]

@[expose] noncomputable def suToSLSelf (m : ℕ) : Su Kf 2 f m →* SL(m, Kf) where
  toFun A := ⟨((A : GL (Fin m) Kf) : Matrix (Fin m) (Fin m) Kf), A.2.1⟩
  map_one' := rfl
  map_mul' _ _ := rfl

@[expose] noncomputable def suToSL (κ : Kf ≃+* Fld) (m : ℕ) : Su Kf 2 f m →* SL(m, Fld) :=
  (Matrix.SpecialLinearGroup.map (κ : Kf →+* Fld)).comp (suToSLSelf m)

theorem coe_suToSL (κ : Kf ≃+* Fld) (m : ℕ) (A : Su Kf 2 f m) :
    ((suToSL κ m A : SL(m, Fld)) : Matrix (Fin m) (Fin m) Fld) =
      (((A : GL (Fin m) Kf) : Matrix (Fin m) (Fin m) Kf)).map κ :=
  rfl

end SU

section Levi

variable {K : Type} [Group K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K}
  {w₀ : (coxeterMatrix D.isFiniteType).Group}

structure StdLevi (F : FrobData D n H w₀) (n₀ : K) where
  Fld : Type
  [instField : Field Fld]
  θ : Fld →+* Fld
  θ_invol : ∀ c, θ (θ c) = c
  norm_surj : ∀ s : Fld, s ≠ 0 → θ s = s → ∃ a : Fld, a * θ a = s
  ε : Fin D.rank → SL(2, Fld) →* K
  ε_inj : ∀ i, Function.Injective (ε i)
  upper : ∀ i, Set.range (fun c => ε i (sl2Upper c)) = (D.rootGroup (Pi.single i 1) : Set K)
  lower : ∀ i, Set.range (fun c => ε i (sl2Lower c)) = (D.rootGroup (-Pi.single i 1) : Set K)
  diag : ∀ i, Set.range (fun s => ε i (WeakCT.torusHom Fld s)) = (H i : Set K)
  weyl : ∀ i, ε i (sl2Upper 1 * sl2Lower (-1) * sl2Upper 1) = n i
  phi_upper : ∀ i c, F.φ (ε i (sl2Upper c)) = ε (F.op i) (sl2Upper (θ c))
  phi_lower : ∀ i c, F.φ (ε i (sl2Lower c)) = ε (F.op i) (sl2Lower (θ c))
  conj_upper : ∀ i c, n₀ * ε (F.op i) (sl2Upper c) * n₀⁻¹ = ε i (sl2Lower (-c))
  conj_lower : ∀ i c, n₀ * ε (F.op i) (sl2Lower c) * n₀⁻¹ = ε i (sl2Upper (-c))
  ε₂ : Fin D.rank → Fin D.rank → SL(3, Fld) →* K
  ε₂_inj : ∀ i j, i < j → coxeterMatrix D.isFiniteType i j = 3 → Function.Injective (ε₂ i j)
  ε₂_left : ∀ i j, i < j → coxeterMatrix D.isFiniteType i j = 3 →
    (ε₂ i j).comp (WeakCT.blk Fld 0) = ε i
  ε₂_right : ∀ i j, i < j → coxeterMatrix D.isFiniteType i j = 3 →
    (ε₂ i j).comp (WeakCT.blk Fld 1) = ε j

attribute [instance] StdLevi.instField

end Levi

end CFSG.ClassicalInvolution.Phan.PhanE
