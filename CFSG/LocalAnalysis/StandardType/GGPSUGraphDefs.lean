module

public import CFSG.LocalAnalysis.StandardType.GGOuterInvAtPSU

public section

namespace CFSG.StandardType

open CFSG.StandardType.ClassicalPosition
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.LieType.BorelTits (unitaryInvolution)

abbrev psuJ (n : ℕ) (K : Type) [Field K] : Matrix (Fin n) (Fin n) K :=
  ((AutPSU.gramJ n : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)

noncomputable abbrev psuAlpha {f n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    (h : UnitaryFieldData 2 f K) (i : MulAut (AutPSU.PJ h n)) : MulAut (AutPSU.PJ h n) :=
  i * primeFormFieldHom h AutPSU.isPrimeFormGram_gramJ (unitaryInvolution K 2 f)

noncomputable abbrev psuDag {f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)
    (a : Matrix (Fin n) (Fin n) K) : Matrix (Fin n) (Fin n) K :=
  formAdj h.bar (psuJ n K) a

@[expose] noncomputable def psuTheta {f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)
    (X : GL (Fin n) K) (a : Matrix (Fin n) (Fin n) K) : Matrix (Fin n) (Fin n) K :=
  (X : Matrix (Fin n) (Fin n) K) * a.map h.bar * ((X⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)

@[expose] noncomputable def psuPsi {f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)
    (X : GL (Fin n) K) (a : Matrix (Fin n) (Fin n) K) : Matrix (Fin n) (Fin n) K :=
  psuTheta h X (psuDag h a)

@[expose] def psuChat {f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K) (B : GL (Fin n) K) :
    Subgroup (AutPSU.XJ h n) where
  carrier := {x | ∃ c : Kˣ, ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      (B : Matrix (Fin n) (Fin n) K) = (c : K) • ((B : Matrix (Fin n) (Fin n) K) *
      ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))}
  one_mem' := ⟨1, by simp⟩
  mul_mem' := by
    rintro x y ⟨c, hc⟩ ⟨c', hc'⟩
    refine ⟨c' * c, ?_⟩
    change ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      (B : Matrix (Fin n) (Fin n) K) = ((c' * c : Kˣ) : K) • ((B : Matrix (Fin n) (Fin n) K) *
      (((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)))
    rw [Matrix.mul_assoc, hc', Matrix.mul_smul, ← Matrix.mul_assoc, hc, Matrix.smul_mul,
      smul_smul, Units.val_mul, Matrix.mul_assoc]
  inv_mem' := by
    rintro x ⟨c, hc⟩
    refine ⟨c⁻¹, ?_⟩
    have hx : ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        (((x⁻¹ : AutPSU.XJ h n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
      rw [← Units.val_mul]; simp
    have hx' : (((x⁻¹ : AutPSU.XJ h n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
      rw [← Units.val_mul]; simp
    change (((x⁻¹ : AutPSU.XJ h n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      (B : Matrix (Fin n) (Fin n) K) = ((c⁻¹ : Kˣ) : K) • ((B : Matrix (Fin n) (Fin n) K) *
      (((x⁻¹ : AutPSU.XJ h n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
    set X := ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hXdef
    set Y := (((x⁻¹ : AutPSU.XJ h n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hYdef
    have e1 : (B : Matrix (Fin n) (Fin n) K) * Y = Y * (X * (B : Matrix (Fin n) (Fin n) K)) * Y := by
      rw [← Matrix.mul_assoc Y X, hx', Matrix.one_mul]
    have e2 : Y * (X * (B : Matrix (Fin n) (Fin n) K)) * Y =
        (c : K) • (Y * (B : Matrix (Fin n) (Fin n) K)) := by
      rw [hc, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc, Matrix.mul_assoc, hx,
        Matrix.mul_one]
    rw [e2] at e1
    rw [e1, smul_smul, Units.inv_mul, one_smul]


abbrev psuAlg {n : ℕ} {K : Type} [Field K] (B : GL (Fin n) K) :
    Subalgebra K (Matrix (Fin n) (Fin n) K) :=
  Algebra.adjoin K (Units.val '' ({B} : Set (GL (Fin n) K)))

@[expose] noncomputable def psuOrbitIdem {f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)
    (e : Matrix (Fin n) (Fin n) K) : Matrix (Fin n) (Fin n) K :=
  open Classical in if psuDag h e = e then e else e + psuDag h e

noncomputable abbrev psuBlock {f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)
    (B : GL (Fin n) K) (e : Matrix (Fin n) (Fin n) K) : Subgroup (AutPSU.XJ h n) :=
  glBlockCentralizer (AutPSU.XJ h n).subtype ({B} : Set (GL (Fin n) K)) (psuOrbitIdem h e)

@[expose] def psuPsiTrivial {f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K) (X B : GL (Fin n) K)
    (e : Matrix (Fin n) (Fin n) K) : Prop :=
  ∀ a ∈ psuAlg B, psuPsi h X (a * e) = a * e

@[expose] noncomputable def psuKind {f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)
    (X B : GL (Fin n) K) (e : Matrix (Fin n) (Fin n) K) : ℕ :=
  open Classical in
  if psuDag h e = e then (if psuPsi h X e = e then 0 else 1)
  else if psuPsi h X e = e then (if psuPsiTrivial h X B e then 2 else 3)
  else if psuPsi h X e = psuDag h e then 4 else 5

@[expose] def psuUnitaryPart {f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)
    (B : GL (Fin n) K) : Set (Matrix (Fin n) (Fin n) K) :=
  {t | t ∈ psuAlg B ∧ psuDag h t * t = 1}

@[expose] def psuNormImage {f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)
    (X B : GL (Fin n) K) : Set (Matrix (Fin n) (Fin n) K) :=
  {m | ∃ t ∈ psuUnitaryPart h B, m = psuPsi h X t * t}

structure PSUGraphSetting {f : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    (h : UnitaryFieldData 2 f K) (n : ℕ) (X B : GL (Fin n) K) : Prop where
  four_le : 4 ≤ n
  X_mem : X ∈ primeFormUnitary h (psuJ n K)
  X_sq : (X : Matrix (Fin n) (Fin n) K) * (X : Matrix (Fin n) (Fin n) K).map h.bar = 1
  B_mem : B ∈ primeFormUnitary h (psuJ n K)
  odd : Odd (orderOf B)
  theta_B : ∃ c : Kˣ, psuTheta h X (B : Matrix (Fin n) (Fin n) K) =
    (c : K) • (B : Matrix (Fin n) (Fin n) K)
  fix : ∀ x ∈ psuChat h B, ∃ d : Kˣ, psuTheta h X ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
    (d : K) • ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
  not_all : ∃ x : AutPSU.XJ h n, ∀ d : Kˣ,
    psuTheta h X ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ≠
      (d : K) • ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)

end CFSG.StandardType
