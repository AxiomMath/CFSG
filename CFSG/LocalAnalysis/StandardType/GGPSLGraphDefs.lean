module

public import CFSG.LocalAnalysis.StandardType.GGOuterInvAtPSL

public section

namespace CFSG.StandardType

open CFSG.StandardType.ClassicalPosition Matrix
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag

noncomputable abbrev pslAlpha {n : ℕ} {K : Type} [Field K] [CharP K 2] (A : GL (Fin n) K) :
    MulAut (projectiveSL n K) :=
  conjAut n K A * AutPSL.graphAut

@[expose] noncomputable def pslCent {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2] (B : GL (Fin n) K) :
    Subgroup (projectiveSL n K) :=
  MonoidHom.eqLocus (conjAut n K B).toMonoidHom (MonoidHom.id _)

@[expose] noncomputable def pslChat {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    (B : GL (Fin n) K) : Subgroup (SpecialLinearGroup (Fin n) K) :=
  (pslCent B).comap (proj n K)

abbrev pslAlg {n : ℕ} {K : Type} [Field K] (B : GL (Fin n) K) :
    Subalgebra K (Matrix (Fin n) (Fin n) K) :=
  Algebra.adjoin K (Units.val '' ({B} : Set (GL (Fin n) K)))

abbrev pslBlock {n : ℕ} {K : Type} [Field K] (B : GL (Fin n) K) (e : Matrix (Fin n) (Fin n) K) :
    Subgroup (SpecialLinearGroup (Fin n) K) :=
  glBlockCentralizer SpecialLinearGroup.toGL ({B} : Set (GL (Fin n) K)) e

structure PSLGraphSetting (n : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2]
    (G : Matrix (Fin n) (Fin n) K) (B : GL (Fin n) K) : Prop where
  three_le : 3 ≤ n
  symm : Gᵀ = G
  det_isUnit : IsUnit G.det
  odd : Odd (orderOf B)
  star_mul : ∃ c : Kˣ,
    formAdj (RingHom.id K) G (B : Matrix (Fin n) (Fin n) K) * (B : Matrix (Fin n) (Fin n) K) =
      (c : K) • (1 : Matrix (Fin n) (Fin n) K)
  fix : ∀ x ∈ pslChat B, ∃ d : Kˣ,
    formAdj (RingHom.id K) G (((x⁻¹ : SpecialLinearGroup (Fin n) K)) : Matrix (Fin n) (Fin n) K) =
      (d : K) • (x : Matrix (Fin n) (Fin n) K)

@[expose] def pslTypeI {n : ℕ} {K : Type} [Field K] (G : Matrix (Fin n) (Fin n) K) (B : GL (Fin n) K)
    (e : Matrix (Fin n) (Fin n) K) : Prop :=
  formAdj (RingHom.id K) G e = e ∧
    ∀ a ∈ pslAlg B, formAdj (RingHom.id K) G (a * e) = a * e

@[expose] def pslTypeII {n : ℕ} {K : Type} [Field K] (G : Matrix (Fin n) (Fin n) K) (B : GL (Fin n) K)
    (e : Matrix (Fin n) (Fin n) K) : Prop :=
  formAdj (RingHom.id K) G e = e ∧
    ∃ a ∈ pslAlg B, formAdj (RingHom.id K) G (a * e) ≠ a * e

@[expose] def pslNormImage {n : ℕ} {K : Type} [Field K] (G : Matrix (Fin n) (Fin n) K) (B : GL (Fin n) K) :
    Set (Matrix (Fin n) (Fin n) K) :=
  {m | ∃ t : (pslAlg B)ˣ, m = formAdj (RingHom.id K) G ((t : pslAlg B) : Matrix (Fin n) (Fin n) K) *
    ((t : pslAlg B) : Matrix (Fin n) (Fin n) K)}

@[expose] noncomputable def pslRho {n : ℕ} {K : Type} [Field K] (G : Matrix (Fin n) (Fin n) K)
    (B : GL (Fin n) K) (e : Matrix (Fin n) (Fin n) K) : ℕ :=
  open Classical in
  if pslTypeII G B e then Nat.card K ^ (blockDegree (pslAlg B) e / 2) - 1
  else Nat.card K ^ blockDegree (pslAlg B) e - 1

end CFSG.StandardType
