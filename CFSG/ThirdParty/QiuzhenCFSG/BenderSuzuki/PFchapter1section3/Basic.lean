module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.MatrixGroups.Suzuki
public import Mathlib.LinearAlgebra.Projectivization.Action

namespace CFSG
end CFSG
open CFSG

namespace CFSG.BenderSuzuki
namespace PFchapter1section3

open PFchapter1section1 PFAppendixIII MatrixGroups
open scoped LinearAlgebra.Projectivization

universe u v w

/-!
# Basic interfaces for Peterfalvi, Part II, Chapter I, Section 3
-/

/-- The natural PSL(2,q) action alternative in Theorem A. -/
public abbrev psl2ActionModel
    (G : Type u) (Omega : Type v) [Group G] [MulAction G Omega]
    (L : Subgroup G) (q : ℕ) : Prop :=
  ∃ (k : ℕ) (_ : k ≠ 0) (_ : q = 2 ^ k)
      (eL : L ≃* PSL2BinaryMatrixGroup k)
      (rho : PSL2BinaryMatrixGroup k →*
        Equiv.Perm (ℙ (BinaryGaloisField k) (Fin 2 → BinaryGaloisField k)))
      (eOmega : Omega ≃
        ℙ (BinaryGaloisField k) (Fin 2 → BinaryGaloisField k)),
    (∀ A : Matrix.SpecialLinearGroup (Fin 2) (BinaryGaloisField k),
      ∀ z : ℙ (BinaryGaloisField k) (Fin 2 → BinaryGaloisField k),
        rho (QuotientGroup.mk'
          (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2)
            (BinaryGaloisField k))) A) z =
          Matrix.SpecialLinearGroup.toLin' A • z) ∧
    ∀ l : L, ∀ omega : Omega,
      eOmega ((l : G) • omega) = rho (eL l) (eOmega omega)

/-- The natural Suzuki action alternative in Theorem A. -/
public abbrev suzukiActionModel
    (G : Type u) (Omega : Type v) [Group G] [MulAction G Omega]
    (L : Subgroup G) (q : ℕ) : Prop :=
  ∃ (k : ℕ) (_ : k ≠ 0) (_ : q = 2 ^ (2 * k + 1)),
    let K := BinaryGaloisField (2 * k + 1)
    let pinf : ℙ K (Fin 4 → K) :=
      Projectivization.mk K ![1, 0, 0, 0] (by simp)
    let p : K → K → ℙ K (Fin 4 → K) := fun x y =>
      Projectivization.mk K
        ![x * y + x ^ (2 ^ (k + 1)) * x ^ 2 + y ^ (2 ^ (k + 1)),
          y, x, 1] (by simp)
    let O : Set (ℙ K (Fin 4 → K)) :=
      {pinf} ∪ Set.range fun z : K × K => p z.1 z.2
    ∃ (eL : L ≃* SuzukiMatrixGroup k)
        (rho : SuzukiMatrixGroup k →* Equiv.Perm {z // z ∈ O})
        (eOmega : Omega ≃ {z // z ∈ O}),
      (∀ g : SuzukiMatrixGroup k, ∀ z : {z // z ∈ O},
        ((rho g z : {z // z ∈ O}) : ℙ K (Fin 4 → K)) =
          (Matrix.GeneralLinearGroup.toLin
            (g : GL (Fin 4) K)).toLinearEquiv •
              (z : ℙ K (Fin 4 → K))) ∧
      ∀ l : L, ∀ omega : Omega,
        eOmega ((l : G) • omega) = rho (eL l) (eOmega omega)

/-- The natural PSU(3,q) action alternative in Theorem A. -/
public abbrev unitaryActionModel
    (G : Type u) (Omega : Type v) [Group G] [MulAction G Omega]
    (L : Subgroup G) (q : ℕ) : Prop :=
  ∃ (E : Type) (_ : Field E) (_ : Finite E) (J : HermitianForm 3 E),
    J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0] ∧
    Nat.card E = q ^ 2 ∧
    Nat.card {z : E // J.conj z = z} = q ∧
    let P := ℙ E (Fin 3 → E)
    let A : Set P :=
      {x | ∃ (v : Fin 3 → E) (hv : v ≠ 0),
        x = Projectivization.mk E v hv ∧
          dotProduct (fun i => J.conj (v i)) (J.form.mulVec v) = 0}
    let X := {x : P // x ∈ A}
    ∃ (eL : L ≃* ProjectiveSpecialUnitaryMatrixGroup J)
        (rho : ProjectiveSpecialUnitaryMatrixGroup J →* Equiv.Perm X)
        (eOmega : Omega ≃ X),
      (∀ g : ProjectiveSpecialUnitaryMatrixGroup J, ∀ z : X,
        ∀ M : J.specialSubgroup,
          Matrix.ProjGenLinGroup.mk (M : GL (Fin 3) E) =
              (g : Matrix.ProjGenLinGroup (Fin 3) E) →
            ((rho g z : X) : P) =
              (Matrix.GeneralLinearGroup.toLin
                (M : GL (Fin 3) E)).toLinearEquiv • (z : P)) ∧
      ∀ l : L, ∀ omega : Omega,
        eOmega ((l : G) • omega) = rho (eL l) (eOmega omega)

/-- The conclusion of Peterfalvi's Theorem A. -/
public abbrev suzukiConclusion
    (G : Type u) (Omega : Type v) [Group G] [Finite G]
    [MulAction G Omega] [Finite Omega] : Prop :=
  ∃ (L : Subgroup G) (_ : L.Normal) (q : ℕ),
    Odd (Nat.card (G ⧸ L)) ∧ (∃ n : ℕ, q = 2 ^ n) ∧ 2 < q ∧
      (psl2ActionModel G Omega L q ∨
        suzukiActionModel G Omega L q ∨
          unitaryActionModel.{u, v} G Omega L q)

/-- The exact PSL(2,q) or Suzuki conclusion of the Zassenhaus branch. -/
public abbrev zassenhausConclusion
    (G : Type u) (Omega : Type v) [Group G] [Finite G]
    [MulAction G Omega] [Finite Omega] : Prop :=
  ∃ q : ℕ, (∃ n : ℕ, q = 2 ^ n) ∧ 2 < q ∧
    (psl2ActionModel G Omega (⊤ : Subgroup G) q ∨
      suzukiActionModel G Omega (⊤ : Subgroup G) q)

/-- The exact two-prime-residual conclusion of the V = W branch. -/
public abbrev unitaryConclusion
    (G : Type u) (Omega : Type v) [Group G] [Finite G]
    [MulAction G Omega] [Finite Omega] : Prop :=
  ∃ (L : Subgroup G) (_ : L.Normal) (q : ℕ),
    L = twoPrimeResidual G ∧ Odd (Nat.card (G ⧸ L)) ∧
      (∃ n : ℕ, q = 2 ^ n) ∧ 2 < q ∧
        unitaryActionModel.{u, v} G Omega L q

/-- The lifted form of the explicit `PSU(3,q)` Bruhat seed used in
Peterfalvi Chapter IV, Section 4.  The quotient calculation determines the
ambient identity only up to the center of the local residual, and that loss
of information is recorded by `delta`. -/
@[expose] public def psuCorollaryTwoLiftedSeed
    {G : Type u} [Group G]
    (F CX CQ0 V : Subgroup G) (t : G) : Prop :=
  ∃ omega gamma zeta delta : G,
    omega ∈ CX ∧ gamma ∈ CX ∧
      zeta ∈ F ∧ zeta ∈ V ∧ zeta ≠ 1 ∧
        zeta ∈ Subgroup.centralizer (CQ0 : Set G) ∧
          zeta ∉ (Subgroup.center F).map F.subtype ∧
            delta ∈ (Subgroup.center F).map F.subtype ∧
              delta ∈ V ∧
                delta ∈ Subgroup.centralizer (CX : Set G) ∧
                  omega ^ 2 ≠ 1 ∧
                    t * omega * t =
                      gamma * zeta ^ 3 * t *
                        (zeta⁻¹ * omega⁻¹ * zeta) * delta

/-- The subgroup Q0K union Q0KtQ0 generated in Lemma 4. -/
@[expose] public def psl2GeneratedSubgroup
    {G : Type u} [Group G] (Q0 K : Subgroup G) (t : G) : Subgroup G :=
  Subgroup.closure ((Q0 : Set G) ∪ (K : Set G) ∪ {t})

/-- The Peterfalvi set Q0K union Q0KtQ0 from Chapter I, Section 3, Lemma 4. -/
@[expose] public def q0KUnionQ0KtQ0
    {G : Type u} [Group G] (Q0 K : Subgroup G) (t : G) : Set G :=
  {x : G |
    (∃ q k : G, q ∈ Q0 ∧ k ∈ K ∧ x = q * k) ∨
      ∃ q k q' : G, q ∈ Q0 ∧ k ∈ K ∧ q' ∈ Q0 ∧ x = q * k * t * q'}

end PFchapter1section3
end CFSG.BenderSuzuki
