
module

public import CFSG.Quasithin.Background.A3StructureDefs
public import CFSG.Quasithin.Background.A3CircleModels
public import CFSG.Assembly.GL83LieDefs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank
open scoped MatrixGroups Matrix

@[expose] def oPrimeResidualOf (p : ℕ) {G : Type*} [Group G] (X : Subgroup G) : Subgroup G :=
  Subgroup.closure {x : G | x ∈ X ∧ ∃ k : ℕ, orderOf x = p ^ k}

@[expose] def StatedGU (n q : ℕ) (K : Type) [Field K] : Subgroup (GL (Fin n) K) :=
  Subgroup.closure {A | ((A : Matrix (Fin n) (Fin n) K).map (· ^ q))ᵀ *
    (A : Matrix (Fin n) (Fin n) K) = 1}

@[expose] def IsPGLEps3 (s : Bool) (q : ℕ) (X : Type) [Group X] : Prop :=
  match s with
  | true => ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = q ∧
      Nonempty (X ≃* StatedProj (⊤ : Subgroup (GL (Fin 3) K)))
  | false => ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = q ^ 2 ∧
      Nonempty (X ≃* StatedProj (StatedGU 3 q K))

@[expose] def IsPSLEps3q (s : Bool) (q : ℕ) (X : Type) [Group X] : Prop :=
  ∃ p e : ℕ, p.Prime ∧ 1 ≤ e ∧ q = p ^ e ∧ IsPSLEps3 s p e X

@[expose] def IsL3CircAbstract (s : Bool) (q : ℕ) (X : Type) [Group X] : Prop :=
  ∃ (e : ℕ) (L₀ : Subgroup X) (_ : L₀.Normal), q = 2 ^ e ∧ IsPSLEps3 s 2 e ↥L₀ ∧
    Nat.card (X ⧸ L₀) = 3 ∧ (∀ x : X, (∀ l ∈ L₀, x * l = l * x) → x = 1) ∧
    ∀ a : X, orderOf a = 3 → a ∈ L₀

open CFSG.ASVolI.ChA

@[expose] def IsL3CircWithBase (sign : Bool) (q : ℕ) (X : Type) [Group X]
    (base : Subgroup X) : Prop :=
  ∃ (parameter : ℕ) (field : Type) (_ : Field field) (_ : Finite field),
    1 ≤ parameter ∧ Nat.card field = 2 ^ (6 * parameter) ∧
    ∃ (fieldMap : RingAut field) (diagonalMatrix : GL (Fin 3) field),
      orderOf fieldMap = 3 ∧ psl3DiagAut diagonalMatrix ∉ psl3InnAut field ∧
      if sign then
        q = 2 ^ (6 * parameter) ∧
        ∃ identification : X ≃* ↥(psl3Circ fieldMap diagonalMatrix),
          base.map identification.toMonoidHom =
            (psl3InnAut field).subgroupOf (psl3Circ fieldMap diagonalMatrix)
      else
        q = 2 ^ (3 * parameter) ∧ Odd parameter ∧
        ∃ graphField : MulAut PSL(3, field), IsPsl3GraphField graphField ∧
          ∃ identification : X ≃* ↥(psl3Circ fieldMap diagonalMatrix ⊓
              Subgroup.centralizer ({graphField} : Set (MulAut PSL(3, field)))),
            base.map identification.toMonoidHom =
              (psl3InnAut field).subgroupOf (psl3Circ fieldMap diagonalMatrix ⊓
                Subgroup.centralizer ({graphField} : Set (MulAut PSL(3, field))))

@[expose] def IsL3Circ (sign : Bool) (q : ℕ) (X : Type) [Group X] : Prop :=
  ∃ base : Subgroup X, IsL3CircWithBase sign q X base

end CFSG.Quasithin
