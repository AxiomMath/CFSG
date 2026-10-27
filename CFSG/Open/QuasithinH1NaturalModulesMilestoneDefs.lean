module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.Open
open CFSG.Open

open scoped MatrixGroups

@[expose] noncomputable def quasithinH1MatrixRep {G ι K : Type} [Group G] [Fintype ι] [DecidableEq ι]
    [Field K] [Algebra (ZMod 2) K] (φ : G →* Matrix ι ι K) :
    Representation (ZMod 2) G (ι → K) where
  toFun g := (Matrix.toLin' (φ g)).restrictScalars (ZMod 2)
  map_one' := by ext v; simp
  map_mul' g h := by ext v; simp

@[expose] def quasithinH1SLMatrix (n : ℕ) (K : Type) [Field K] : SL(n, K) →* Matrix (Fin n) (Fin n) K where
  toFun g := (g : Matrix (Fin n) (Fin n) K)
  map_one' := Matrix.SpecialLinearGroup.coe_one
  map_mul' := Matrix.SpecialLinearGroup.coe_mul

@[expose] noncomputable def quasithinH1CardSL (n : ℕ) (K : Type) [Field K] [Algebra (ZMod 2) K] : ℕ :=
  Nat.card (groupCohomology (Rep.of (quasithinH1MatrixRep (quasithinH1SLMatrix n K))) 1)

end CFSG.Open
