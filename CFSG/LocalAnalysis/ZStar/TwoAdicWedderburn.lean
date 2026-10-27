module

public import CFSG.LocalAnalysis.ZStar.WedderburnBlock
public import Mathlib.RingTheory.SimpleModule.IsAlgClosed
public import CFSG.LocalAnalysis.ZStar.PadicBlockField
public import Mathlib.RepresentationTheory.Maschke
public import Mathlib.RingTheory.PicardGroup

public section

namespace CFSG

namespace ZStar.TwoAdicWedderburn

open ZStar.PadicBlockField
open ZStar.WedderburnBlock

noncomputable section

universe u

variable {G : Type u} [Group G] [Fintype G]

structure Decomposition (G : Type u) [Group G] [Fintype G] where
  blockCount : ℕ
  blockSize : Fin blockCount → ℕ
  blockSize_neZero : ∀ i, NeZero (blockSize i)
  equiv : MonoidAlgebra TwoAdicComplex G ≃ₐ[TwoAdicComplex]
    BlockProduct TwoAdicComplex blockSize

theorem exists_decomposition : Nonempty (Decomposition G) := by
  let _ : NeZero (Nat.card G : TwoAdicComplex) := by infer_instance
  obtain ⟨n, d, hd, ⟨φ⟩⟩ :=
    IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed
      TwoAdicComplex (MonoidAlgebra TwoAdicComplex G)
  exact ⟨⟨n, d, hd, φ⟩⟩

@[expose] noncomputable def decomposition : Decomposition G :=
  Classical.choice (exists_decomposition (G := G))

@[expose] noncomputable def componentAlgHom (D : Decomposition G)
    (i : Fin D.blockCount) :
    MonoidAlgebra TwoAdicComplex G →ₐ[TwoAdicComplex]
      Matrix (Fin (D.blockSize i)) (Fin (D.blockSize i)) TwoAdicComplex :=
  (Pi.evalAlgHom TwoAdicComplex
    (fun j : Fin D.blockCount ↦
      Matrix (Fin (D.blockSize j)) (Fin (D.blockSize j)) TwoAdicComplex) i).comp
    D.equiv.toAlgHom

@[expose] noncomputable def componentRepresentation (D : Decomposition G)
    (i : Fin D.blockCount) :
    Representation TwoAdicComplex G (Fin (D.blockSize i) → TwoAdicComplex) :=
  Matrix.toLinAlgEquiv'.toMonoidHom.comp
    ((componentAlgHom D i).toMonoidHom.comp
      (MonoidAlgebra.of TwoAdicComplex G))

@[simp]
theorem componentRepresentation_apply (D : Decomposition G)
    (i : Fin D.blockCount) (g : G) :
    componentRepresentation D i g =
      Matrix.toLinAlgEquiv'
        (D.equiv (MonoidAlgebra.single g 1) i) := by
  rfl

theorem componentCharacter_eq_matrixTrace (D : Decomposition G)
    (i : Fin D.blockCount) (g : G) :
    (componentRepresentation D i).character g =
      Matrix.trace (D.equiv (MonoidAlgebra.single g 1) i) := by
  rw [Representation.character, componentRepresentation_apply]
  exact Matrix.trace_toLin_eq _
    (Pi.basisFun TwoAdicComplex (Fin (D.blockSize i)))

end

end ZStar.TwoAdicWedderburn

end CFSG
