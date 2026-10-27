module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.HardMathSupport.U4FF.ClassComb
public import CFSG.HardMathSupport.U4FF.ClassTwist

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.HardMathSupport.U4FF

@[expose] def finU4Label : Lbl 1 := ⟨fun _ => true, fun _ => false, fun _ => true⟩

theorem finU4Label_dim : finU4Label.dim = 14 := by
  simp [finU4Label, Lbl.dim, locM]

@[expose] def finU4ZMat (K : Type) [Field K] : Matrix (Fin 4) (Fin 4) K :=
  !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 1, 0, 0, 1]

@[expose] def FinU4FrobPair {K : Type} [Field K] [Finite K] [CharP K 2]
    (Z : Matrix (Fin 4) (Fin 4) K) (x y : SU4 K 1) : Prop :=
  ((y : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
    Z * ((x : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map (fun c => c ^ 2) * Z

end CFSG.LocalAnalysis.WeakClosure81
