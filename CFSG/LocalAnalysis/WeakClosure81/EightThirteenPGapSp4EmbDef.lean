module

public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPGapSl2Emb

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (unitriangular)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (unipotent)
open CFSG.Assembly.LowTwoRank (StatedSp)

@[expose] def Sp4Sl2Emb {F : Type} [Field F] (A : Subgroup (StatedSp 2 F)) : Prop :=
  ∃ ι : Matrix.SpecialLinearGroup (Fin 2) F →* StatedSp 2 F, Function.Injective ι ∧
    A = (unitriangular 2 F).map ι ∧
    ∀ l : Fˣ, ι (slTwoDiag l) ∈
      normalizer ((unipotent 2 F : Subgroup (StatedSp 2 F)) : Set (StatedSp 2 F))

end CFSG.LocalAnalysis.WeakClosure81

end
