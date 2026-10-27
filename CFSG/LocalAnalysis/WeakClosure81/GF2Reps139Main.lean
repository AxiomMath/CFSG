module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps139K
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps139AlphaRows
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps139BetaShape
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps139ConclA
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps139ConclB
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps139ConclC
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps139GapEndA
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps139GapEndU33
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps139GapEndL32
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps139GapOut
public import CFSG.LocalAnalysis.WeakClosure81.U43TripleHolds

public section

namespace CFSG.LocalAnalysis.WeakClosure81.GF2Reps139

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise Matrix

variable {W : Type} [CommGroup W] [Finite W] {G X D : Subgroup (MulAut W)} {s : MulAut W}
  {Y : Subgroup W} {n : ℕ}

theorem Std139.lemmaI (h135 : W4Lem13_5) (hgen : U43TripleGen)
    (gU33 : GapEndU33) (gSp62 : GapEndSp62) (gL52 : GapEndL52) (gM22 : GapEndM22)
    (gL32 : GapEndL32) (gOut : GapOutU43) (hw2 : ∀ w : W, w ^ 2 = 1)
    (S : Std139 G X D s Y n) (hn : 3 ≤ n) {K : Subgroup (MulAut W)} (hK : Comp139 G X D K) :
    ShapeNat4 K X n ∨ ShapeTensor K X n ∨ ShapeCover K X n := by
  by_cases hirr : IsIrrOn K ⊤ ⊥
  · rcases Std139.alpha_shape h135 hgen gU33 gSp62 gL52 gM22 gL32 gOut hw2 S hn hK hirr with
      h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
  · exact Or.inr (Or.inl (Std139.beta_shape hw2 S hn hK hirr))

theorem hyp139Ge3_of_inputs (h134 : W4Lem13_4) (h135 : W4Lem13_5)
    (hgen : U43TripleGen) (gU33 : GapEndU33) (gSp62 : GapEndSp62) (gL52 : GapEndL52)
    (gM22 : GapEndM22) (gL32 : GapEndL32) (gOut : GapOutU43) : Hyp139Ge3 := by
  intro W _ _ hw2 G X D s Y n S hn
  obtain ⟨K, hK⟩ := Std139.exists_comp139 h134 hw2 S hn
  rcases Std139.lemmaI h135 hgen gU33 gSp62 gL52 gM22 gL32 gOut hw2 S hn hK with h | h | h
  · exact Std139.concl_of_shapeNat4 hw2 S hK h
  · exact Std139.concl_of_shapeTensor hw2 S hn hK h
  · exact Std139.concl_of_shapeCover hw2 S hn hK h

theorem hyp139_of_inputs (h134 : W4Lem13_4) (h135 : W4Lem13_5)
    (hgen : U43TripleGen) (gU33 : GapEndU33) (gSp62 : GapEndSp62) (gL52 : GapEndL52)
    (gM22 : GapEndM22) (gL32 : GapEndL32) (gOut : GapOutU43) : Hyp139 :=
  hyp139_of_ge3 (hyp139Ge3_of_inputs h134 h135 hgen gU33 gSp62 gL52 gM22 gL32 gOut)

theorem hyp139_of_inputs_closed
    (h134 : W4Lem13_4) (h135 : W4Lem13_5) : Hyp139 :=
  hyp139_of_inputs h134 h135 u43TripleGen_holds gapEndU33_holds gapEndSp62_holds
    gapEndL52_holds gapEndM22_holds gapEndL32_holds (show GapOutU43 from gapOutU43_le_eight)

end CFSG.LocalAnalysis.WeakClosure81.GF2Reps139
