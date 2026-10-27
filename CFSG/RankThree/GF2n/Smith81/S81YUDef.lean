module

public import CFSG.RankThree.GF2n.Smith81.S81UModelData
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.RankThree.GF2n.Smith81.RootGenU

open CFSG.RankThree.GF2n.Smith81.U6Cube CFSG.RankThree.GF2n.Smith81.A5Cube
  CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.Unitary

variable {F : Type} [Field F] {K : Type} [Field K]

@[expose] def IsRtU [CharP F 2] (σ : F ≃+* F) (e : K ≃+* Fσ σ)
    (r : E3UWspace σ e ≃ₗ[K] E3UWspace σ e) : Prop :=
  ∃ g : SUid σ 6, IsTransvec F (g : GL (Fin 6) F) ∧ r = e3uWact σ e g

end CFSG.RankThree.GF2n.Smith81.RootGenU
