module

public import CFSG.LocalAnalysis.StandardType.GGTPNNonExc
public import CFSG.LocalAnalysis.StandardType.GGTPNRegimeDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGNonExcR (R : ℕ → ℕ → LargeEvenLabel → LargeEvenLabel → Prop) : Prop :=
  GGTablePKnownR fun p n labJ labX =>
    R p n labJ labX ∧ ¬ GGTPNClTag labX.tag ∧ ¬ GGTPNExcTag labX.tag

theorem ggNonExcR_holds
    (R : ℕ → ℕ → LargeEvenLabel → LargeEvenLabel → Prop) : GGNonExcR R := by
  intro p hp hp2 X _ _ A Ab σ J n hd labJ labX hΛJ hΛX hQ hhJ hhX
  exact (ggNonExc_core hp hp2 hd hΛJ hΛX hQ.2.1 hQ.2.2 hhJ hhX).elim

end CFSG.StandardType

end
