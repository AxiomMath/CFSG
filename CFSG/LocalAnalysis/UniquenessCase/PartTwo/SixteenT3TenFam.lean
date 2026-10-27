module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsModule

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

structure S16tBlocks {T : Type} [CommGroup T] (X : Subgroup (MulAut T)) {ι : Type} [Fintype ι]
    (Y : ι → Subgroup T) (d : ℕ) : Prop where
  indep : iSupIndep Y
  inj : Function.Injective Y
  sup : ⨆ i, Y i = ⊤
  card : Fintype.card ι = 4
  rank : ∀ i, rk ↥(Y i) = d
  perm : ∀ g ∈ X, ∀ i, ∃ j, (Y i).map g.toMonoidHom = Y j

structure S16tTenBlocks {T : Type} [CommGroup T] (X A : Subgroup (MulAut T)) {ι : Type}
    [Fintype ι] (Y : ι → Subgroup T) (p : ℕ) : Prop where
  blocks : S16tBlocks X Y (dParam p)
  norm : ∀ a ∈ A, ∀ i, (Y i).map a.toMonoidHom = Y i
  card_ker : ∀ i, Nat.card ↥(A ⊓ centSub (Y i)) = p ^ 2
  card_inf_ker : ∀ i j, i ≠ j →
    Nat.card ↥((A ⊓ centSub (Y i)) ⊓ (A ⊓ centSub (Y j))) ≤ p

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
