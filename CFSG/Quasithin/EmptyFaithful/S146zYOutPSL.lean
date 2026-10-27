module

public import CFSG.Quasithin.EmptyFaithful.S146zYOutComm
public import CFSG.Quasithin.Vol2.F134L2
public import CFSG.LocalAnalysis.ComponentInitial.QTNQRLinearUnitaryOuterDerivedLinear

public section

namespace CFSG.Quasithin.S146zY

open CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

theorem outer_comm_of_statedPSL2 {X : Type} [Group X] {p f : ℕ} (hp : p.Prime)
    (h : StatedClassicalModel X .PSL 2 p f) : ∀ x y : Outer X, x * y = y * x := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨e⟩ := CFSG.Quasithin.F134.nonempty_mulEquiv_psl2 h
  exact outer_comm_of_mulEquiv e.symm
    (CFSG.LocalAnalysis.ComponentInitial.OuterDerived.outer_psl2_mul_comm (GaloisField p f))

end CFSG.Quasithin.S146zY
