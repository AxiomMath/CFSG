module

public import CFSG.Blueprint.Catalog

public section

namespace CFSG.RankThree.PartOne.S12K

open CFSG.Blueprint CFSG.Assembly.LowTwoRank

@[expose] def LieRigidity3 : Prop :=
  ∀ (S : Type) [Group S] (t : StatedLieTag) (n f : ℕ),
    (LieModel S t n 2 f ∨ (t = .twistedF4 ∧ n = 0 ∧ f = 1 ∧ LieModel S .Tits 0 2 1)) →
    (∀ g : ℕ, StatedClassicalModel S .PSU 3 2 g → t = .PSU ∧ n = 3 ∧ f = g) ∧
    (∀ g : ℕ, StatedClassicalModel S .PSp 2 2 g → t = .PSp ∧ n = 2 ∧ f = g) ∧
    (∀ g : ℕ, StatedClassicalModel S .PSL 2 2 g → t = .PSL ∧ n = 2 ∧ f = g)

end CFSG.RankThree.PartOne.S12K
