module

public import CFSG.RankThree.E6.RootLatticeTools
public import CFSG.RankThree.Lattice.SteinbergBIListMatrix
public meta import CFSG.RankThree.E6.RootLatticeTools
public meta import CFSG.RankThree.Lattice.SteinbergBIListMatrix
public meta import CFSG.Blueprint.ChevalleyRootArtifact
public import CFSG.Blueprint.ChevalleyRootArtifact

public section

namespace CFSG.RankThree.PartOne.KE6

open CFSG.Blueprint.Chevalley CFSG.RankThree.Lattice
open CFSG.RankThree.E6 (charVal)

@[expose] def e8Count7 (z : Fin Tag.E8.rank → ZMod 7) : ℕ :=
  (Tag.E8.artifactRoots.filter fun l => decide (charVal z (toVec Tag.E8.rank l) = 0)).length

@[expose] def e8Eig2 (a b c d : ZMod 7) : Fin Tag.E8.rank → ZMod 7 :=
  ![-(2 * a + 5 * b + 2 * c + 2 * d), -(5 * a + 2 * b + 3 * c + d), -(a + 6 * b + 4 * c + 3 * d),
    -(2 * b + 6 * c + 4 * d), a, b, c, d]

@[expose] def e8Eig4 (a b c d : ZMod 7) : Fin Tag.E8.rank → ZMod 7 :=
  ![-(4 * a + 2 * b + 4 * c + 4 * d), -(3 * a + 5 * b + 6 * c + d), -(a + 4 * b + 6 * c + 5 * d),
    -(4 * b + 6 * c + 2 * d), a, b, c, d]

@[expose] def E8SevenCount : Prop :=
  ∀ a b c d : ZMod 7, (a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0 ∨ d ≠ 0) →
    (e8Count7 (e8Eig2 a b c d) = 30 ∨ e8Count7 (e8Eig2 a b c d) = 72) ∧
    (e8Count7 (e8Eig4 a b c d) = 30 ∨ e8Count7 (e8Eig4 a b c d) = 72)

instance : Decidable E8SevenCount := by
  unfold E8SevenCount
  infer_instance

end CFSG.RankThree.PartOne.KE6
