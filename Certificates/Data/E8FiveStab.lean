module

public import CFSG.RankThree.E6.RootLatticeTools
public import CFSG.RankThree.Lattice.SteinbergBIListMatrix
public meta import CFSG.RankThree.E6.RootLatticeTools
public meta import CFSG.RankThree.Lattice.SteinbergBIListMatrix
public meta import CFSG.Blueprint.ChevalleyRootArtifact
public import CFSG.Blueprint.ChevalleyRootArtifact

public section

namespace CFSG.RankThree.PartOne.KE8F

open CFSG.Blueprint.Chevalley CFSG.RankThree.Lattice
open CFSG.RankThree.E6 (charVal)
open scoped Matrix

@[expose] def e8Count5 (z : Fin Tag.E8.rank → ZMod 5) : ℕ :=
  (Tag.E8.artifactRoots.filter fun l => decide (charVal z (toVec Tag.E8.rank l) = 0)).length

@[expose] def e8FiveEig2 (c : Fin 4 → ZMod 5) : Fin Tag.E8.rank → ZMod 5 :=
  ![-(4 * c 0 + 2 * c 2 + c 3), -(3 * c 0 + 4 * c 1 + c 3), -(4 * c 0 + c 1 + c 3),
    -(3 * c 1 + 4 * c 2 + 2 * c 3), c 0, c 1, c 2, c 3]

@[expose] def e8FiveEig3 (c : Fin 4 → ZMod 5) : Fin Tag.E8.rank → ZMod 5 :=
  ![-(4 * c 0 + c 2 + 2 * c 3), -(4 * c 0 + c 1 + 2 * c 2 + c 3),
    -(3 * c 0 + c 1 + 4 * c 2 + 4 * c 3), -(2 * c 1 + 4 * c 2 + 3 * c 3), c 0, c 1, c 2, c 3]

@[expose] def e8FiveT40 (B : (Fin 4 → ZMod 5) → Fin Tag.E8.rank → ZMod 5) :
    Finset (Fin 4 → ZMod 5) :=
  Finset.univ.filter fun c => c ≠ 0 ∧ e8Count5 (B c) = 40

@[expose] def e8FiveT40Two : Finset (Fin 4 → ZMod 5) := e8FiveT40 e8FiveEig2

@[expose] def e8FiveT40Three : Finset (Fin 4 → ZMod 5) := e8FiveT40 e8FiveEig3

@[expose] def E8FiveTorsionCount : Prop :=
  ∀ f : Fin 4 → ZMod 5, f ≠ 0 →
    25 ≤ (e8FiveT40Two.filter fun c => dotProduct f c = 0).card ∧
      25 ≤ (e8FiveT40Three.filter fun c => dotProduct f c = 0).card

instance : Decidable E8FiveTorsionCount := by
  unfold E8FiveTorsionCount
  infer_instance

@[expose] def e8FiveFix1 (c : Fin 4 → ZMod 5) : Fin Tag.E8.rank → ZMod 5 :=
  ![0, 0, 0, 0, c 0, c 1, c 2, c 3]

@[expose] def e8FiveFix2 (c : Fin 4 → ZMod 5) : Fin Tag.E8.rank → ZMod 5 :=
  ![-(4 * c 0 + 2 * c 1 + 3 * c 2), c 0, c 1, c 2, c 3, 0, 0, 0]

@[expose] def E8FiveSylowCount : Prop :=
  (e8FiveT40 e8FiveFix1).card ≤ 24 ∧ (e8FiveT40 e8FiveFix2).card ≤ 24

instance : Decidable E8FiveSylowCount := by
  unfold E8FiveSylowCount
  infer_instance

end CFSG.RankThree.PartOne.KE8F
