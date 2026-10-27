module

public import CFSG.RankThree.E6.RootLatticeTools

public section

namespace Certificates.E6WeylMinors

open CFSG.Blueprint.Chevalley

@[expose] def SmallMinor (k : ℕ) (A : Matrix (Fin Tag.E6.rank) (Fin Tag.E6.rank) ℤ) : Prop :=
  ∃ R C : Fin k → Fin Tag.E6.rank, StrictMono R ∧ StrictMono C ∧
    (A.submatrix R C).det ∈ ({1, -1, 2, -2} : Finset ℤ)

end Certificates.E6WeylMinors

end
