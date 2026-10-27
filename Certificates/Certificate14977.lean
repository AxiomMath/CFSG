module

public import CFSG.RankThree.PartOne.KE.E7ThreeLatticeInputs

public section

open CFSG.RankThree.PartOne.KE CFSG.RankThree.Lattice

namespace CertificateChecks.Batch14977

open CFSG.RankThree.PartOne.KE CFSG.RankThree.Lattice

private theorem e7T3_charpoly_0 : ∀ n : Fin 8, CFSG.LieType.Chevalley.laplaceDet 7
      ((Matrix.of fun i j : Fin 7 => if i = j then ((n : ℕ) : ℤ) else 0) - toMat 7 e7T3WList) =
        (((n : ℕ) : ℤ) - 1) * (((n : ℕ) : ℤ) ^ 2 + ((n : ℕ) : ℤ) + 1) ^ 3 := by
  decide +kernel

end CertificateChecks.Batch14977

namespace Certificates

open CertificateChecks

open CFSG.RankThree.PartOne.KE CFSG.RankThree.Lattice in
theorem certificate14977 : ∀ n : Fin 8, CFSG.LieType.Chevalley.laplaceDet 7
      ((Matrix.of fun i j : Fin 7 => if i = j then ((n : ℕ) : ℤ) else 0) - toMat 7 e7T3WList) =
        (((n : ℕ) : ℤ) - 1) * (((n : ℕ) : ℤ) ^ 2 + ((n : ℕ) : ℤ) + 1) ^ 3 := by
  exact CertificateChecks.Batch14977.e7T3_charpoly_0

end Certificates
