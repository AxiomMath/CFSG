module

public import CFSG.Monster.Existence.StdOdd.Cert.SylowThreeData
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LieType.Chevalley.C2E6MinusSixDefs
public import CFSG.Monster.B.Classical.E6AdjointDefs
public import Certificates.Certificate113
import CFSG.LieType.Chevalley.C2E6StdMatrixData

public section

open CFSG CFSG.Monster CFSG.Monster.Existence CFSG.Monster.Existence.StdOdd
  CFSG.Monster.Existence.StdOdd.Cert CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.C2E6Overlap CFSG.LieType.Chevalley.C2E6Std
  CFSG.LieType.Chevalley.C2E6Std.MatrixModel CFSG.Monster.B.Classical.E6Adjoint

namespace CertificateChecks.Batch16038

open CFSG CFSG.Monster CFSG.Monster.Existence CFSG.Monster.Existence.StdOdd
  CFSG.Monster.Existence.StdOdd.Cert CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.C2E6Overlap CFSG.LieType.Chevalley.C2E6Std
  CFSG.LieType.Chevalley.C2E6Std.MatrixModel CFSG.Monster.B.Classical.E6Adjoint

private theorem permLattice_cert_aux_0 : ∀ j < 72,
    List.ofFn (permLattice TwistTag.E6.perm (e6Certificate.root j)) =
    List.ofFn (e6Certificate.root (gamTable.getD j 0)) := by
  decide +kernel

private theorem gamTable_lt_1 : ∀ j < 72, gamTable.getD j 0 < 72 := by
  decide +kernel

end CertificateChecks.Batch16038

namespace Certificates

open CertificateChecks

open CFSG CFSG.Monster CFSG.Monster.Existence CFSG.Monster.Existence.StdOdd
  CFSG.Monster.Existence.StdOdd.Cert CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.C2E6Overlap CFSG.LieType.Chevalley.C2E6Std
  CFSG.LieType.Chevalley.C2E6Std.MatrixModel CFSG.Monster.B.Classical.E6Adjoint in
theorem certificate16038 : (
    ∀ j < 72,
      List.ofFn (permLattice TwistTag.E6.perm (e6Certificate.root j)) =
      List.ofFn (e6Certificate.root (gamTable.getD j 0))
  ) ∧ (
    ∀ j < 72, gamTable.getD j 0 < 72
  ) := by
  exact ⟨CertificateChecks.Batch16038.permLattice_cert_aux_0, CertificateChecks.Batch16038.gamTable_lt_1⟩

end Certificates
