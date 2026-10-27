module

public import Certificates.Data.E6ThreeTwD4T2Gen
import Certificates.Kernel.E6TwD4T2.Glue101

public section

open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three CertificateChecks.KernelE6TwD4T2
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.Steinberg
  CFSG.HardMathSupport.Timmesfeld.CrossChar

namespace Certificates

theorem certificate214101 : CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.twD4T2Check () = true := by
  have e : twD4T2Check () = (twD4T2RepsOK () &&
      ((twD4T2Sig ()).map fun b => (b, twD4T2Row (twD4T2Vecs ()) b)).all
        (fun p => twD4T2RowOK p.1 p.2) &&
      twD4T2Closed (twD4T2Elems.map Prod.fst)
        ((twD4T2Sig ()).map fun b => (b, twD4T2Row (twD4T2Vecs ()) b))
        (KTree.ofSorted (twD4T2Elems.map Prod.fst)) &&
      twD4T2Elems.all (fun e => decodeT Tag.E6.rank e.1 == List.range Tag.E6.rank ||
        twD4T2Moves (decodeT Tag.E6.rank e.1) e.2.1 e.2.2) &&
      (twD4T2Words.map twD4T2WordTuple).all (fun t =>
        twD4T2Fixes (vec3 (τ := .E6) twD4T2F0) t && e6ScTest e6Certificate twD4T2F0 t) &&
      twD4T2PairsOK (twD4T2ZTab (twD4T2Sig ())) (twD4T2GTab (twD4T2Words.map twD4T2WordTuple))) :=
    rfl
  rw [e, brs_eq, reps_check, rows_check, closed_check, moves_check, words_check, pairs_ok]
  rfl

end Certificates
