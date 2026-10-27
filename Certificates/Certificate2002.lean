module

public import CFSG.Literature.GL52LocalCheckInputs
public meta import CFSG.Literature.GL52Isos
public meta import CFSG.Literature.GL52Pass
import Certificates.Kernel.Misc.GL52.LC
public import CFSG.Literature.GL52Isos

public section

open CFSG CFSG.Literature CFSG.Literature.GL52 CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
open CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native

attribute [local instance high] fastGL3

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Literature CFSG.Literature.GL52 CFSG.Sporadic.Th CFSG.Sporadic.Th.Native in
open CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native in
theorem certificate2002 : (ordTest 31 2 (tbl glT0) = true ∧ ordTest 31 2 (tbl glU0) = true ∧
      ordTest 31 3 (tbl glTau1) = true ∧ ordTest 31 3 (tbl glTau2) = true ∧
      ordTest 31 3 (tbl glTauB) = true ∧ ordTest 31 5 (tbl glF5) = true ∧
      ordTest 31 15 (tbl glC15) = true ∧ ordTest 31 7 (tbl glS7) = true ∧
      ordTest 31 3 (tbl glFr) = true ∧ ordTest 31 31 (tbl glA) = true ∧
      ordTest 31 5 (tbl glH5) = true
    )
    ∧ (fpT (tbl glT0) = 15 ∧ fpT (tbl glU0) = 7 ∧ fpT (tbl glTau1) = 1 ∧ fpT (tbl glTau2) = 7)
    ∧ ((gensE ++ gensT1 ++ gensT2).all (fun g => cmtT (tbl g) (tbl glT0)) = true ∧
      gensK1.all (fun g => cmtT (tbl g) (tbl glTau1)) = true ∧
      gensK2.all (fun g => cmtT (tbl g) (tbl glTau2)) = true ∧
      gensX.all (fun g => gensY.all fun h => cmtT (tbl g) (tbl h)) = true ∧
      cmtT (tbl glC15) (tbl glF5) = true ∧ cmtT (tbl glTau2) (tbl glTauB) = true
    )
    ∧ (tblEq 31 (compT 31 (tbl glFr) (tbl glS7)) (compT 31 (tbl (glS7 * glS7)) (tbl glFr)) = true ∧
      tblEq 31 (compT 31 (tbl glH5) (tbl glA)) (compT 31 (tbl (glA * glA)) (tbl glH5)) = true ∧
      tblEq 31 (tbl glF5) (tbl (glC15 * glC15 * glC15)) = true ∧
      cmtT (tbl glFr) (tbl glS7) = false ∧ cmtT (tbl glH5) (tbl glA) = false ∧
      cmtT (tbl glA) (tbl glB) = false
    )
    ∧ ((∀ σ : alternatingGroup (Fin 5),
        tblEq 31 (lkTableT tbK1 tbiK1 keyA5 tblA5 σ) (tbl glTau1) = false) ∧
      (∀ M : GL (Fin 3) (ZMod 2),
        tblEq 31 (lkTableT tbK2 tbiK2 keyGL3 tblGL3 M) (tbl glTau2) = false)
    )
    ∧ (enumOK gensE wordsE = true ∧ keysDistinct 31 (enumTables gensE wordsE) = true ∧
      enumOK r0Gens r0Words = true ∧ keysDistinct 31 (enumTables r0Gens r0Words) = true ∧
      enumOK gensY wordsY = true ∧ keysDistinct 31 (enumTables gensY wordsY) = true
    )
    ∧ (wordsE.all (fun w => wordsE.all fun w' => cmtT (wT gensE w) (wT gensE w') &&
        tblEq 31 (compT 31 (wT gensE w) (wT gensE w)) (idT 31)) = true ∧
      r0Words.all (fun w => r0Words.all fun w' => cmtT (wT r0Gens w) (wT r0Gens w') &&
        tblEq 31 (compT 31 (wT r0Gens w) (compT 31 (wT r0Gens w) (wT r0Gens w))) (idT 31)) =
        true
    )
    ∧ ((gensT1 ++ gensT2).all (fun a => gensE.all fun e => wordsE.any fun w =>
        tblEq 31 (compT 31 (tbl a) (tbl e)) (compT 31 (wT gensE w) (tbl a))) = true ∧
      gensD.all (fun a => r0Gens.all fun x => r0Words.any fun w =>
        tblEq 31 (compT 31 (tbl a) (tbl x)) (compT 31 (wT r0Gens w) (tbl a))) = true
    )
    ∧ ((∀ (c : Multiplicative (Fin 3 → ZMod 2)) (M : GL (Fin 3) (ZMod 2)),
        wordsE.all (fun w => !tblEq 31 (wT gensE w) (compT 31 (t1Table c) (t2Table M)) ||
          w.isEmpty) = true) ∧
      (∀ (c : Multiplicative (Fin 3 → ZMod 2)) (M : GL (Fin 3) (ZMod 2)),
        gensE.all (fun e => cmtT (compT 31 (t1Table c) (t2Table M)) (tbl e)) = true →
          c = 1 ∧ M = 1)
    )
    ∧ (∀ σ : Equiv.Perm (Fin 3), wordsY.all (fun w =>
      !tblEq 31 (lkTable gensX (keyPerm (n := 3)) tblS3 σ) (wT gensY w)) = true ∨ σ = 1
    ) := KernelMisc.GL52L.facts2002

end Certificates
