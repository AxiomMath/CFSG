
module

public import CFSG.Literature.GL52IsosInputs
public meta import CFSG.Literature.GL52BFS
public meta import CFSG.Literature.GL52Pass
public meta import CFSG.Literature.GL52Elements
public meta import CFSG.LocalAnalysis.ComponentInitial.SmallLinearIsomorphisms
import Certificates.Kernel.Misc.GL52.Iso

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Literature CFSG.Literature.GL52 Matrix CFSG.Sporadic.Th CFSG.Sporadic.Th.Native in
open CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native in
theorem certificate2001 : ((gl3Elems.map keyGL3).Nodup ∧ gl3Elems.length = 168)
    ∧ (∀ q r : alternatingGroup (Fin 5),
      tblEq 31 (lkTableT tbK1 tbiK1 keyA5 tblA5 (q * r))
        (compT 31 (lkTableT tbK1 tbiK1 keyA5 tblA5 q) (lkTableT tbK1 tbiK1 keyA5 tblA5 r)) =
        true
    )
    ∧ (∀ q : alternatingGroup (Fin 5),
      tblEq 31 (lkTableT tbK1 tbiK1 keyA5 tblA5 q) (idT 31) = true → q = 1
    )
    ∧ (∀ q r : GL (Fin 3) (ZMod 2),
      tblEq 31 (lkTableT tbK2 tbiK2 keyGL3 tblGL3 (q * r))
        (compT 31 (lkTableT tbK2 tbiK2 keyGL3 tblGL3 q) (lkTableT tbK2 tbiK2 keyGL3 tblGL3 r)) =
        true
    )
    ∧ (∀ q : GL (Fin 3) (ZMod 2),
      tblEq 31 (lkTableT tbK2 tbiK2 keyGL3 tblGL3 q) (idT 31) = true → q = 1
    )
    ∧ (lkMulOK gensX (keyPerm (n := 3)) tblS3)
    ∧ (lkInjOK gensX (keyPerm (n := 3)) tblS3)
    ∧ (lkMulOK gensD keyD8 tblD8)
    ∧ (lkInjOK gensD keyD8 tblD8)
    ∧ (lkMulOK gensE (keyVec (n := 4) (p := 2)) tblE16)
    ∧ (lkInjOK gensE (keyVec (n := 4) (p := 2)) tblE16)
    ∧ (lkMulOK r0Gens (keyVec (n := 2) (p := 3)) tblR9)
    ∧ (lkInjOK r0Gens (keyVec (n := 2) (p := 3)) tblR9)
    ∧ (lkMulOK gensT1 (keyVec (n := 3) (p := 2)) tblE8)
    ∧ (∀ q r : GL (Fin 3) (ZMod 2),
      tblEq 31 (lkTableT tbT2 tbiT2 keyGL3 tblGL3 (q * r))
        (compT 31 (lkTableT tbT2 tbiT2 keyGL3 tblGL3 q) (lkTableT tbT2 tbiT2 keyGL3 tblGL3 r)) =
        true
    )
    ∧ (∀ (M : GL (Fin 3) (ZMod 2)) (c : Multiplicative (Fin 3 → ZMod 2)),
      tblEq 31 (t1Table (glAct M c)) (compT 31 (compT 31 (t2Table M) (t1Table c)) (t2Table M⁻¹)) =
        true
    )
    ∧ (∀ (c : Multiplicative (Fin 3 → ZMod 2)) (M : GL (Fin 3) (ZMod 2)),
      tblEq 31 (compT 31 (t1Table c) (t2Table M)) (idT 31) = true → c = 1 ∧ M = 1
    ) := KernelMisc.GL52L.facts2001

end Certificates
