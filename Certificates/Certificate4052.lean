
module

public import Certificates.Certificate4052Base

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporAutLocal
public import CFSG.Sporadic.Schreier.PairHSPairs
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporAutHSInputs
import Certificates.Kernel.SporSch.PairHS.Aut4052Facts
import CFSG.Sporadic.Schreier.PairHSCertInputs
import CFSG.Sporadic.Schreier.PairHSCheckInputs
meta import CFSG.Sporadic.Schreier.PairHSCert
meta import Certificates.Data.CFSGNative.PairSchreier.Core
meta import Certificates.Data.CFSGNative.Schreier.Check
meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public import CFSG.Foundations
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.LocalAnalysis.SectionRank.SQT
import CFSG.Certificates.Kernel.SporSch.PairClTSound

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1 CFSG.QuasithinUnique.Ch1.SporAutHS in
open CFSG.Sporadic.Schreier in
theorem certificate4052 : Nat.card s0Chain.originalSubgroup = 512
    ∧ (∀ k < 4, hsLtr k ∈ hsChain.originalSubgroup)
    ∧ (∀ k < 4, hsLtr 0 * hsLtr k = hsLtr k * hsLtr 0)
    ∧ wordElt bWord * hsLtr 0 = wordElt yWord * wordElt bWord
    ∧ hsGen 1 = wordElt t0Word * wordElt bWord ^ 2 * wordElt t1Word * wordElt bWord ^ 4 *
        wordElt t2Word
    ∧ (orderOf (wordElt bWord) = 15 ∧ orderOf (wordElt l1Word * wordElt bWord) = 5 ∧
        orderOf (wordElt l2Word * wordElt bWord) = 12)
    ∧ Nat.card {g : hsChain.originalSubgroup // (g : Equiv.Perm (Fin 3850)) * hsLtr 0 =
        wordElt yWord * g ∧ orderOf (g : Equiv.Perm (Fin 3850)) = 15 ∧
        orderOf (wordElt l1Word * g) = 5 ∧ orderOf (wordElt l2Word * g) = 12} = 2 := KernelSporSch.PHSAFacts.facts

end Certificates
