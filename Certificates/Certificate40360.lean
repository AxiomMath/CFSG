module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.SimsSporJ4Data
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.SimsSporJ4Facts
import Certificates.Kernel.J4Row.Glue
public import CFSG.LocalAnalysis.SectionRank.Sporadic.LocalWitness
public import CFSG.Open.Defs
public import CFSG.Sporadic.Schreier.ClassSum
public import CFSG.Sporadic.Schreier.J4SNative
public import CFSG.Sporadic.Schreier.M24Data
public import CFSG.Sporadic.Th.F2Spec
public import Certificates.Data.CFSGNative.SporadicSchreier.MathieuOddCore

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.J4 CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.SimsSporJ4 in
open CFSG.QuasithinUnique.Vol2Native.L239.J4Pairs (starMasks) in
theorem certificate40360 : (∃ z u : CFSG.Sporadic.J4.J, ∃ L : List CFSG.Sporadic.J4.J, RowFactsJ 31 27 10 row31.col 80 z u L) ∧
    (∀ j, row31.col j < 2 ^ 11) ∧
    (∀ i : Fin 24, ∀ c ∈ starMasks.getD i [],
      QT.rowsXor row31.col 11 c ∈ starMasks.getD (row31.piPerm i) []) ∧
    (∀ i < 24, 1 ∈ starMasks.getD i [] → i = 4 ∨ i = 11) ∧
    1 ∈ starMasks.getD 4 [] ∧ 1 ∈ starMasks.getD 11 [] ∧
    ((Finset.range 2048).filter fun c => QT.rowsXor row31.col 11 c = c).card = 8 := KernelJ4Row.facts31

end Certificates
