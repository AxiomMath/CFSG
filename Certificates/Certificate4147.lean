module

import Certificates.Kernel.LocalQT.Small.C4147
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourEnumSpec
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19HSAutData
public import CFSG.Sporadic.SmallOddCore.AutCount
public import Certificates.Data.CFSGNative.SmallOddCore.Check

public section

namespace Certificates

open CFSG.KD.LQT.C4147 in
open CFSG CFSG.QuasithinUnique CFSG.QuasithinUnique.Id2519 CFSG.QuasithinUnique.Id2519.HSAut in
open CFSG.PSL3Four CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Schreier CFSG.RankThreeCoreUniqueness.Helpers in
open scoped commutatorElement in
theorem certificate4147 : (∀ l₀ : Fin classSizes.size, l₀.val = 0 → ∀ U : Finset (Fin classSizes.size),
          l₀ ∈ U → (∑ l ∈ U, classSizes[l.val]!) ∣ 20160 → U = {l₀} ∨ U = Finset.univ) := CFSG.KC.LQT.S.s4147 _ hL hk hc

end Certificates
