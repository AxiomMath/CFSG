module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporRuSelfInputs
public import CFSG.Sporadic.Schreier.RuArrays
import Certificates.Kernel.SporSch.Ru.Self4097

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.QuasithinUnique CFSG.QuasithinUnique.Vol2Native CFSG.QuasithinUnique.Vol2Native.L239 CFSG.QuasithinUnique.Vol2Native.L239.RuPairs in
open CFSG.Sporadic.RuSchreier CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native in
theorem certificate4097 : ((∀ j < 4, ∀ i < 6, imgSorted ruSGensA[j]! (ruCBlockList i) =
            ruCBlockList (ruSBlockArr j)[i]!) ∧ (∀ j < 4, ∀ i < 6, (ruSBlockArr j)[i]! < 6)) := KernelSporSch.RuSelf.facts

end Certificates
