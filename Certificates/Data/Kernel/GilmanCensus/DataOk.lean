module

public import Certificates.Data.Kernel.GilmanCensus.Twin

public section

namespace Certificates.GilmanCensusK

@[expose] def reflLtK (dk : DK) : Bool :=
  (List.range dk.N).all fun i => (List.range dk.N).all fun j =>
    decide ((dk.reflP.getD i 0 >>> (7 * j)) % 128 < dk.N)

@[expose] def dataOkK (dk : DK) : Bool :=
  dk.F.all (fun r => r.all fun x => decide (x < 3)) &&
    dk.absidx.all (fun r => r.all fun j => decide (j < dk.AR.length)) &&
    decide (dk.N ≤ 125) && reflLtK dk

end Certificates.GilmanCensusK

end
