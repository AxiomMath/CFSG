module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAFyWrFact

public section

open CFSG.EvenSporadicStandard.TwoHS

namespace Certificates

theorem wrClassFact : WrClassFact := by
  decide +kernel

open CFSG.EvenSporadicStandard.TwoHS in
theorem certificate26790 : WrClassFact := wrClassFact

end Certificates
