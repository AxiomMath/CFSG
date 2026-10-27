module

public import Certificates.Data.GrSLitHeZStar
public meta import Certificates.Data.GrSLitHeZStar

public section

namespace Certificates.GrSLitHeF3

open CFSG.PSL3Four.Native CFSG.Sporadic.HeldB CFSG.ComponentClassification.GrSLit.HeGS
  Certificates.GrSLitHeZStar

@[expose] def heF3W1Tab : Tab := heGSKTab (heGSEW [2, 4, 2, 4])

@[expose] def heF3W2Tab : Tab := heGSKTab (heGSEW [1])

@[expose] def heF3W12Tab : Tab := comp 8330 heF3W1Tab heF3W2Tab

end Certificates.GrSLitHeF3
