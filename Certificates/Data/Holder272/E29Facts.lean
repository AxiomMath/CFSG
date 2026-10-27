module

public import Certificates.Data.Holder272.E29Words
public import Certificates.Data.Holder272.E29Check

public section

namespace CFSG.ClassicalInvolution.Q3.E29Data

theorem e29Words_eq : e29Words = (e29AllRels ()).map fun w => w.map e29Letter := rfl

end CFSG.ClassicalInvolution.Q3.E29Data
