module

public import Certificates.Data.Holder255.E64Words
public import Certificates.Data.Holder255.E64Check

public section

namespace CFSG.ClassicalInvolution.Q3.E64Data

theorem e64Words_eq : e64Words = (e64Rels () ++ [e64Partner]).map fun w => w.map e64Letter := rfl

end CFSG.ClassicalInvolution.Q3.E64Data
