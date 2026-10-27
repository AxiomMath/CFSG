module

public import CFSG.Quasithin.Vol2.Ch12Sec6L12TwoRuPT
public import CFSG.Quasithin.Vol2.Ch12Sec6L12TwoRuPGroup
import Certificates.Kernel.RuIdx2.Prov
public import CFSG.Sporadic.HS.Group

public section

namespace Certificates

open CFSG.Quasithin.H13.K1262Two.RuP CFSG.QuasithinUnique.K1.SporadicPerm CFSG.Sporadic.SmallF2 in
open CFSG.Sporadic.Ru.Native (ruData) in
theorem certificate589235 : NoBig (Subgroup.closure {x | x ∈ [ruT1 (a ruData) (CFSG.Sporadic.SmallF2.b ruData),
    ruT2 (a ruData) (CFSG.Sporadic.SmallF2.b ruData) * ruT1 (a ruData) (CFSG.Sporadic.SmallF2.b ruData) * ruT2 (a ruData) (CFSG.Sporadic.SmallF2.b ruData),
    ruT3 (a ruData) (CFSG.Sporadic.SmallF2.b ruData) * ruT2 (a ruData) (CFSG.Sporadic.SmallF2.b ruData)]}) := CFSG.KD.RuIdx2.Prov.noBig_011

end Certificates
