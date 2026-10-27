
module

public import CFSG.Quasithin.H13.J4CentralizerBase

public import CFSG.Quasithin.H13.J4FixCheckBase
public import CFSG.Quasithin.H13.J4ClassesBase1
public import CFSG.Quasithin.H13.J4OrderBase
public import CFSG.Sporadic.Schreier.J4SNative
public import CFSG.Sporadic.Schreier.J4SCols
public import CFSG.Sporadic.Schreier.J4SOrbits
public meta import CFSG.Sporadic.Schreier.J4SOrbits
public import CFSG.Quasithin.H13.J4Defs
public import CFSG.Quasithin.H13.J4WordsInputs
public import CFSG.Quasithin.H13.J4ChainSpec
public import Certificates.Data.CFSGNative.H13.J4Elems
public import CFSG.Quasithin.H13.J4FixSpec
public import CFSG.Sporadic.Schreier.J4SLocal
public import CFSG.Sporadic.J4.Local
public import CFSG.Quasithin.H13.J4ClassCheckInputs
public import Certificates.Data.CFSGNative.H13.J4Class
public import CFSG.Sporadic.Schreier.J4SKCent

@[expose] public noncomputable section

namespace CFSG.Quasithin.H13.J4

open CFSG.Sporadic.J4


theorem tS_eq_tJ : J4Classes.tS = tJ := Subtype.ext J4Classes.tS_coe

theorem isConj_tJ_e1
    : IsConj tJ CFSG.Sporadic.J4Schreier.z := tS_eq_tJ ▸ J4Classes.isConj_tS_z

end CFSG.Quasithin.H13.J4
