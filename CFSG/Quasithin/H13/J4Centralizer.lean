module

public import CFSG.Quasithin.H13.J4CentralizerPrelude
import all CFSG.Quasithin.H13.J4CentralizerPrelude
public import CFSG.Quasithin.H13.J4Order

public import CFSG.Quasithin.H13.J4CentralizerBase4

public import CFSG.Quasithin.H13.J4FixCheck
public import CFSG.Quasithin.H13.J4Classes
public import CFSG.Quasithin.H13.J4Order
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

public noncomputable section

namespace CFSG.Quasithin.H13.J4

open CFSG.Sporadic.J4

theorem centralizer_tJ_eq
    : Subgroup.centralizer ({tJ} : Set J) = W.subgroupOf J := by
  have hcard : Nat.card (W.subgroupOf J) = 21799895040 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe W_le_J).toEquiv, card_W]
  exact (Subgroup.eq_of_le_of_card_ge W_subgroupOf_le_centralizer
    (by rw [hcard]; exact card_centralizer_tJ_le)).symm

end CFSG.Quasithin.H13.J4
