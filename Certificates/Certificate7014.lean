
module

public import Certificates.Certificate7014Base
import CFSG.Quasithin.H13.J4CentralizerBase
import CFSG.Sporadic.Schreier.J4SOrbitsBase
meta import CFSG.Sporadic.Schreier.J4SOrbitsBase
import CFSG.Sporadic.Schreier.J4SKCentBase

public import CFSG.Quasithin.H13.J4Defs
import CFSG.Quasithin.H13.J4CentralizerBase4
import CFSG.Quasithin.H13.J4CentralizerPrelude
import CFSG.Quasithin.H13.J4Core
import CFSG.Quasithin.H13.J4Image
import CFSG.Sporadic.Schreier.J4SNative
import CFSG.Sporadic.Schreier.J4SCols
import CFSG.Sporadic.Schreier.J4SOrbits
meta import CFSG.Sporadic.Schreier.J4SOrbits
import CFSG.Sporadic.J4.Local
import CFSG.Quasithin.H13.J4CoreInputs
import CFSG.Quasithin.H13.J4Words
import CFSG.Certificates.ExtraspecialNormalForm
import CFSG.Sporadic.HS.SmallF2Spec
import Certificates.Data.CFSGNative.H13.J4Data
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import CFSG.Quasithin.H13.J4QuotInputs
import Certificates.Data.CFSGNative.H13.J4Elems
import CFSG.Quasithin.H13.J4WordsInputs
import CFSG.Quasithin.H13.J4ChainSpec
import CFSG.Quasithin.H13.J4FixSpec
import CFSG.Sporadic.Schreier.J4SLocal
import CFSG.Quasithin.H13.J4ClassCheckInputs
import Certificates.Data.CFSGNative.H13.J4Class
import CFSG.Sporadic.Schreier.J4SKCent
public import CFSG.Sporadic.J4.ParSpec

public section

namespace Certificates

open CFSG.Quasithin.H13.J4

theorem certificate7014 :
    Nat.card CFSG.Quasithin.H13.J4.W = 21799895040 := by
  refine le_antisymm ?_ ?_
  · rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe W_le_J).toEquiv]
    exact (Subgroup.card_le_of_le W_subgroupOf_le_centralizer).trans card_centralizer_tJ_le
  · have hPW : Nat.card (P.subgroupOf W) = 8192 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe P_le_W).toEquiv, card_P]
      norm_num
    have hW : Nat.card rho.ker * Nat.card rho.range = Nat.card W := by
      rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange rho).toEquiv, mul_comm,
        ← Subgroup.card_eq_card_quotient_mul_card_subgroup]
    have hk : 8192 ≤ Nat.card rho.ker := hPW ▸ Subgroup.card_le_of_le P_le_ker_rho
    rw [← hW]
    calc (21799895040 : ℕ) = 8192 * 2661120 := by norm_num
      _ ≤ Nat.card rho.ker * Nat.card rho.range := Nat.mul_le_mul hk le_card_range_rho

end Certificates
