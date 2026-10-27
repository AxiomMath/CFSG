
module

public import CFSG.Quasithin.H13.J4CentralizerBase3

public import CFSG.Quasithin.H13.J4FixCheck
public import CFSG.Quasithin.H13.J4Classes
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

theorem H_eq_Hj'
    : CFSG.Sporadic.J4Schreier.H = Hj := by
  have hle : CFSG.Sporadic.J4Schreier.H ≤ Hj := by
    rw [← CFSG.Sporadic.J4Schreier.stabilizer_v_eq_Hj]
    exact CFSG.Sporadic.J4Schreier.H_le_stabilizer_v
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [CFSG.Sporadic.J4Schreier.card_H, card_Hj j4Facts])

theorem stabilizer_root_eq_H :
    MulAction.stabilizer J vOm = CFSG.Sporadic.J4Schreier.H := by
  ext g
  rw [MulAction.mem_stabilizer_iff, H_eq_Hj', ← CFSG.Sporadic.J4Schreier.stabilizer_v_eq_Hj,
    MulAction.mem_stabilizer_iff]
  constructor
  · intro h
    have := congrArg Subtype.val h
    rwa [MulAction.orbit.coe_smul] at this
  · intro h
    exact Subtype.ext (by rw [MulAction.orbit.coe_smul]; exact h)

end CFSG.Quasithin.H13.J4
