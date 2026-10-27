
module

public import CFSG.Quasithin.H13.J4CentralizerBase1

public import CFSG.Quasithin.H13.J4FixCheck
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

theorem card_fix_Om :
    Nat.card {x : Om // tJ • x = x} = 52349 := by
  rw [← card_fix_orbit]
  refine Nat.card_congr
    { toFun := fun x => ⟨x.1.1, x.1.2, by
        have := congrArg Subtype.val x.2
        rwa [MulAction.orbit.coe_smul] at this⟩
      invFun := fun w => ⟨⟨w.1, w.2.1⟩, Subtype.ext (by rw [MulAction.orbit.coe_smul]; exact w.2.2)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

end CFSG.Quasithin.H13.J4
