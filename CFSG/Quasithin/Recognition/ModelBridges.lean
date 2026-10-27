module

public import CFSG.Open.QuasithinDefs
public import CFSG.Blueprint.NativeSporadic
import all CFSG.Blueprint.NativeSporadic

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Blueprint.NativeSporadic

theorem quasithinM12_eq_native : quasithinM12 = CFSG.Blueprint.NativeSporadic.M12 := rfl

theorem quasithinJ2_seed1_eq : quasithinDecodeMatrix 5 14 quasithinJ2Data1 = decode 5 14 1 J2Seed1 := by
  decide +kernel

theorem quasithinJ2_seed2_eq : quasithinDecodeMatrix 5 14 quasithinJ2Data2 = decode 5 14 1 J2Seed2 := by
  decide +kernel

noncomputable def quasithinJ2MulEquivNative : quasithinJ2 ≃* CFSG.Blueprint.NativeSporadic.J2 := by
  unfold quasithinJ2 quasithinSeedUnits CFSG.Blueprint.NativeSporadic.J2 seedMonoid
  rw [quasithinJ2_seed1_eq, quasithinJ2_seed2_eq]

end CFSG.Quasithin
