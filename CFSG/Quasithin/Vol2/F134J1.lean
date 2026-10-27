module

public import CFSG.Walter.Models
public import CFSG.Walter.J1Props.Facts

public section

namespace CFSG.Quasithin.F134

theorem card_carrier_J1 : Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .J1) = 175560 := by
  change Nat.card CFSG.Blueprint.NativeSporadic.J1 = 175560
  rw [← Nat.card_congr CFSG.Walter.walterJ1EquivNative.toEquiv, CFSG.Walter.J1Props.J1_card]
  norm_num

end CFSG.Quasithin.F134
