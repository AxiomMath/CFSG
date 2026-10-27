module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P518B2Low
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P518B2MMain

public section

namespace CFSG.Quasithin.Fan86

namespace P518

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T P62

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}
variable {F : FanTree Γ G} {L : ZLab Γ G} {T : Track Γ G} {a : ℤ}

theorem lowerBound (S : B2Set F L T a) {x : G} (hx : x ∈ MulAction.stabilizer G (xv T a 6))
    (hxo : orderOf x = 5) : 2 ^ 12 ≤ cIdx Γ x (xv T a 6) := by
  have hv : valence Γ (xv T a 6) = 5 := by simpa using S.val_even 3
  exact lowerBound_of_layers F hx hxo (labSpan2_le_ballStab S.h40 S.lab hv)
    (fun g hg h hh => labSpan2_normalized S.h40 S.lab hv hg hh)
    (eLayer S hx hxo) (mLayer S hx hxo) (vLayer S hx hxo)

end P518

end CFSG.Quasithin.Fan86
