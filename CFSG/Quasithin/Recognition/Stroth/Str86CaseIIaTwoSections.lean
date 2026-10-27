module

public import CFSG.Quasithin.Recognition.Stroth.Str86CaseIIaTwoFilt

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F112R
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem str86U1_sup_un {P N L2 S : Subgroup G} (hPN : P ≤ N) :
    str86U1 P L2 S ⊔ str86UN N L2 S = str86UN N L2 S :=
  sup_eq_right.mpr (str86U1_le_str86UN hPN)

theorem str86U2_sup_u1 {p P L2 S : Subgroup G} (hpP : p ≤ P) :
    str86U2 p P L2 S ⊔ str86U1 P L2 S = str86U1 P L2 S :=
  sup_eq_right.mpr (str86U2_le_str86U1 hpP)

end CFSG.Quasithin.Stroth
