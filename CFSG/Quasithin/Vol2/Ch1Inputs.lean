
module

public import CFSG.Quasithin.Background.A3Structure312Defs

public section

namespace CFSG.Quasithin

@[expose] def A36ForSQTK : Prop := ∀ (Q : Type) [Group Q], SQTKHyp Q → A36Statement Q

@[expose] def A312ForSQTK : Prop := ∀ (Q : Type) [Group Q], SQTKHyp Q → A312Statement Q

end CFSG.Quasithin
