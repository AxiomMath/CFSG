module

public import CFSG.Quasithin.Background.C124HoldsE22
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtE22NoNProved

public section

namespace CFSG.Quasithin.C124

theorem c124StatementSQTK_holds :
    ∀ (G : Type) [Group G] [Finite G], C124StatementSQTK (G := G) :=
  fun G _ _ => c124StatementSQTK_of_e22 e22StatementNoN_proved G

end CFSG.Quasithin.C124
