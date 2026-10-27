module

public import CFSG.Quasithin.EmptyFaithful.S152RDef
public import CFSG.Quasithin.EmptyFaithful.S152He4Inv

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank CFSG.Quasithin.He4

theorem noE9CentralizedByInvolution_of_noInvCommNine {X : Type} [Group X] (h : NoInvCommNine X) :
    NoE9CentralizedByInvolution X := by
  intro l hl2 hl1 P hPl hP9 _
  exact hl1 (h P hP9 l hl2 fun p hp => Subgroup.mem_centralizer_singleton_iff.1 (hPl hp))

theorem noE9CentralizedByInvolution_of_psl_four_two {X : Type} [Group X]
    (h : StatedClassicalModel X .PSL 4 2 1) : NoE9CentralizedByInvolution X :=
  noE9CentralizedByInvolution_of_noInvCommNine (noInvCommNine_l42 h)

theorem noE9CentralizedByInvolution_of_psl_five_two {X : Type} [Group X]
    (h : StatedClassicalModel X .PSL 5 2 1) : NoE9CentralizedByInvolution X :=
  noE9CentralizedByInvolution_of_noInvCommNine (noInvCommNine_l52 h)

end CFSG.Quasithin
