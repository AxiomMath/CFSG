module

public import CFSG.Sporadic.Fi22.Nfp
public import CFSG.Sporadic.Fi22.Fischer
public import CFSG.Fischer.Uniq.F23Local

public section

namespace CFSG.Sporadic.Fi22

open CFSG.Blueprint.Fischer CFSG.Fischer

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem connected_D :
    (commGraph D).Connected :=
  Pair.connected_of_simple pair_D isSimpleGroup_commutator_J (F22.exists_commute f22_J)

theorem hasFixedPointProperty_D :
    HasFixedPointProperty pair_D :=
  fun g hg hadj htau => nfp22_involutive g hg hadj htau

theorem F23.nonempty_localPoints_fi22
    (hPF : PolarFacts) {X : Type} [Group X] {E : Set X}
    (hE : F23 X E) {e : X} (he : e ∈ E) : Nonempty (LocalPoints (pairModel pair_D) E e) :=
  F23.nonempty_localPoints hPF f22_J connected_D hasFixedPointProperty_D hE he

end CFSG.Sporadic.Fi22
