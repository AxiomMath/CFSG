module

public import CFSG.RankThree.PartTwo.KFacts.KS163P6
import CFSG.RankThree.PartTwo.KFacts.KS163P6A10Cycles
import CFSG.RankThree.PartTwo.KFacts.KS163P6A10Orbits

public section

namespace CFSG.RankThree.PartTwo.KFacts

theorem ks163P6A10 : KS163P6A10 :=
  KF163A10.ks163P6A10_of_perm fun _ _ hB hB27 hT hBT => by
    obtain ⟨x, hxB, hx, hdisj⟩ := KF163A10.exists_threeCycles hB hB27
    exact KF163A10.card_eq_one_or_four hT x hx hdisj fun i => hBT (hxB i)

end CFSG.RankThree.PartTwo.KFacts
