module

public import CFSG.RankThree.PartTwo.Sec15.Sylow155R3Thm90Aux
public import CFSG.RankThree.PartTwo.Sec13.Item13Sporadic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B42J2Main

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155R3.Thm90

theorem j2Facts_native :
    J2Facts CFSG.Blueprint.NativeSporadic.J2 := by
  have hsimple : IsSimpleGroup CFSG.Blueprint.NativeSporadic.J2 :=
    CFSG.Sporadic.J2.isSimpleGroup_J2
  have hcard : Nat.card CFSG.Blueprint.NativeSporadic.J2 = 604800 := CFSG.Sporadic.J2.card_J2
  obtain ⟨hperf, hcen⟩ := Sec13.isPerfect_center_of_isSimpleGroup hsimple
    (by rw [hcard]; norm_num)
  refine ⟨hsimple, hperf, hcen, ?_, Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)⟩
  obtain ⟨Φ, -⟩ := CFSG.QuasithinUnique.Bridge.J2Excl.j2_aut_model
  exact (Nat.card_congr Φ.toEquiv).symm.trans CFSG.QuasithinUnique.Bridge.J2Excl.card_j2R

end CFSG.RankThree.PartTwo.Sec15.Sylow155R3.Thm90
