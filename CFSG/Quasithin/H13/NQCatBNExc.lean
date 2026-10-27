module

public import CFSG.Quasithin.H13.NQCatBND4
public import CFSG.Quasithin.H13.NQCatBNRee

public section

namespace CFSG.Quasithin.H13.NQCat

theorem lieOvergroupFactRank2Exc_holds :
    LieOvergroupFactRank2Exc := by
  intro S _ _ _ ⟨k, hk, h⟩ P hP X hPX hX
  rcases h with h | h | h
  · exact BN.solvOver_of_isG2 hk h hP X hPX hX
  · exact BN.solvOver_of_is3D4 hk h hP X hPX hX
  · exact BN.solvOver_of_is2F4 h hP X hPX hX

theorem lieOvergroupFactRank2_holds :
    LieOvergroupFactRank2 :=
  lieOvergroupFactRank2_of lieOvergroupFactRank2Exc_holds

theorem lieOvergroupFact_holds :
    LieOvergroupFact :=
  lieOvergroupFact_of lieOvergroupFactRank1_holds lieOvergroupFactRank2_holds

end CFSG.Quasithin.H13.NQCat
