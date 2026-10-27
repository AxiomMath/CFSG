module

public import CFSG.Quasithin.Vol2.Ch5Sec1L34FiveMain
public import CFSG.Quasithin.Vol2.Ch5Sec1L34FiveLieL3
public import CFSG.Quasithin.Vol2.Ch5Sec1L34FiveLieSp4
public import CFSG.Quasithin.Vol2.Ch5Sec1L34FiveLieG2
public import CFSG.Quasithin.Vol2.Ch5Sec1L34FiveLieD4

public section

namespace CFSG.Quasithin.H13.FiveNorm

theorem fiveRigidLie_holds :
    FiveRigidLie := by
  intro X _ _ h
  rcases h with h | h | h | h | h
  · exact LieL3.fiveRigid_quot_of_isPSL3 h
  · exact LieL3.fiveRigid_quot_of_isSL3 h
  · exact LieSp4.fiveRigid_quot_of_isPSp4 h
  · exact LieG2.fiveRigid_quot_of_isG2 h
  · exact LieD4.fiveRigid_quot_of_is3D4 h

end CFSG.Quasithin.H13.FiveNorm
