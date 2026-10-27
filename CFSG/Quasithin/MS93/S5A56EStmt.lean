module

public import CFSG.Quasithin.MS93.S5Stmt

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible

namespace S5

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}

@[expose] def Concl56e (h : PUHyp M T L) (q : ℕ) {F : Type} [Field F]
    (a : ↥M →* ↥(StatedSp 2 F)) (α' : Vtx (puAmalgam h.le)) (l : Submodule F (MSP.V4 F))
    (g x : (puAmalgam h.le).Universal) : Prop :=
  Concl56 h q a α' l g x ∧
    (¬ (q = 2 ∧ (Qv _ (baseA _)).relIndex (jOff h.le L q (baseA _) (baseB _)) = q ^ 2) →
      x ∈ vPre h.le a (MSP.stab l))

end S5

end CFSG.Quasithin.MS93
