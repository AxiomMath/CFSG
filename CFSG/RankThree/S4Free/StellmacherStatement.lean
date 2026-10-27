module

public import CFSG.RankThree.S4Free.StellmacherHosts

public section

universe u v

namespace CFSG.RankThree.S4Free

variable {S : Type u} [Group S]

@[expose] def IsStellmacherSubgroupSz (W : Subgroup S) : Prop :=
  W.Characteristic ∧ W ≠ ⊥ ∧
    ∀ (X : Type v) [Group X] (ι : S →* X), IsAdmissibleHost ι → SzSections X →
      (W.map ι).Normal

variable (S) in
@[expose] def StellmacherClauseSz : Prop :=
  ∃ W : Subgroup S, IsStellmacherSubgroupSz.{u, v} W

end CFSG.RankThree.S4Free
