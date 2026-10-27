module

public import CFSG.RankThree.S4Free.StellmacherStatement

public section

universe u v

namespace CFSG.RankThree.S4Free

@[expose] def StellmacherSzAll : Prop :=
  ∀ (S : Type u) [Group S] [Finite S], IsPGroup 2 S → Nontrivial S →
    StellmacherClauseSz.{u, v} S

end CFSG.RankThree.S4Free
