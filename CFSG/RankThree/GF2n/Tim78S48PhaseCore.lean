module

public import CFSG.RankThree.GF2n.Tim78S48Defs

public section

namespace CFSG.RankThree.GF2n.Tim78

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open

variable {G : Type} [Group G]

structure Core48 (Q B T : Subgroup G) (g : G) : Prop where
  T_not_cent : ¬ ∀ t ∈ T, ∀ b ∈ conjSubgroup g B, t * b = b * t
  Tg_not_cent : ¬ ∀ t ∈ conjSubgroup g T, ∀ b ∈ B, t * b = b * t
  conj : ∃ x ∈ T ⊔ conjSubgroup g T, conjSubgroup g T = conjSubgroup x T ∧
    conjSubgroup g B = conjSubgroup x B
  T_inf_W : T ⊓ (B ⊔ conjSubgroup g B) = B
  Tg_inf_W : conjSubgroup g T ⊓ (B ⊔ conjSubgroup g B) = conjSubgroup g B
  phase : Phase1a Q B T g

end CFSG.RankThree.GF2n.Tim78
