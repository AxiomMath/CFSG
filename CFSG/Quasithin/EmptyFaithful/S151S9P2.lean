module

public import CFSG.Quasithin.EmptyFaithful.S151S9P2C

public section

namespace CFSG.Quasithin

namespace HSRuLoc

open CFSG.Open CFSG.QuasithinUnique CFSG.Blueprint Lift
open scoped Pointwise

variable {G : Type} [Group G]

theorem lift_struct [Finite G] {L S : Subgroup G} {H : Type} [Group H] [Finite H] {π : ↥L →* H}
    {P Kb Rb : Subgroup H} {e : ℕ} (c : LiftCtx L S π P Kb Rb e) :
    liftK L π Kb ≤ L ∧ S ≤ Subgroup.normalizer (liftK L π Kb : Set G) ∧
      liftK L π Kb ∈ cComp (liftK L π Kb ⊔ S) ∧ IsSylowTwoOf S (liftK L π Kb ⊔ S) ∧
      CharTwo (liftK L π Kb) ∧
      (∃ α : ↥(liftK L π Kb) →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 2)),
        IsModO2Surj (liftK L π Kb) α) ∧
      ¬ liftK L π Kb ≤ Subgroup.centralizer (centerOf (S ⊓ L) : Set G) :=
  ⟨liftK_le c, le_normalizer_liftK c, liftK_mem_cComp c,
    isSylowTwoOf_sup (liftK_le c) (le_normalizer_liftK c) c.hS2 c.hsyl, charTwo_liftK c,
    isModO2Surj_liftK c, not_liftK_le_centralizer c⟩

end HSRuLoc

end CFSG.Quasithin
