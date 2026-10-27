module


import CFSG.ClassicalGroups.PCoreSection
import CFSG.RankThree.GF2n.Stroth78.Sec2Six
public import CFSG.RankThree.GF2n.Stroth78.Sec2Defs
public import CFSG.RankThree.OrthogonalInvolutions.Basic

public section

namespace CFSG.RankThree.GF2n.Stroth78

open CFSG CFSG.Open CFSG.ClassicalGroups.PCoreSection CFSG.RankThree.GF2n.Tim79a
open CFSG.LargeExtraspecial.Timmesfeld
open CFSG.Timmesfeld
open CFSG.RankThree.OrthogonalInvolutions Module
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G} {E F : Subgroup G}

theorem pCoreOf_Xsub_normal (S : Setting z E F) (a : G) (p : ℕ) :
    (pCoreOf p (Xsub S a)).Normal := by
  haveI : (Xsub S a).Normal := Xsub_normal S a
  have hle : (⊤ : Subgroup (Hbar z)) ≤
      Subgroup.normalizer (pCoreOf p (Xsub S a) : Set (Hbar z)) := by
    rw [← Subgroup.normalizer_eq_top (Xsub S a)]
    exact CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf p (Xsub S a)
  exact Subgroup.normalizer_eq_top_iff.mp (le_antisymm le_top hle)

end CFSG.RankThree.GF2n.Stroth78
