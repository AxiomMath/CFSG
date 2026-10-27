module

public import CFSG.RankThree.GF2n.Stroth80.Defs

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G]

theorem pCore_two_eq_bot_of_simple [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) : pCore 2 G = ⊥ := by
  haveI : (pCore 2 G).Normal := pCore_normal (p := 2) (G := G)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (pCore 2 G) with h | h
  · exact h
  · exfalso
    have hP : IsPGroup 2 ↥(⊤ : Subgroup G) := h ▸ pCore_isPGroup (p := 2) (G := G)
    have hP' : IsPGroup 2 G :=
      hP.of_surjective (⊤ : Subgroup G).subtype Subgroup.topEquiv.surjective
    have hnil : Group.IsNilpotent G := hP'.isNilpotent
    have hcomm : ∀ a b : G, a * b = b * a :=
      IsSimpleGroup.comm_iff_isSolvable.mpr (inferInstance : Group.IsSolvable G)
    obtain ⟨a, b, hab⟩ := hnonab
    exact hab (hcomm a b)

theorem stroth_hyp_of_simple [Finite G] [IsSimpleGroup G]
    {M V Q : Subgroup G} (hnonab : ∃ a b : G, a * b ≠ b * a) (H : Tim79.Hyp79 M V Q) :
    StrothHyp M Q V :=
  stroth_hyp_of_hyp79 (pCore_two_eq_bot_of_simple hnonab) H

end CFSG.RankThree.GF2n.Stroth80
