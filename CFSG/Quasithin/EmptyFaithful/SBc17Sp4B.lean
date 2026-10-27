module

public import CFSG.Quasithin.EmptyFaithful.SBc17Sp4
public import CFSG.Quasithin.EmptyFaithful.SBc17Ent0
public import CFSG.Quasithin.Background.C2Blocks

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace SBc17

variable {G : Type} [Group G] [Finite G]

theorem false_of_sp4_block {J : Subgroup G} (h : IsSp4Block J) (hrank : CFSG.pRank 5 ↥J ≤ 1) :
    False := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨-, F, hF, hFin, hcard, α, hα, hker, -⟩ := h
  have hFfin : Finite F := inferInstance
  have h2 := two_le_pRank_statedSp_four (F := F) hcard
  have e : (↥J ⧸ CFSG.pCore 2 ↥J) ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSp 2 F) :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective α hα)
  have h3 := CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 5) (by norm_num) e
  have h4 := CFSG.SectionRank.pRank_quotient_two_group (CFSG.pCore 2 ↥J) (isPGroup_pCore J)
    (r := 5) (by norm_num) (by norm_num)
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top] at hrank
  omega

end SBc17

end CFSG.Quasithin
