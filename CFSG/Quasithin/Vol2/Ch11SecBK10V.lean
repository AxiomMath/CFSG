module

public import CFSG.Quasithin.Vol2.Ch11SecBK10G
public import CFSG.Quasithin.Vol2.Ch11SecO8HS
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A3Native36
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A3Native38
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A134Final
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239InspNotRankLie
public import CFSG.Quasithin.Background.KnownMultTypes

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecD

namespace BK10

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.SectionRank

theorem sqtkSimpleList_xCls
    {G : Type} [Group G] [Finite G] {H J : Subgroup G}
    (hH : IsSQTKCat ↥H) (hJH : J ≤ H) (hJq : CFSG.IsQuasisimple (JBar J)) :
    Milestones.SQTKSimpleList (XCls J) := by
  have hJ1 : IsSQTKCat ↥(J.subgroupOf H) := hH.subgroup _
  set e₀ := Subgroup.subgroupOfEquivOfLe hJH with he₀
  have hJ2 : IsSQTKCat ↥J :=
    ⟨isStronglyQuasithin_of_mulEquiv e₀.symm hJ1.1, hJ1.2.of_mulEquiv e₀.symm⟩
  have hJ3 : IsSQTKCat (JBar J) :=
    ⟨(isStronglyQuasithin_quotient_two_group_iff (CFSG.pCore 2 ↥J) CFSG.pCore_isPGroup).2 hJ2.1,
      hJ2.2.quotient _⟩
  set e₁ : ↥(⊤ : Subgroup (JBar J)) ≃* JBar J := Subgroup.topEquiv with he₁
  set e : (↥(⊤ : Subgroup (JBar J)) ⧸ Subgroup.center ↥(⊤ : Subgroup (JBar J))) ≃* XCls J :=
    QuotientGroup.congr _ _ e₁ (Subgroup.map_center_eq e₁) with he
  have := hJq.2.1
  have : IsSimpleGroup
      (↥(⊤ : Subgroup (JBar J)) ⧸ Subgroup.center ↥(⊤ : Subgroup (JBar J))) := e.isSimpleGroup
  have hnonab : ∃ a b : ↥(⊤ : Subgroup (JBar J)) ⧸ Subgroup.center ↥(⊤ : Subgroup (JBar J)),
      a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hJq.2.2
    refine ⟨e.symm a, e.symm b, fun h => hab ?_⟩
    have := congrArg e h
    rwa [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at this
  exact Ch1.sqtkSimpleList_of_mulEquiv e.symm
    (Milestones.cl_lit_sqtk_simple_list_section (JBar J) hJ3 ⊤ _ hnonab)

theorem factCCompTorus_of_dispatch
    (hdisp : ∀ (X : Type) [Group X] [Finite X], Milestones.SQTKSimpleList X →
      TorusRigid X ∨ 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X)) :
    FactCCompTorus := by
  intro G _ _ H S J A D hH hS hJ hJq hJ3 hcop hAS hD hg
  have hHyp := Vol2Native.SQTKHypCat.quotient_pCore ↥H hH
  have h37 := Vol2Native.a37ForSQTKCat_proved _ hHyp
  have h38 := Vol2Native.a38ForSQTKCat_of_facts CFSG.Quasithin.mult2Fact
    Vol2Native.a134SQTKFactCat Vol2Native.a36CoreForSQTKCat_proved
    Vol2Native.a37ForSQTKCat_proved _ hHyp
  have hlist := sqtkSimpleList_xCls hH (le_of_mem_cComp hJ) hJq
  rcases hdisp (XCls J) hlist with hT | h3
  · exact commutator_le_of_torusRigid h37 h38 hS hJ hJq hT hcop hAS hD hg
  · exfalso
    have h1 := Vol2Native.L239.two_le_pRank_of_surjective Nat.prime_three (by norm_num) (piX J)
      (piX_surjective J) (by rwa [pRank_eq_open_pRank_top])
    omega

end BK10

end CFSG.Quasithin.Vol2.Ch11.SecD
