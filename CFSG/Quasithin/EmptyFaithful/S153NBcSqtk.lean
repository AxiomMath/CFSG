module

public import CFSG.Quasithin.Background.S1567Ctx
public import CFSG.Quasithin.Vol2.Ch12Sec8NonabG112Def

public section

namespace CFSG.Quasithin.S153N

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open scoped commutatorElement Pointwise

section Sqtk

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ E : Subgroup G} {t : G}

namespace BridgeC

theorem sqtkGroup_of_le {X : Type} [Group X] [Finite X] (hS : SQTKGroup X) (H : Subgroup X) :
    SQTKGroup ↥H := by
  refine ⟨fun p hp hp2 => ?_, hS.2.subgroup H⟩
  have h1 : CFSG.Open.pRank p (⊤ : Subgroup ↥H) ≤ CFSG.Open.pRank p (⊤ : Subgroup X) :=
    CFSG.SectionRank.pRank_top_le_of_injective hp.one_lt H.subtype H.subtype_injective
  have h2 : CFSG.Open.pRank p (⊤ : Subgroup X) ≤ 2 := hS.1 p hp hp2
  show CFSG.Open.pRank p (⊤ : Subgroup ↥H) ≤ 2
  omega

theorem pCoreOf_normalizer_ne_bot (k : Ctx67 G T Mc M V₁ V₂ E t) :
    pCoreOf 2 (Subgroup.normalizer (E : Set G)) ≠ ⊥ := by
  have hp : IsPGroup 2 ↥E := IsPGroup.of_card (n := 2) (by rw [k.L.card_eq]; norm_num)
  have hle : E ≤ pCoreOf 2 (Subgroup.normalizer (E : Set G)) :=
    le_pCoreOf_of_le_normalizer 2 Subgroup.le_normalizer le_rfl hp
  intro hbot
  rw [hbot] at hle
  have h := Subgroup.card_le_of_le hle
  rw [Subgroup.card_bot, k.L.card_eq] at h
  omega

theorem sqtkGroup_normalizer (k : Ctx67 G T Mc M V₁ V₂ E t) :
    SQTKGroup ↥(Subgroup.normalizer (E : Set G)) :=
  ⟨stronglyQuasithin_of_pCoreOf_ne_bot k.c.hyp.qtfe.qtke (pCoreOf_normalizer_ne_bot k),
    kGroup_of_pCoreOf_ne_bot k.c.hyp.qtfe.qtke k.c.hyp.qtfe.simple k.c.hyp.qtfe.nonabelian
      (pCoreOf_normalizer_ne_bot k)⟩

theorem sqtkGroup_centralizer (k : Ctx67 G T Mc M V₁ V₂ E t) :
    SQTKGroup ↥(Subgroup.centralizer (E : Set G)) := by
  have hCN : Subgroup.centralizer (E : Set G) ≤ Subgroup.normalizer (E : Set G) :=
    Subgroup.centralizer_le_normalizer _
  have hS := sqtkGroup_of_le (sqtkGroup_normalizer k)
    ((Subgroup.centralizer (E : Set G)).subgroupOf (Subgroup.normalizer (E : Set G)))
  refine ⟨?_, ?_⟩
  · intro p hp hp2
    have h1 := CFSG.SectionRank.pRank_top_le_of_injective hp.one_lt
      (Subgroup.subgroupOfEquivOfLe hCN).symm.toMonoidHom (Subgroup.subgroupOfEquivOfLe hCN).symm.injective
    exact h1.trans (hS.1 p hp hp2)
  · exact hS.2.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hCN).symm

end BridgeC

theorem bridgeC_sqtk (h113 : StageLemma14113) (k : Ctx67 G T Mc M V₁ V₂ E t) {Q : Type} [Group Q]
    (φ : ↥(Subgroup.centralizer (E : Set G)) →* Q) : IsQuotientOfSQTKTauCeti ↥φ.range := by
  have _ := h113
  have hS := BridgeC.sqtkGroup_centralizer k
  exact ⟨↥(Subgroup.centralizer (E : Set G)), inferInstance, inferInstance, hS.1, hS.2, φ.rangeRestrict,
    MonoidHom.rangeRestrict_surjective φ⟩

end Sqtk

end CFSG.Quasithin.S153N
