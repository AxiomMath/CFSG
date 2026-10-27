module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.PartTwo.Sec21.FF84S4PreBasic

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S4

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF84
open CFSG.Assembly (InCatalog)
open CFSG.Assembly.RankThreeEven (localRank)
open CFSG.RankThree.LocalRank (aschbacherSolvableCore)

variable {G : Type} [Group G] [Finite G] {b b₁ b₂ : G} {L B K : Subgroup G}

theorem cen_bb₁_ne_top (h : FF84Sec4 b L B K b₁ b₂) : Cen (b * b₁) ≠ ⊤ := by
  intro htop
  have hc : b * b₁ ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro g
    have : g ∈ Cen (b * b₁) := htop ▸ Subgroup.mem_top g
    exact Subgroup.mem_centralizer_singleton_iff.1 this
  haveI := h.hyp.simple
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with hb | ht
  · rw [hb] at hc
    exact bb₁_ne_one h (Subgroup.mem_bot.1 hc)
  · obtain ⟨x, y, hxy⟩ := h.hyp.nonab
    have hx : x ∈ Subgroup.center G := ht ▸ Subgroup.mem_top x
    exact hxy ((Subgroup.mem_center_iff.1 hx y).symm)

theorem isTypeLnq_subgroupOf {D : Subgroup G} (hKD : K ≤ D) (hK : IsTypeLnq 2 2 2 K) :
    IsTypeLnq 2 2 2 (K.subgroupOf D) := by
  let e : ↥(K.subgroupOf D) ≃* ↥K := Subgroup.subgroupOfEquivOfLe hKD
  let e' : ↥(K.subgroupOf D) ⧸ Subgroup.center ↥(K.subgroupOf D) ≃*
      ↥K ⧸ Subgroup.center ↥K :=
    QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)
  exact CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv e'.symm hK

@[expose] def S43_tail : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (b : G) (L B K : Subgroup G) (b₁ b₂ : G),
    FF84Sec4 b L B K b₁ b₂ → Odd (Nat.card (Opp 3 (Cen b)))

end CFSG.RankThree.PartTwo.Sec21.FF84.S4
