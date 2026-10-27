module

public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefsB
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenTwentyThree

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

private theorem centralizer_singleton_le_M_of_mem_V₀ (D : Data G) {V₀ V : Subgroup G}
    (h : Hyp125 D V₀ V) {z : G} (hzV₀ : z ∈ V₀) (hz : z ≠ 1) :
    centralizer ({z} : Set G) ≤ D.M := by
  have hXV : Subgroup.zpowers z ≤ V₀ := Subgroup.zpowers_le.2 hzV₀
  have hX1 : Subgroup.zpowers z ≠ ⊥ := Subgroup.zpowers_ne_bot.mpr hz
  have hN := h.hyp62.normalizer_le _ hXV hX1
  have hcent_eq : centralizer ({z} : Set G) = centralizer (Subgroup.zpowers z : Set G) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  exact ((le_of_eq hcent_eq).trans (Subgroup.centralizer_le_normalizer _)).trans hN

theorem s16c1_mkTil_ne_one {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hS : Sect16 D V₀ V L hV) {x : IntMod V hV} (hx : Setup1645 D V hV x) :
    mkTil V₀ V hV x ≠ 1 := by
  intro h1
  have hx0 : x.val ∈ V₀ := by
    have h : x ∈ modNull V₀ V hV :=
      (QuotientGroup.eq_one_iff (N := modNull V₀ V hV) x).1 h1
    exact (mem_modNull V₀ V hV x).1 h
  exact hx.not_le
    (centralizer_singleton_le_M_of_mem_V₀ D hS.setting.hyp16.hyp125 hx0 hx.ne_one)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
