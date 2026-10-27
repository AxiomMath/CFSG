module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight69S7
public import CFSG.LocalAnalysis.UniquenessCase.UC22R880J4Facts
import CFSG.Adapters.GeneralizedFitting

public section

open CFSG.Open

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsSpor)

theorem s7J4Rank_holds :
    S7J4Rank := by
  intro Q _ _ Y hFY hY
  classical
  obtain ⟨e⟩ := hY
  have hJ4s : IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier .J4) :=
    CFSG.Sporadic.J4.isSimpleGroup_J4
  have hYs : IsSimpleGroup ↥Y := e.isSimpleGroup
  have hcardY : Nat.card ↥Y = 86775571046077562880 :=
    (Nat.card_congr e.toEquiv).trans CFSG.Sporadic.J4.card_J4
  have hZY : Subgroup.center ↥Y = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥Y) with h | h
    · exact h
    · exfalso
      have : IsMulCommutative ↥Y := ⟨⟨fun a b => by
        have ha : a ∈ Subgroup.center ↥Y := h ▸ Subgroup.mem_top a
        exact (Subgroup.mem_center_iff.mp ha b).symm⟩⟩
      have hp : (Nat.card ↥Y).Prime := IsSimpleGroup.prime_card
      rw [hcardY] at hp
      exact absurd hp (by norm_num)
  have hFn : (genFittingFStar Q).Normal := CFSG.ComponentClassification.GeneralizedFitting.normal Q
  have hF1 : genFittingFStar Q ≠ ⊥ := by
    intro h
    have hc := CFSG.Adapters.generalized_fitting_self_centralizing Q
    rw [h, Subgroup.coe_bot, Subgroup.centralizer_singleton_one] at hc
    have hQ1 : (⊤ : Subgroup Q) = ⊥ := le_bot_iff.mp hc
    have hY1 : Y = ⊥ := eq_bot_iff.mpr (le_top.trans hQ1.le)
    have : Nat.card ↥Y = 1 := by rw [hY1, Subgroup.card_bot]
    rw [hcardY] at this
    norm_num at this
  have hFeq : genFittingFStar Q = Y := by
    have hn : ((genFittingFStar Q).subgroupOf Y).Normal := hFn.subgroupOf Y
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((genFittingFStar Q).subgroupOf Y) with h | h
    · exfalso
      apply hF1
      rw [eq_bot_iff]
      intro x hx
      have hx' : (⟨x, hFY hx⟩ : ↥Y) ∈ (genFittingFStar Q).subgroupOf Y := hx
      rw [h, Subgroup.mem_bot] at hx'
      exact Subgroup.mem_bot.mpr (congrArg Subtype.val hx')
    · exact le_antisymm hFY (fun y hy => by
        have hy' : (⟨y, hy⟩ : ↥Y) ∈ (genFittingFStar Q).subgroupOf Y := h ▸ Subgroup.mem_top _
        exact hy')
  have hYn : Y.Normal := hFeq ▸ hFn
  have hCY : Subgroup.centralizer (Y : Set Q) ≤ ⊥ := by
    intro g hg
    have hgY : g ∈ Y := hFeq ▸ CFSG.Adapters.generalized_fitting_self_centralizing Q (hFeq ▸ hg)
    have hgZ : (⟨g, hgY⟩ : ↥Y) ∈ Subgroup.center ↥Y := by
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp hg) y y.2)
    rw [hZY, Subgroup.mem_bot] at hgZ
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val hgZ)
  let φ : Q →* MulAut ↥Y := MulAut.conjNormal
  have hφ : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro g hg
    apply hCY
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have h1 : φ g ⟨y, hy⟩ = ⟨y, hy⟩ := by rw [MonoidHom.mem_ker.mp hg]; rfl
    have h2 : g * y * g⁻¹ = y := congrArg Subtype.val h1
    calc y * g = g * y * g⁻¹ * g := by rw [h2]
      _ = g * y := by group
  refine CFSG.SectionRank.pRank_le (by norm_num) fun E _ hE => ?_
  have hB : IsElemAbelian 11 (E.map φ) := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
    · obtain ⟨_, ⟨u, hu, rfl⟩⟩ := a
      obtain ⟨_, ⟨v, hv, rfl⟩⟩ := b
      apply Subtype.ext
      change φ u * φ v = φ v * φ u
      rw [← map_mul, ← map_mul]
      exact congrArg φ (congrArg Subtype.val
        (hE.1.is_comm.comm (⟨u, hu⟩ : ↥E) ⟨v, hv⟩))
    · obtain ⟨u, hu, rfl⟩ := hx
      rw [← map_pow, hE.2 u hu, map_one]
  have h := CFSG.LocalAnalysis.UniquenessCase.UC22.F08.card_le_of_isSpor_J4_of_isElemAbelian
    ⟨e⟩ (E.map φ) hB
  rwa [Subgroup.card_map_of_injective hφ] at h

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
