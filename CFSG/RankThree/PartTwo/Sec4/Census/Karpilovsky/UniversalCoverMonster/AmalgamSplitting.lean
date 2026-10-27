module

public import CFSG.Monster.GMS.AmalgamIso
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.SectionRank.Framework.Semisimple

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster

open CFSG.Monster.GMS
open scoped commutatorElement

section Perfect

variable {X E : Type} [Group X] [Group E] (π : E →* X)

theorem ker_eq_bot_of_section [Group.IsPerfect E] (hC : π.ker ≤ Subgroup.center E) (s : X →* E)
    (hs : ∀ x, π (s x) = x) : π.ker = ⊥ := by
  have hle : (⊤ : Subgroup E) ≤ s.range := by
    rw [← Group.IsPerfect.commutator_eq_top (G := E), _root_.commutator_def,
      Subgroup.commutator_le]
    intro e₁ _ e₂ _
    have h₁ : e₁ = s (π e₁) * ((s (π e₁))⁻¹ * e₁) := by group
    have h₂ : e₂ = s (π e₂) * ((s (π e₂))⁻¹ * e₂) := by group
    have hz₁ : (s (π e₁))⁻¹ * e₁ ∈ Subgroup.center E := hC (by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hs, inv_mul_cancel])
    have hz₂ : (s (π e₂))⁻¹ * e₂ ∈ Subgroup.center E := hC (by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hs, inv_mul_cancel])
    rw [h₁, h₂, CFSG.SectionRank.commutatorElement_mul_mem_center _ _ hz₁ hz₂]
    refine ⟨⁅π e₁, π e₂⁆, ?_⟩
    rw [map_commutatorElement]
  rw [eq_bot_iff]
  intro z hz
  obtain ⟨x, hx⟩ := hle (Subgroup.mem_top z)
  have hπz : π z = 1 := hz
  have : x = 1 := by rw [← hs x, hx, hπz]
  rw [Subgroup.mem_bot, ← hx, this, map_one]

end Perfect

section Amalgam

variable {V : Type*} {Γ : SimpleGraph V} {X : Type} [Group X] [MulAction X V] {ι : Type*}
  {E : Type} [Group E]

theorem exists_section_of_titsData (D : TitsData Γ X ι) (π : E →* X) (σv : D.Xv →* E)
    (σe : D.Xe →* E) (σt : ∀ j, D.Xt j →* E) (hv : ∀ x, π (σv x) = x) (he : ∀ x, π (σe x) = x)
    (ht : ∀ j x, π (σt j x) = x)
    (hve : ∀ a (ha : a ∈ D.Xv) (hb : a ∈ D.Xe), σv ⟨a, ha⟩ = σe ⟨a, hb⟩)
    (hvt : ∀ j a (ha : a ∈ D.Xv) (hb : a ∈ D.Xt j), σv ⟨a, ha⟩ = σt j ⟨a, hb⟩)
    (het : ∀ j a (ha : a ∈ D.Xe) (hb : a ∈ D.Xt j), σe ⟨a, ha⟩ = σt j ⟨a, hb⟩) :
    ∃ s : X →* E, ∀ x, π (s x) = x := by
  obtain ⟨Φ, ⟨hΦv, hΦe, hΦt⟩, -⟩ := D.existsUnique_hom σv σe σt hve hvt het
  refine ⟨Φ, fun x => ?_⟩
  have := D.hom_eq_id (π.comp Φ) (fun a => by simp [hΦv a, hv a]) (fun a => by simp [hΦe a, he a])
    (fun j a => by simp [hΦt j a, ht j a])
  exact congrArg (fun f : X →* X => f x) this

end Amalgam

end CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster
