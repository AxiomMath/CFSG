
module

public import CFSG.Quasithin.Background.A3Structure37Base

public import CFSG.Quasithin.Background.A3StructureFacts
public import CFSG.Quasithin.Background.A3Structure36ABasic
public import CFSG.Quasithin.Background.A3Structure37Comm
public import CFSG.Quasithin.Background.A3Structure37Key

public section

namespace CFSG.Quasithin

namespace A37

open scoped commutatorElement

theorem commutator_eq_bot_of_extra {G : Type} [Group G] [Finite G] {L₁ L₂ : Subgroup G}
    (hn : L₂ ≤ Subgroup.normalizer (L₁ : Set G)) [Group.IsPerfect ↥L₁] [Group.IsPerfect ↥L₂]
    (hc : ⁅L₁, L₂⁆ ≤ (CFSG.fittingSubgroup ↥L₁).map L₁.subtype)
    (hF : CFSG.fittingSubgroup ↥L₁ ≠ ⊤) (hX : A36Extra ↥L₁) : ⁅L₁, L₂⁆ = ⊥ := by
  have hcent := centralizes_fitting hn hc hF hX
  have hle : ⁅L₂, L₁⁆ ≤ (CFSG.fittingSubgroup ↥L₁).map L₁.subtype := by
    rw [Subgroup.commutator_comm]
    exact hc
  have h2 : ⁅⁅L₂, L₁⁆, L₂⁆ = ⊥ :=
    le_bot_iff.1 ((Subgroup.commutator_mono hle le_rfl).trans hcent.le)
  have := CFSG.LocalCores.perfect_double_commutator (P := L₂) (X := L₁) ‹Group.IsPerfect ↥L₂› h2
  rwa [Subgroup.commutator_comm] at this

theorem a37_of_a36 {G : Type} [Group G] [Finite G] (h36 : A36Statement G) : A37Statement G := by
  intro L₁ h₁ L₂ h₂ hne
  have hS₁ := cComp_normal_span h₁
  have hS₂ := cComp_normal_span h₂
  have hn₁ : cCompSpan (⊤ : Subgroup G) ≤ Subgroup.normalizer (L₁ : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hS₁.1).mp hS₁.2
  have hn₂ : cCompSpan (⊤ : Subgroup G) ≤ Subgroup.normalizer (L₂ : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hS₂.1).mp hS₂.2
  have hL₂N : L₂ ≤ Subgroup.normalizer (L₁ : Set G) := (le_cCompSpan h₂).trans hn₁
  have : Group.IsPerfect ↥L₁ := A36A.isPerfect_of_mem_cComp h₁
  have : Group.IsPerfect ↥L₂ := A36A.isPerfect_of_mem_cComp h₂
  obtain ⟨hconc, hcom₁, hextra⟩ := h36 L₁ h₁
  obtain ⟨-, hcom₂, -⟩ := h36 L₂ h₂
  have hc : ⁅L₁, L₂⁆ ≤ (CFSG.fittingSubgroup ↥L₁).map L₁.subtype := by
    have h := commutator_le_oddCoreOf h₁ h₂ hne (quasisimple_quotient_oddCore hcom₁)
      (quasisimple_quotient_oddCore hcom₂) hL₂N
    rwa [oddCoreOf, ← hcom₁.1] at h
  rcases hconc with ⟨hcomp, -, -⟩ | ⟨hcomp, -, -⟩ | h3 | h4
  · exact commutator_eq_bot_of_quasisimple hcomp.1 hcom₁ hc
  · exact commutator_eq_bot_of_quasisimple hcomp.1 hcom₁ hc
  · exact commutator_eq_bot_of_extra hL₂N hc (fitting_ne_top hcom₁) (hextra (Or.inl h3))
  · exact commutator_eq_bot_of_extra hL₂N hc (fitting_ne_top hcom₁) (hextra (Or.inr h4))

end A37

theorem a37 (hF : A129One) {G : Type} [Group G] (hG : SQTKHyp G) (h36 : A36Statement G) :
    A37Statement G := by
  have _ := hF
  have := hG.finite
  exact A37.a37_of_a36 h36

end CFSG.Quasithin
