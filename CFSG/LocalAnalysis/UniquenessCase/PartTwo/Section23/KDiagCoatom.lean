module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ParabolicTransfer

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup

variable {X : Type} [Group X] [Finite X]

theorem kDiag_of_sylow_normalizer_coatom
    (hcoat : ∀ S : Sylow 2 X, IsCoatom (Subgroup.normalizer (S : Set X))) :
    ∀ (θ : MulAut X), Odd (orderOf θ) →
    ∀ S : Sylow 2 X, (∀ x ∈ (S : Subgroup X), θ x ∈ (S : Subgroup X)) →
    ∀ (P : Subgroup X), IsParabolicTwo X P →
      (S : Subgroup X) ≤ Subgroup.normalizer (P : Set X) →
      ∀ x ∈ P, θ x ∈ P := by
  intro θ hθ S hSθ P hPpar hSP x hx
  obtain ⟨S₀, hS₀P⟩ := hPpar
  rcases (hcoat S₀).le_iff.mp hS₀P with hPtop | hPN
  · rw [hPtop]
    exact Subgroup.mem_top x
  · have hSP' : (S : Subgroup X) ≤ P :=
      IsParabolicTwo.le_of_le_normalizer ⟨S₀, hS₀P⟩ S.isPGroup' hSP
    have hS₀P' : (S₀ : Subgroup X) ≤ P := Subgroup.le_normalizer.trans hS₀P
    have hnorm : (S₀.subgroupOf P).Normal := by
      refine (Subgroup.normal_subgroupOf_iff_le_normalizer hS₀P').mpr ?_
      rw [hPN]
      exact le_rfl
    let T₁ : Sylow 2 P := S₀.subtype hS₀P'
    let T₂ : Sylow 2 P := S.subtype hSP'
    have hnormT₁ : (T₁ : Subgroup P).Normal := hnorm
    have hT₂T₁ : T₂ = T₁ := by
      haveI : (T₁ : Subgroup P).Normal := hnormT₁
      obtain ⟨p, hp⟩ := MulAction.exists_smul_eq P T₁ T₂
      rw [← hp, Sylow.smul_eq_of_normal]
    have hSS₀ : S = S₀ := Sylow.subtype_injective hT₂T₁
    let Ssub : Subgroup X := (S : Subgroup X)
    have hPN' : P = Subgroup.normalizer (Ssub : Set X) := by
      rw [hPN]
      change Subgroup.normalizer (S₀ : Set X) = Subgroup.normalizer (S : Set X)
      have hset : (S₀ : Set X) = (S : Set X) := by
        rw [hSS₀]
      rw [hset]
    have hmapS : Ssub.map θ.toMonoidHom = Ssub := by
      refine Subgroup.eq_of_le_of_card_ge ?_ ?_
      · rintro _ ⟨y, hy, rfl⟩
        exact hSθ y hy
      · rw [Subgroup.card_map_of_injective θ.injective]
    have hmapN : (Subgroup.normalizer (Ssub : Set X)).map θ.toMonoidHom =
        Subgroup.normalizer (Ssub : Set X) := by
      rw [Subgroup.map_equiv_normalizer_eq Ssub θ, hmapS]
    rw [hPN'] at hx ⊢
    exact hmapN ▸ Subgroup.mem_map_of_mem θ.toMonoidHom hx

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
