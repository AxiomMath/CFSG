module

public import CFSG.OddTranspositions.SevenLocalSecond
public import CFSG.OddTranspositions.SixNineUnconditional
public import CFSG.OddTranspositions.SixSeven

public section

namespace CFSG.OddTranspositions

open CFSG.Timmesfeld CFSG.Timmesfeld.Connectivity CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem alpha_mem_Dalpha_of_mem (hC : HypothesisC D) {δ : Set G}
    (hδ : δ ∈ Dalpha D hC.alpha) : hC.alpha ∈ Dalpha D δ := by
  obtain ⟨hδclass, -, hδne, hδcomm⟩ := mem_Dalpha_iff.mp hδ
  obtain ⟨g, hg⟩ := mem_blockClass_iff.mp hδclass
  rw [mem_Dalpha_iff]
  refine ⟨?_, hC.isBlock_alpha.subset, fun h => hδne h.symm, ?_⟩
  · rw [mem_blockClass_iff]
    refine ⟨g⁻¹, ?_⟩
    rw [hg]
    change hC.alpha = cimg g⁻¹ ((fun z => g * z * g⁻¹) '' hC.alpha)
    have hcomp : cimg g⁻¹ ((fun z => g * z * g⁻¹) '' hC.alpha) =
        (fun z => g⁻¹ * (g * z * g⁻¹) * (g⁻¹)⁻¹) '' hC.alpha := by
      change (fun z => g⁻¹ * z * (g⁻¹)⁻¹) '' ((fun z => g * z * g⁻¹) '' hC.alpha) =
        (fun z => g⁻¹ * (g * z * g⁻¹) * (g⁻¹)⁻¹) '' hC.alpha
      rw [Set.image_image]
    have hfun : (fun z => g⁻¹ * (g * z * g⁻¹) * (g⁻¹)⁻¹) = id := by
      funext z
      change g⁻¹ * (g * z * g⁻¹) * (g⁻¹)⁻¹ = z
      group
    rw [hcomp, hfun, Set.image_id]
  · intro a ha b hb
    exact (hδcomm b hb a ha).symm

theorem localSecond_of_DalphaStar_triangles (hC : HypothesisC D)
    (h : ∀ x ∈ DalphaStar D hC.alpha, ∀ y ∈ DalphaStar D hC.alpha,
      ∀ t ∈ DalphaStar D hC.alpha,
        IsTriangle D x y t → orderOf (x * t * y) = 4) :
    LocalSecond D := by
  intro d hd x y t hxd hyd htd htri
  classical
  obtain ⟨g, hg⟩ := isConj_iff.mp
    (isConj_of_isClass hC.setup.isClass hd (hC.isBlock_alpha.subset hC.d_mem_alpha))
  let x' : G := g * x * g⁻¹
  let y' : G := g * y * g⁻¹
  let t' : G := g * t * g⁻¹
  have hx'D : x' ∈ D := hC.setup.normal g x htri.1
  have hy'D : y' ∈ D := hC.setup.normal g y htri.2.2.1
  have ht'D : t' ∈ D := hC.setup.normal g t htri.2.1
  have htri' : IsTriangle D x' y' t' := isTriangle_conj hC.setup.normal htri
  have hx'd : Commute x' hC.d := by simpa [x', hg] using hxd.conj g
  have hy'd : Commute y' hC.d := by simpa [y', hg] using hyd.conj g
  have ht'd : Commute t' hC.d := by simpa [t', hg] using htd.conj g
  have hx'mem : x' ∈ hC.alpha ∪ DalphaStar D hC.alpha :=
    mem_alpha_or_DalphaStar_of_commute hC hx'D hx'd
  have hy'mem : y' ∈ hC.alpha ∪ DalphaStar D hC.alpha :=
    mem_alpha_or_DalphaStar_of_commute hC hy'D hy'd
  have ht'mem : t' ∈ hC.alpha ∪ DalphaStar D hC.alpha :=
    mem_alpha_or_DalphaStar_of_commute hC ht'D ht'd
  have hord : orderOf (x' * t' * y') = orderOf (x * t * y) := by
    have e : x' * t' * y' = g * (x * t * y) * g⁻¹ := by
      simp only [x', y', t']
      group
    rw [e, orderOf_conj_eq]
  by_cases hx'α : x' ∈ hC.alpha
  ·
    by_cases hy'α : y' ∈ hC.alpha
    ·
      have ht'α : t' ∈ hC.alpha := by
        rcases ht'mem with h | h
        · exact h
        · exfalso
          obtain ⟨β, hβ, ht'β⟩ := h
          exact htri'.2.2.2.2.2.2 (hβ.2.2.2 y' hy'α t' ht'β).symm
      obtain ⟨e, heE⟩ := OddLocal.nonempty hC.hE
      have heDs : e ∈ DalphaStar D hC.alpha := by
        rw [hC.DalphaStar_alpha]
        exact heE
      obtain ⟨δ, hδ, heδ⟩ := heDs
      have hαδ : hC.alpha ∈ Dalpha D δ := alpha_mem_Dalpha_of_mem hC hδ
      obtain ⟨g₁, hg₁⟩ := mem_blockClass_iff.mp hδ.1
      have hx'' : g₁⁻¹ * x' * g₁ ∈ DalphaStar D hC.alpha := by
        have hmem0 := DalphaStar.conj hC.setup.normal ⟨hC.alpha, hαδ, hx'α⟩ g₁⁻¹
        have hmem : g₁⁻¹ * x' * g₁ ∈ DalphaStar D (cimg g₁⁻¹ δ) := by
          simpa [cimg] using hmem0
        have hαeq : cimg g₁⁻¹ δ = hC.alpha := by
          rw [hg₁]
          change (fun z => g₁⁻¹ * z * (g₁⁻¹)⁻¹) '' cimg g₁ hC.alpha = hC.alpha
          rw [Set.image_image]
          have hfun : (fun z => g₁⁻¹ * (g₁ * z * g₁⁻¹) * (g₁⁻¹)⁻¹) = id := by
            funext z
            change g₁⁻¹ * (g₁ * z * g₁⁻¹) * (g₁⁻¹)⁻¹ = z
            group
          rw [hfun, Set.image_id]
        rwa [hαeq] at hmem
      have hy'' : g₁⁻¹ * y' * g₁ ∈ DalphaStar D hC.alpha := by
        have hmem0 := DalphaStar.conj hC.setup.normal ⟨hC.alpha, hαδ, hy'α⟩ g₁⁻¹
        have hmem : g₁⁻¹ * y' * g₁ ∈ DalphaStar D (cimg g₁⁻¹ δ) := by
          simpa [cimg] using hmem0
        have hαeq : cimg g₁⁻¹ δ = hC.alpha := by
          rw [hg₁]
          change (fun z => g₁⁻¹ * z * (g₁⁻¹)⁻¹) '' cimg g₁ hC.alpha = hC.alpha
          rw [Set.image_image]
          have hfun : (fun z => g₁⁻¹ * (g₁ * z * g₁⁻¹) * (g₁⁻¹)⁻¹) = id := by
            funext z
            change g₁⁻¹ * (g₁ * z * g₁⁻¹) * (g₁⁻¹)⁻¹ = z
            group
          rw [hfun, Set.image_id]
        rwa [hαeq] at hmem
      have ht'' : g₁⁻¹ * t' * g₁ ∈ DalphaStar D hC.alpha := by
        have hmem0 := DalphaStar.conj hC.setup.normal ⟨hC.alpha, hαδ, ht'α⟩ g₁⁻¹
        have hmem : g₁⁻¹ * t' * g₁ ∈ DalphaStar D (cimg g₁⁻¹ δ) := by
          simpa [cimg] using hmem0
        have hαeq : cimg g₁⁻¹ δ = hC.alpha := by
          rw [hg₁]
          change (fun z => g₁⁻¹ * z * (g₁⁻¹)⁻¹) '' cimg g₁ hC.alpha = hC.alpha
          rw [Set.image_image]
          have hfun : (fun z => g₁⁻¹ * (g₁ * z * g₁⁻¹) * (g₁⁻¹)⁻¹) = id := by
            funext z
            change g₁⁻¹ * (g₁ * z * g₁⁻¹) * (g₁⁻¹)⁻¹ = z
            group
          rw [hfun, Set.image_id]
        rwa [hαeq] at hmem
      have htri'' : IsTriangle D (g₁⁻¹ * x' * g₁) (g₁⁻¹ * y' * g₁) (g₁⁻¹ * t' * g₁) := by
        simpa using isTriangle_conj hC.setup.normal htri' (g := g₁⁻¹)
      have h4 := h _ hx'' _ hy'' _ ht'' htri''
      have e : (g₁⁻¹ * x' * g₁) * (g₁⁻¹ * t' * g₁) * (g₁⁻¹ * y' * g₁) =
          g₁⁻¹ * (x' * t' * y') * g₁ := by group
      rw [e] at h4
      have h4' : orderOf (x' * t' * y') = 4 := by
        have hconj := orderOf_conj_eq (g₁⁻¹) (x' * t' * y')
        rw [show (g₁⁻¹)⁻¹ = g₁ by group] at hconj
        rw [← hconj]
        exact h4
      rw [← hord]
      exact h4'
    ·
      exfalso
      rcases hy'mem with h | h
      · exact hy'α h
      · obtain ⟨β, hβ, hy'β⟩ := h
        exact htri'.2.2.2.2.2.1 (hβ.2.2.2 x' hx'α y' hy'β)
  ·
    rcases hx'mem with h | hx'Dα
    · exact absurd h hx'α
    · have hy'Dα : y' ∈ DalphaStar D hC.alpha := by
        rcases hy'mem with h | h
        · exfalso
          obtain ⟨β, hβ, hx'β⟩ := hx'Dα
          exact htri'.2.2.2.2.2.1 (hβ.2.2.2 y' h x' hx'β).symm
        · exact h
      have ht'Dα : t' ∈ DalphaStar D hC.alpha := by
        rcases ht'mem with h | h
        · exfalso
          obtain ⟨β, hβ, hy'β⟩ := hy'Dα
          exact htri'.2.2.2.2.2.2 (hβ.2.2.2 t' h y' hy'β)
        · exact h
      have h4 := h x' hx'Dα y' hy'Dα t' ht'Dα htri'
      rw [← hord]
      exact h4

end CFSG.OddTranspositions

