module

public import CFSG.Timmesfeld.Bridge.RootStructClassTwo
public import CFSG.Timmesfeld.Exceptional.PlaneComm
public import CFSG.Timmesfeld.Exceptional.CaseIThm31

public section

namespace CFSG.Timmesfeld.Bridge

open CFSG.Timmesfeld

variable {G : Type*} [Group G] {D : Set G}

@[expose] def NCoreCommutatorInRoot (D : Set G) : Prop :=
  ∀ y ∈ D, ∀ g ∈ nCore D y, ∀ h ∈ nCore D y, g * h * g⁻¹ * h⁻¹ ∈ rootGroup D y

@[expose] def NCoreStep : Prop :=
  ∀ (G : Type) [Group G] (D : Set G), Hyp G D → RootIH G → RootClosure D →
    NCoreCommutatorInRoot D

@[expose] def NCoreStepLarge : Prop :=
  ∀ (G : Type) [Group G] (D : Set G), Hyp G D → RootIH G → (∃ d ∈ D, ∃ e ∈ rootSet D d, e ≠ d) →
    RootClosure D → NCoreCommutatorInRoot D

private theorem commutator_eq_sq_of_mem (hD : IsRootInvolutionSet D) {s t : G} (hs : s ∈ D)
    (ht : t ∈ D) : s * t * s⁻¹ * t⁻¹ = (s * t) ^ 2 := by
  rw [hD.inv_eq hs, hD.inv_eq ht, sq, ← mul_assoc]

theorem commLambda_of_nCoreCommutatorInRoot [Finite G]
    (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g}) (hD : IsRootInvolutionSet D)
    (hR : NCoreCommutatorInRoot D) : Moufang.CommLambda D := by
  intro y hy x₁ hx₁ x₂ hx₂ hyx₁ hyx₁D hyx₂ hyx₂D h4
  have hmem : ∀ x ∈ D, Commute y x → y * x ∈ D → x ∈ nCore D y := fun x hx hyx hyxD =>
    mem_nCore_of_collinear hclass hD hy hx hyx.symm (by rwa [← hyx.eq])
  have hc := hR y hy x₁ (hmem x₁ hx₁ hyx₁ hyx₁D) x₂ (hmem x₂ hx₂ hyx₂ hyx₂D)
  rw [commutator_eq_sq_of_mem hD hx₁ hx₂] at hc
  exact mem_rootSet_of_mem_rootGroup hclass hy (hD.sq_mem hx₁ hx₂ h4) hc

theorem excCollinearComm_of_nCoreCommutatorInRoot [Finite G]
    (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g}) (hD : IsRootInvolutionSet D)
    (hsing : ∀ x ∈ D, rootSet D x = {x}) (hNL : Moufang.NoLevi D)
    (hR : NCoreCommutatorInRoot D) : Moufang.ExcCollinearComm D := by
  intro y hy x₁ hx₁ x₂ hx₂ hyx₁ _ hyx₂ h4
  have hmem : ∀ x ∈ D, Commute y x → x ∈ nCore D y := fun x hx hyx =>
    mem_nCore_of_mem_twoCore hx (hNL.mem_twoCore hclass hD hy hx hyx.symm)
  have hc := hR y hy x₁ (hmem x₁ hx₁ hyx₁) x₂ (hmem x₂ hx₂ hyx₂)
  rw [commutator_eq_sq_of_mem hD hx₁ hx₂] at hc
  have hroot := mem_rootSet_of_mem_rootGroup hclass hy (hD.sq_mem hx₁ hx₂ h4) hc
  rwa [hsing y hy] at hroot

theorem nCoreCommutatorInRoot_of_oppositeDetermines [Finite G]
    (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g}) (hD : IsRootInvolutionSet D)
    (hsing : ∀ x ∈ D, rootSet D x = {x}) (hOD : OppositeDetermines D) :
    NCoreCommutatorInRoot D := fun y hy _ hg _ hh =>
  Subgroup.zpowers_le.2 (rootSet_subset_rootGroup D y (mem_rootSet_self hy))
    (commutator_mem_zpowers_of_mem_nCore hclass hD hsing hOD hy hg hh)

theorem nCoreStep_of_oppositeDetermines (hOD : OppositeDeterminesStep) (hL : NCoreStepLarge) :
    NCoreStep := by
  intro G _ D hH IH hRC
  by_cases hl : ∃ d ∈ D, ∃ e ∈ rootSet D d, e ≠ d
  · exact hL G D hH IH hl hRC
  · have := hH.finite
    refine nCoreCommutatorInRoot_of_oppositeDetermines hH.isClass hH.root (fun x hx => ?_)
      (hOD G D hH IH)
    refine Set.eq_singleton_iff_unique_mem.2 ⟨mem_rootSet_self hx, fun e he => ?_⟩
    by_contra hne
    exact hl ⟨x, hx, e, he, hne⟩

theorem commLambdaStep_of_nCore (h : NCoreStep) : CommLambdaStep := by
  intro G _ D hH IH _ hRC _
  have := hH.finite
  exact commLambda_of_nCoreCommutatorInRoot hH.isClass hH.root (h G D hH IH hRC)

theorem excCollinearCommInput_of_oppositeDeterminesStep (h : OppositeDeterminesStep) :
    Moufang.ExcCollinearCommInput := by
  intro G _ D hH IH hsing _ hNL
  have := hH.finite
  exact excCollinearComm_of_nCoreCommutatorInRoot hH.isClass hH.root hsing hNL
    (nCoreCommutatorInRoot_of_oppositeDetermines hH.isClass hH.root hsing (h G D hH IH))

theorem exceptionalNoLeviPlaneStep_of_oppositeDeterminesStep (h : OppositeDeterminesStep) :
    Moufang.ExceptionalNoLeviPlaneStep :=
  Moufang.exceptionalNoLeviPlaneStep_of_collinearComm
    (excCollinearCommInput_of_oppositeDeterminesStep h)

theorem commLambda_of_oppositeDetermines (h : Hyp G D) (hsing : ∀ x ∈ D, rootSet D x = {x})
    (hOD : OppositeDetermines D) : Moufang.CommLambda D :=
  have := h.finite
  commLambda_of_nCoreCommutatorInRoot h.isClass h.root
    (nCoreCommutatorInRoot_of_oppositeDetermines h.isClass h.root hsing hOD)

theorem excPQ_of_oppositeDetermines [Finite G] (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hD : IsRootInvolutionSet D) (hsing : ∀ x ∈ D, rootSet D x = {x})
    (hOD : OppositeDetermines D) : Moufang.ExcPQ D := by
  intro d hd p hp hdp hne hpol hpQ
  rcases eq_or_collinear_of_mem_nCore hclass hD hsing hOD hd hp
      (mem_nCore_of_mem_twoCore hp hpQ) with h | ⟨-, hpdD⟩
  · exact hne h
  · exact hpol (by rwa [hdp.eq])

theorem caseICommPQInput_of_oppositeDetermines (h : OppositeDeterminesStep) :
    Moufang.CaseICommPQInput := by
  intro G _ D hH IH hsing _ _
  have := hH.finite
  exact ⟨commLambda_of_oppositeDetermines hH hsing (h G D hH IH),
    excPQ_of_oppositeDetermines hH.isClass hH.root hsing (h G D hH IH)⟩

end CFSG.Timmesfeld.Bridge
