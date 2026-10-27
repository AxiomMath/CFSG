module

public import CFSG.Quasithin.Background.G118CanonNineF2
public import CFSG.Quasithin.Background.G118CanonNineF2TensorBuild
public import CFSG.Quasithin.Background.G118CanonNineF2TensorMod

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin

namespace G11

namespace Canon

open scoped TensorProduct

open F2Tensor

theorem f2TensorGap_holds : F2TensorGap := by
  intro V _ _ _ H I hHI D C Dg e φ σ hdim hU hF hCH hDC hDN hσ hIA5
  obtain ⟨ιI, hιI⟩ := exists_intertwines G118.autA5Input hIA5 φ
  have hIrrI : IrrPlus H I := irrPlus_of_intertwines D hU hdim hHI hιI
  set c₀ : GLV V := ((e.symm rho3 : ↥C) : GLV V)
  set y₀ : GLV V := ((e.symm tau3 : ↥C) : GLV V)
  have hy₀C : y₀ ∈ C := (e.symm tau3).2
  have hc₀H : ∀ h ∈ H, h * c₀ = c₀ * h := fun h hh => hCH c₀ (e.symm rho3).2 h hh
  have hy₀H : ∀ h ∈ H, h * y₀ = y₀ * h := fun h hh => hCH y₀ hy₀C h hh
  have hc₀3' : c₀ * c₀ * c₀ = 1 := by
    have h : e.symm rho3 * e.symm rho3 * e.symm rho3 = 1 := by
      rw [← map_mul, ← map_mul, ← pow_three', rho3_pow_three, map_one]
    simpa using congrArg (fun z : ↥C => (z : GLV V)) h
  have hc₀3 : c₀ ^ 3 = 1 := by rw [pow_three']; exact hc₀3'
  have hc₀1 : c₀ ≠ 1 := by
    intro h
    apply rho3_ne_one
    have h1 : e.symm rho3 = 1 := Subtype.ext h
    simpa using congrArg e h1
  have hy₀2 : y₀ * y₀ = 1 := by
    have h : e.symm tau3 * e.symm tau3 = 1 := by rw [← map_mul, tau3_mul_self, map_one]
    simpa using congrArg (fun z : ↥C => (z : GLV V)) h
  have hy₀c₀ : y₀ * c₀ = c₀⁻¹ * y₀ := by
    have h : e.symm tau3 * e.symm rho3 = (e.symm rho3)⁻¹ * e.symm tau3 := by
      rw [← map_mul, ← map_inv, ← map_mul, tau3_rho3]
    simpa using congrArg (fun z : ↥C => (z : GLV V)) h
  obtain ⟨B, hB, hyB⟩ := exists_fixed_point_involution D hU hy₀H hy₀2
  have hBint : ∃ ι : ↥B ≃ₗ[ZMod 2] ↥(permCore 5), Intertwines H φ B ι := by
    rcases orbit_cases D hU hF hc₀H hc₀3 hc₀1 hIrrI hB with h | h | h
    · rw [h]
      exact ⟨ιI, hιI⟩
    · rw [h]
      exact exists_intertwines_conj ⟨ιI, hιI⟩ hc₀H
    · rw [h]
      exact exists_intertwines_conj (exists_intertwines_conj ⟨ιI, hιI⟩ hc₀H) hc₀H
  obtain ⟨ι, hι⟩ := hBint
  have hB4 : Module.finrank (ZMod 2) B = 4 := by
    rw [ι.finrank_eq, finrank_permCore_five]
  have hBinv : Invariant H B := hB.1
  have hne : conjSub c₀ B ≠ B := conjSub_ne D hU hF hc₀H hc₀3 hc₀1 hB
  obtain ⟨hinf, hsup⟩ := inf_sup_conj D hU hdim hB4 hc₀H hne hBinv
  have hcc : ∀ v, c₀ (c₀ v) = c₀ v + v :=
    sq_eq_add_of_cube c₀ hc₀3 (fixed_eq_zero D hU hF hc₀H hc₀3 hc₀1)
  have hyBpt : ∀ b ∈ B, y₀ b = b := by
    refine IsA5Module.fixes_of_commute ⟨φ, ι, hι⟩ hBinv ?_ ?_
    · intro v hv
      have h1 : y₀ v ∈ conjSub y₀ B := apply_mem_conjSub hv
      rwa [hyB] at h1
    · intro l hl v _
      exact (congrArg (fun g : GLV V => g v) (hy₀H l hl)).symm
  have hc₀inv : c₀⁻¹ = c₀ * c₀ :=
    inv_eq_of_mul_eq_one_right (by rw [← mul_assoc]; exact hc₀3')
  have hyc : ∀ b ∈ B, y₀ (c₀ b) = c₀ (c₀ b) := by
    intro b hb
    have h1 : y₀ (c₀ b) = c₀⁻¹ (y₀ b) := congrArg (fun g : GLV V => g b) hy₀c₀
    rw [h1, hyBpt b hb, hc₀inv]
    rfl
  have hker : ∀ v : V, y₀ v = v → v ∈ B := by
    intro v hv
    have hv' : v ∈ B ⊔ conjSub c₀ B := hsup ▸ Submodule.mem_top
    obtain ⟨b, hb, z, hz, rfl⟩ := Submodule.mem_sup.1 hv'
    obtain ⟨b', hb', rfl⟩ := hz
    have h1 : y₀ (b + c₀ b') = b + (c₀ b' + b') := by
      rw [map_add, hyBpt b hb, hyc b' hb', hcc]
    have hv2 : y₀ (b + c₀ b') = b + c₀ b' := hv
    rw [h1] at hv2
    have h2 : b' = 0 := by
      have h3 : (b + c₀ b') + b' = b + c₀ b' := by rw [add_assoc]; exact hv2
      simpa using h3
    have h4 : b + (c₀ : V →ₗ[ZMod 2] V) b' = b := by
      show b + c₀ b' = b
      rw [h2, map_zero, add_zero]
    show b + (c₀ : V →ₗ[ZMod 2] V) b' ∈ B
    rw [h4]
    exact hb
  let β : ↥(permCore 5) →ₗ[ZMod 2] V := B.subtype ∘ₗ ι.symm.toLinearMap
  have hβ : ∀ a, β a = ((ι.symm a : ↥B) : V) := fun a => rfl
  have hβinj : Function.Injective β := Subtype.val_injective.comp ι.symm.injective
  have hβrange : LinearMap.range β = B := by
    ext v
    constructor
    · rintro ⟨a, rfl⟩
      exact (ι.symm a).2
    · intro hv
      exact ⟨ι ⟨v, hv⟩, by rw [hβ, LinearEquiv.symm_apply_apply]⟩
  have hβ0 : ∀ a, y₀ (β a) = β a := fun a => hyBpt _ (ι.symm a).2
  have hβ1 : ∀ a, y₀ (c₀ (β a)) = c₀ (c₀ (β a)) := fun a => hyc _ (ι.symm a).2
  have hβcc : ∀ a, c₀ (c₀ (β a)) = c₀ (β a) + β a := fun a => hcc _
  have hbij := tensorMap_bijective β c₀ B hβinj hβrange hinf hsup
  have hP : ∀ π : Equiv.Perm (Fin 3), ∀ (x : ↥(permCore 3)) (a : ↥(permCore 5)),
      tensorMap β c₀ (permActCore 3 π x ⊗ₜ a) =
        ((e.symm π : ↥C) : GLV V) (tensorMap β c₀ (x ⊗ₜ a)) := by
    have hmul : ∀ π₁ π₂ : Equiv.Perm (Fin 3),
        (∀ (x : ↥(permCore 3)) (a : ↥(permCore 5)), tensorMap β c₀ (permActCore 3 π₁ x ⊗ₜ a) =
          ((e.symm π₁ : ↥C) : GLV V) (tensorMap β c₀ (x ⊗ₜ a))) →
        (∀ (x : ↥(permCore 3)) (a : ↥(permCore 5)), tensorMap β c₀ (permActCore 3 π₂ x ⊗ₜ a) =
          ((e.symm π₂ : ↥C) : GLV V) (tensorMap β c₀ (x ⊗ₜ a))) →
        (∀ (x : ↥(permCore 3)) (a : ↥(permCore 5)),
          tensorMap β c₀ (permActCore 3 (π₁ * π₂) x ⊗ₜ a) =
          ((e.symm (π₁ * π₂) : ↥C) : GLV V) (tensorMap β c₀ (x ⊗ₜ a))) := by
      intro π₁ π₂ h₁ h₂ x a
      rw [permActCore_mul, h₁, h₂, map_mul]
      rfl
    have h1 : ∀ (x : ↥(permCore 3)) (a : ↥(permCore 5)),
        tensorMap β c₀ (permActCore 3 1 x ⊗ₜ a) =
          ((e.symm 1 : ↥C) : GLV V) (tensorMap β c₀ (x ⊗ₜ a)) := by
      intro x a
      rw [permActCore_one, map_one]
      rfl
    have hρ : ∀ (x : ↥(permCore 3)) (a : ↥(permCore 5)),
        tensorMap β c₀ (permActCore 3 rho3 x ⊗ₜ a) =
          ((e.symm rho3 : ↥C) : GLV V) (tensorMap β c₀ (x ⊗ₜ a)) :=
      fun x a => tensorMap_rho β c₀ hβcc x a
    have hτ : ∀ (x : ↥(permCore 3)) (a : ↥(permCore 5)),
        tensorMap β c₀ (permActCore 3 tau3 x ⊗ₜ a) =
          ((e.symm tau3 : ↥C) : GLV V) (tensorMap β c₀ (x ⊗ₜ a)) :=
      fun x a => tensorMap_tau β c₀ y₀ hβ0 hβ1 hβcc x a
    intro π
    rcases perm3_cases π with rfl | rfl | rfl | rfl | rfl | rfl
    · exact h1
    · exact hρ
    · exact hmul _ _ hρ hρ
    · exact hτ
    · exact hmul _ _ hτ hρ
    · exact hmul _ _ (hmul _ _ hτ hρ) hρ
  have hdBmem : ∀ d ∈ Dg, ∀ b ∈ B, d b ∈ B := by
    intro d hd b hb
    apply hker
    have h1 : y₀ * d = d * y₀ := hDC d hd y₀ hy₀C
    have h2 : y₀ (d b) = d (y₀ b) := congrArg (fun g : GLV V => g b) h1
    rw [h2, hyBpt b hb]
  refine ⟨(LinearEquiv.ofBijective (tensorMap β c₀) hbij).symm, ?_, ?_⟩
  · intro c x a
    rw [LinearEquiv.symm_symm, LinearEquiv.symm_apply_eq]
    have h := hP (e c) x a
    rw [MulEquiv.symm_apply_apply] at h
    exact h.symm
  · intro d x a
    rw [LinearEquiv.symm_symm, LinearEquiv.symm_apply_eq]
    have hdc : ∀ v, (d : GLV V) (c₀ v) = c₀ ((d : GLV V) v) := fun v =>
      congrArg (fun g : GLV V => g v) (hDC d d.2 c₀ (e.symm rho3).2).symm
    have hdβ : (d : GLV V) (β a) = β (permActCore 5 (σ d) a) := by
      have h := dcompat hι hBinv (hdBmem d d.2) (hDN d d.2) (σ d)
        (fun h g hg => hσ d h g hg) (ι.symm a)
      rw [LinearEquiv.apply_symm_apply] at h
      have h2 : ι ⟨(d : GLV V) ((ι.symm a : ↥B) : V), hdBmem d d.2 _ (ι.symm a).2⟩ =
          permActCore 5 (σ d) a := Subtype.ext h
      have h3 : (⟨(d : GLV V) ((ι.symm a : ↥B) : V), hdBmem d d.2 _ (ι.symm a).2⟩ : ↥B) =
          ι.symm (permActCore 5 (σ d) a) := by
        rw [← h2, LinearEquiv.symm_apply_apply]
      exact congrArg Subtype.val h3
    exact tensorMap_comm β c₀ (d : GLV V) hdc a (permActCore 5 (σ d) a) hdβ x

theorem g118NineInputF2_holds' : G118NineInputF2 :=
  g118NineInputF2_of_gap f2TensorGap_holds

end Canon

end G11

end CFSG.Quasithin
