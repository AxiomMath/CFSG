module

public import CFSG.LocalAnalysis.ComponentClassification.J2CoverKernelCentralizers

public section

namespace CFSG.RankThree.PartTwo.KFacts

open CFSG.ComponentClassification.J2Cover CFSG.Sporadic.Schreier
open CFSG.ComponentClassification.M12Cover (centralizerInConjEquiv)

theorem ks152J2InvolNine :
    ∀ (Γ : Type) [Group Γ] [Finite Γ], Nonempty (Γ ≃* CFSG.Blueprint.NativeSporadic.J2) →
      ∀ E : Subgroup Γ, Nat.card E = 9 → ∀ σ : MulAut Γ, σ ^ 2 = 1 →
        (∀ e ∈ E, σ e = e) → σ = 1 := by
  intro Γ _ _ ⟨e⟩ E hE σ hσ hfix
  obtain ⟨-, -, hcl, -, -, hA, -, -, -, hT, -, hU, -⟩ :=
    ctss_j2_automorphism_involution_centralizers_exclude_small_normal_four_groups
  set φ : Γ ≃* ↥P := e.trans nativeEquivP with hφ
  set α : MulAut ↥P := (φ.symm.trans σ).trans φ with hα
  have hαapply : ∀ x : ↥P, α x = φ (σ (φ.symm x)) := fun x => rfl
  have hσσ : ∀ g : Γ, σ (σ g) = g := by
    intro g
    have := congrArg (fun τ : MulAut Γ => τ g) hσ
    simpa [pow_two] using this
  have hαα : α * α = 1 := by
    ext x
    rw [MulAut.mul_apply, hαapply, hαapply, MulEquiv.symm_apply_apply, hσσ,
      MulEquiv.apply_symm_apply, MulAut.one_apply]
  set r : ↥R := rAutEquiv.symm α with hr
  have hrα : rConj r = α := (rAutEquiv_apply r).symm.trans (rAutEquiv.apply_symm_apply α)
  have hr2 : r * r = 1 := by
    apply rConj_injective
    rw [map_mul, hrα, hαα, map_one]
  by_contra hne
  have hr1 : (r : Equiv.Perm (Fin 315)) ≠ 1 := by
    intro h1
    apply hne
    have hr1' : r = 1 := Subtype.ext h1
    have hα1 : α = 1 := by rw [← hrα, hr1', map_one]
    ext g
    have h2 := congrArg (fun τ : MulAut ↥P => τ (φ g)) hα1
    simp only [MulAut.one_apply] at h2
    rw [hαapply, MulEquiv.symm_apply_apply] at h2
    exact φ.injective h2
  have hord : orderOf (r : Equiv.Perm (Fin 315)) = 2 := by
    refine orderOf_eq_prime ?_ hr1
    rw [pow_two]
    exact congrArg Subtype.val hr2
  set ι : Γ →* Equiv.Perm (Fin 315) := P.subtype.comp φ.toMonoidHom with hι
  have hιinj : Function.Injective ι := P.subtype_injective.comp φ.injective
  set EP : Subgroup (Equiv.Perm (Fin 315)) := E.map ι with hEP
  have hEcard : Nat.card EP = 9 := by
    rw [hEP, Subgroup.card_map_of_injective hιinj]
    exact hE
  have hle : EP ≤ centralizerIn R (r : Equiv.Perm (Fin 315)) := by
    rintro _ ⟨g, hg, rfl⟩
    rw [mem_centralizerIn]
    refine ⟨P_le_R (φ g).2, ?_⟩
    have h1 : α (φ g) = φ g := by
      rw [hαapply, MulEquiv.symm_apply_apply, hfix g hg]
    have h2 : ((rConj r (φ g) : ↥P) : Equiv.Perm (Fin 315)) = (φ g : Equiv.Perm (Fin 315)) := by
      rw [hrα, h1]
    rw [rConj_apply] at h2
    change (φ g : Equiv.Perm (Fin 315)) * (r : Equiv.Perm (Fin 315)) =
      (r : Equiv.Perm (Fin 315)) * (φ g : Equiv.Perm (Fin 315))
    calc (φ g : Equiv.Perm (Fin 315)) * (r : Equiv.Perm (Fin 315))
        = (r : Equiv.Perm (Fin 315)) * (φ g : Equiv.Perm (Fin 315)) *
            (r : Equiv.Perm (Fin 315))⁻¹ * (r : Equiv.Perm (Fin 315)) := by rw [h2]
      _ = (r : Equiv.Perm (Fin 315)) * (φ g : Equiv.Perm (Fin 315)) := by group
  have h9 : 9 ∣ Nat.card (centralizerIn R (r : Equiv.Perm (Fin 315))) := by
    rw [← hEcard]
    exact Subgroup.card_dvd_of_le hle
  obtain ⟨ρ, hρ, c, hc, hrc⟩ := hcl (r : Equiv.Perm (Fin 315)) r.2 hord
  have hcard : Nat.card (centralizerIn R (r : Equiv.Perm (Fin 315))) =
      Nat.card (centralizerIn R ρ) := by
    rw [hrc]
    exact (Nat.card_congr (centralizerInConjEquiv R (P_le_R hc) ρ).toEquiv).symm
  rw [hcard] at h9
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hρ
  rcases hρ with rfl | rfl | rfl
  · rw [hA] at h9
    omega
  · rw [hT] at h9
    omega
  · rw [hU] at h9
    omega

end CFSG.RankThree.PartTwo.KFacts
