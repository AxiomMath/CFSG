module

public import CFSG.Quasithin.Background.RonanH15L34
public import CFSG.Quasithin.Background.RonanH15Trans

public section

namespace CFSG.Quasithin.RonanH15

open CFSG.Quasithin CFSG.Quasithin.H.Mathieu
open CFSG.Monster.Code (AutPerm)
open scoped MatrixGroups

private theorem map_conj_eq_of_iff' (τ : Equiv.Perm (Fin 24)) (hτ : τ ∈ AutPerm)
    (H T : Subgroup (Equiv.Perm (Fin 24))) (P Q : Equiv.Perm (Fin 24) → Prop)
    (hT : ∀ x, x ∈ T ↔ x ∈ AutPerm ∧ P x)
    (hH : ∀ h, h ∈ H ↔ h ∈ AutPerm ∧ Q h)
    (hPQ : ∀ h, P (τ * h * τ⁻¹) ↔ Q h) :
    H.map (MulAut.conj τ).toMonoidHom = T := by
  ext x
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨h, hh, rfl⟩
    have hhh := (hH h).1 hh
    rw [hT]
    refine ⟨?_, (hPQ h).2 hhh.2⟩
    exact AutPerm.mul_mem (AutPerm.mul_mem hτ hhh.1) (AutPerm.inv_mem hτ)
  · intro hx
    rw [hT] at hx
    have hconj : (MulAut.conj τ).toMonoidHom (τ⁻¹ * x * τ) = x := by
      show τ * (τ⁻¹ * x * τ) * τ⁻¹ = x
      group
    refine ⟨τ⁻¹ * x * τ, (hH _).2 ⟨?_, (hPQ _).1 ?_⟩, hconj⟩
    · exact AutPerm.mul_mem (AutPerm.mul_mem (AutPerm.inv_mem hτ) hx.1) hτ
    · rw [show τ * (τ⁻¹ * x * τ) * τ⁻¹ = x by group]
      exact hx.2

theorem nonempty_stab3_equiv_mog21 {a b j : Fin 24} (hab : a ≠ b)
    (hja : j ≠ a) (hjb : j ≠ b) :
    Nonempty (↥(AutPerm ⊓ stab a ⊓ stab b ⊓ stab j) ≃* ↥mog21) := by
  obtain ⟨τ, hτ, h0, h1, h2⟩ := exists_maps_three hab hja hjb
  have e0 : τ⁻¹ a = 0 := by rw [← h0, Equiv.Perm.inv_def, Equiv.symm_apply_apply]
  have e1 : τ⁻¹ b = 1 := by rw [← h1, Equiv.Perm.inv_def, Equiv.symm_apply_apply]
  have e2 : τ⁻¹ j = 2 := by rw [← h2, Equiv.Perm.inv_def, Equiv.symm_apply_apply]
  have hmap : mog21.map (MulAut.conj τ).toMonoidHom = AutPerm ⊓ stab a ⊓ stab b ⊓ stab j := by
    refine map_conj_eq_of_iff' τ hτ mog21 (AutPerm ⊓ stab a ⊓ stab b ⊓ stab j)
      (fun x => x a = a ∧ x b = b ∧ x j = j) (fun h => h 0 = 0 ∧ h 1 = 1 ∧ h 2 = 2)
      (fun x => ?_) (fun h => ?_) (fun h => ?_)
    · simp only [Subgroup.mem_inf, CFSG.Quasithin.H.Mathieu.mem_stab_iff, and_assoc]
    · simp only [mog21, mog22, Subgroup.mem_inf, CFSG.Quasithin.H.Mathieu.mem_stab_iff, and_assoc]
    · show (τ * h * τ⁻¹) a = a ∧ (τ * h * τ⁻¹) b = b ∧ (τ * h * τ⁻¹) j = j ↔
        h 0 = 0 ∧ h 1 = 1 ∧ h 2 = 2
      simp only [Equiv.Perm.mul_apply, e0, e1, e2]
      rw [← h0, ← h1, ← h2]
      simp only [EmbeddingLike.apply_eq_iff_eq]
  exact ⟨(MulEquiv.subgroupCongr hmap).symm.trans (MulEquiv.subgroupMap (MulAut.conj τ) mog21).symm⟩

theorem nonempty_stab3_equiv_PSL
    {a b j : Fin 24} (hab : a ≠ b) (hja : j ≠ a) (hjb : j ≠ b) :
    Nonempty (↥(AutPerm ⊓ stab a ⊓ stab b ⊓ stab j) ≃*
      PSL(3, CFSG.ComponentClassification.PSL3Four.F4)) := by
  obtain ⟨e⟩ := nonempty_stab3_equiv_mog21 hab hja hjb
  obtain ⟨f⟩ := nonempty_mog21_equiv_PSL
  exact ⟨e.trans f⟩

end CFSG.Quasithin.RonanH15
