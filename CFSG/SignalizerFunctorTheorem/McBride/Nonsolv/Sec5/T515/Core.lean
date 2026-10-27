module

public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec5.L514.Setup

public section

open CFSG.Open
open CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.L514

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.T515ab

variable {Γ : Type*} [Group Γ]

theorem not_isSolvable_of_not_isMulCommutative {H : Type*} [Group H] [IsSimpleGroup H]
    (hnc : ¬ IsMulCommutative H) : ¬ Group.IsSolvable H := fun hs =>
  hnc (isMulCommutative_iff.mpr (IsSimpleGroup.comm_iff_isSolvable.mpr hs))

theorem isSolvable_of_le {K H : Subgroup Γ} (hKH : K ≤ H) (hH : Group.IsSolvable H) :
    Group.IsSolvable K :=
  Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hKH)
    (Subgroup.inclusion_injective hKH)

theorem orbitClosure_map_conj {A J : Subgroup Γ} {a : Γ} (ha : a ∈ A) :
    orbitClosure (J.map (MulAut.conj a).toMonoidHom) A = orbitClosure J A := by
  refine le_antisymm (orbitClosure_le fun b hb => ?_) (orbitClosure_le fun b hb => ?_)
  · rw [map_conj_map_conj]
    exact map_conj_le_orbitClosure J (mul_mem hb ha)
  · have h := map_conj_le_orbitClosure (J.map (MulAut.conj a).toMonoidHom)
      (mul_mem hb (inv_mem ha))
    rwa [map_conj_map_conj, show b * a⁻¹ * a = b by group] at h

theorem map_conj_mem_lcalA {A G J : Subgroup Γ} (hAG : A ≤ Subgroup.normalizer (G : Set Γ))
    (hJ : J ∈ lcalA G A) {a : Γ} (ha : a ∈ A) :
    J.map (MulAut.conj a).toMonoidHom ∈ lcalA G A := by
  refine ⟨map_conj_mem_lcal hJ.1 (hAG ha), ?_⟩
  have : smear (J.map (MulAut.conj a).toMonoidHom) A = smear J A := by
    unfold smear
    rw [orbitClosure_map_conj ha]
  rw [this]
  exact hJ.2

theorem orbitClosure_le_kUp {A G J : Subgroup Γ} (hAG : A ≤ Subgroup.normalizer (G : Set Γ))
    (hsol : sol G = ⊥) (hJ : J ∈ lcalA G A) : orbitClosure J A ≤ kUp G A := by
  refine orbitClosure_le fun a ha => ?_
  have h := map_conj_mem_lcalA hAG hJ ha
  refine le_iSup₂_of_le (J.map (MulAut.conj a).toMonoidHom) ?_ le_rfl
  exact ⟨(mcal_eq_lcal_of_sol_eq_bot hsol).symm ▸ h.1, h.2⟩

theorem mul_comm_of_mem_kDown {A G : Subgroup Γ} (hsol : sol G = ⊥) {g : Γ}
    (hg : g ∈ kDown G A) {k : Γ} (hk : k ∈ kUp G A) : g * k = k * g := by
  have h := (mem_kDown_iff.mp hg).2 k hk
  rw [hsol, Subgroup.mem_bot] at h
  exact commutatorElement_eq_one_iff_mul_comm.mp h

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.T515ab
