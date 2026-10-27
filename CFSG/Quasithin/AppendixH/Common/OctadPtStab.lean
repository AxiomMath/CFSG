module

public import CFSG.Quasithin.AppendixH.Common.OctadBasic

public section

open scoped Pointwise

namespace CFSG.ASVolI.AppH

open CFSG.ASVolI.ChH CFSG.Monster.Code

@[expose] def octFix (O : Finset (Fin 24)) : Subgroup S24 where
  carrier := {g | g ∈ M24g ∧ ∀ i ∈ O, g i = i}
  mul_mem' := fun {a b} ha hb => ⟨M24g.mul_mem ha.1 hb.1, fun i hi => by
    rw [Equiv.Perm.mul_apply, hb.2 i hi, ha.2 i hi]⟩
  one_mem' := ⟨M24g.one_mem, fun _ _ => rfl⟩
  inv_mem' := fun {g} hg => ⟨M24g.inv_mem hg.1, fun i hi => by
    rw [Equiv.Perm.inv_eq_iff_eq, hg.2 i hi]⟩

theorem mem_octFix_iff {O : Finset (Fin 24)} {g : S24} :
    g ∈ octFix O ↔ g ∈ M24g ∧ ∀ i ∈ O, g i = i := Iff.rfl

theorem octFix_le_octStab (O : Finset (Fin 24)) : octFix O ≤ octStab O := by
  intro g hg
  rw [mem_octStab_iff]
  obtain ⟨hgM, hgfix⟩ := mem_octFix_iff.1 hg
  refine ⟨hgM, ?_⟩
  ext x
  rw [smul_finset_eq_map, Finset.mem_map_equiv]
  constructor
  · intro hx
    have h1 : g (g.symm x) = g.symm x := hgfix (g.symm x) hx
    rw [Equiv.apply_symm_apply] at h1
    rwa [h1]
  · intro hx
    have h1 : g x = x := hgfix x hx
    have h2 : g.symm x = x := by
      simpa using (congrArg g.symm h1).symm
    rwa [h2]

theorem octFix_smul {σ : S24} (hσ : σ ∈ M24g) (O : Finset (Fin 24)) :
    octFix (σ • O) = (octFix O).map (MulAut.conj σ).toMonoidHom := by
  ext g
  rw [Subgroup.mem_map]
  constructor
  · intro hg
    obtain ⟨hgM, hgfix⟩ := mem_octFix_iff.1 hg
    refine ⟨σ⁻¹ * g * σ, ?_, ?_⟩
    · rw [mem_octFix_iff]
      refine ⟨M24g.mul_mem (M24g.mul_mem (M24g.inv_mem hσ) hgM) hσ, ?_⟩
      intro i hi
      have hσi : σ i ∈ σ • O := by
        rw [smul_finset_eq_map, Finset.mem_map_equiv]
        simpa using hi
      rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hgfix (σ i) hσi, Equiv.Perm.inv_def]
      exact Equiv.symm_apply_apply σ i
    · rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
  · rintro ⟨h, hh, hgh⟩
    obtain ⟨hhM, hhfix⟩ := mem_octFix_iff.1 hh
    rw [← hgh, mem_octFix_iff]
    refine ⟨?_, ?_⟩
    · rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact M24g.mul_mem (M24g.mul_mem hσ hhM) (M24g.inv_mem hσ)
    · intro i hi
      have hiO : σ.symm i ∈ O := by
        rw [smul_finset_eq_map, Finset.mem_map_equiv] at hi
        exact hi
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply,
        Equiv.Perm.inv_def, hhfix (σ.symm i) hiO]
      exact Equiv.apply_symm_apply σ i

theorem normal_octFix (O : Finset (Fin 24)) : ((octFix O).subgroupOf (octStab O)).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  obtain ⟨hgM, hgO⟩ := mem_octStab_iff.1 g.2
  obtain ⟨hnM, hnfix⟩ := mem_octFix_iff.1 hn
  rw [mem_octFix_iff]
  refine ⟨?_, ?_⟩
  · simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact M24g.mul_mem (M24g.mul_mem hgM hnM) (M24g.inv_mem hgM)
  · intro i hi
    have hginv : (g : S24).symm i ∈ O := by
      have hi' : i ∈ (g : S24) • O := by rw [hgO]; exact hi
      rw [smul_finset_eq_map, Finset.mem_map_equiv] at hi'
      exact hi'
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Equiv.Perm.mul_apply, Equiv.Perm.inv_def,
      hnfix ((g : S24).symm i) hginv]
    exact Equiv.apply_symm_apply (g : S24) i

end CFSG.ASVolI.AppH
