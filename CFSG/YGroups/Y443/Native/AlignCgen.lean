module

public import CFSG.YGroups.Y443.Native.AlignConj
public import CFSG.Monster.AxisCount.HSCount

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.YGroups.Y443

open CFSG.Monster CFSG.Monster.AxisCount CFSG.Monster.Griess CFSG.Monster.Generated
  CFSG.Monster.B CFSG.Monster.B.Short CFSG.Open

theorem centralizer_fMc_eq :
    Gmat ⊓ Subgroup.centralizer {((fM y443C : Gmat) : SpaceB ≃ₗ[ℚ] SpaceB)} =
      Cgen.map (MulAut.conj (wordLin omegaWord)⁻¹).toMonoidHom := by
  ext x
  rw [Subgroup.mem_map]
  constructor
  · intro hx
    obtain ⟨hxG, hxc⟩ := Subgroup.mem_inf.1 hx
    have hc := commute_fMc_iff.1 (Subgroup.mem_centralizer_singleton_iff.1 hxc)
    have hy : wordLin omegaWord * x * (wordLin omegaWord)⁻¹ ∈ Cgen := by
      rw [← HS.centralizer_tStar_eq_Cgen]
      exact Subgroup.mem_inf.2
        ⟨mul_mem (mul_mem (wordLin_mem_Gmat _) hxG) (inv_mem (wordLin_mem_Gmat _)),
          Subgroup.mem_centralizer_singleton_iff.2 hc⟩
    refine ⟨_, hy, ?_⟩
    simp [mul_assoc]
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨hyG, hyc⟩ := Subgroup.mem_inf.1 (Cgen_le hy)
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact mul_mem (mul_mem (inv_mem (wordLin_mem_Gmat _)) hyG)
        (by simpa using wordLin_mem_Gmat omegaWord)
    · rw [Subgroup.mem_centralizer_singleton_iff, commute_fMc_iff]
      have hyc' := Subgroup.mem_centralizer_singleton_iff.1 hyc
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      simpa [mul_assoc] using hyc'

theorem fM_y443C_ne_one :
    ((fM y443C : Gmat) : SpaceB ≃ₗ[ℚ] SpaceB) ≠ 1 := by
  intro h
  have h1 := omega_conj
  rw [h, mul_one, mul_inv_cancel] at h1
  exact tStar_ne_one h1.symm

theorem conj_fM_mem_Cgen
    {h : MonsterY443Derived} (hh : h ∈ y443H) :
    wordLin omegaWord * ((fM h : Gmat) : SpaceB ≃ₗ[ℚ] SpaceB) * (wordLin omegaWord)⁻¹ ∈ Cgen := by
  rw [← HS.centralizer_tStar_eq_Cgen]
  exact Subgroup.mem_inf.2 ⟨conj_fM_mem_Gmat h,
    Subgroup.mem_centralizer_singleton_iff.2 (conj_fM_commute_tStar hh)⟩

theorem Hbar_conj_le_Cgen :
    ((y443H.map fM).map Gmat.subtype).map (MulAut.conj (wordLin omegaWord)).toMonoidHom ≤ Cgen := by
  rintro _ ⟨_, ⟨x, ⟨h, hh, rfl⟩, rfl⟩, rfl⟩
  exact conj_fM_mem_Cgen hh

theorem fM_mem_centralizer_fMc
    {h : MonsterY443Derived} (hh : h ∈ y443H) :
    ((fM h : Gmat) : SpaceB ≃ₗ[ℚ] SpaceB) ∈
      Gmat ⊓ Subgroup.centralizer {((fM y443C : Gmat) : SpaceB ≃ₗ[ℚ] SpaceB)} := by
  refine Subgroup.mem_inf.2 ⟨(fM h).2, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
  have := congrArg (fun m => ((fM m : Gmat) : SpaceB ≃ₗ[ℚ] SpaceB)) (y443C_comm_H hh)
  simpa using this

theorem Hbar_map_le_conj_Cgen :
    (y443H.map fM).map Gmat.subtype ≤ Cgen.map (MulAut.conj (wordLin omegaWord)⁻¹).toMonoidHom := by
  rintro _ ⟨x, ⟨h, hh, rfl⟩, rfl⟩
  rw [← centralizer_fMc_eq]
  exact fM_mem_centralizer_fMc hh

theorem Hbar_le_conj_Cgen :
    y443H.map fM ≤
      (Cgen.map (MulAut.conj (wordLin omegaWord)⁻¹).toMonoidHom).subgroupOf Gmat := by
  rintro _ ⟨h, hh, rfl⟩
  rw [Subgroup.mem_subgroupOf, ← centralizer_fMc_eq]
  exact fM_mem_centralizer_fMc hh

end CFSG.YGroups.Y443
