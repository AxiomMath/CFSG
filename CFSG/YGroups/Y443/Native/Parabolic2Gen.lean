module

public import CFSG.Monster.AxisCount.HSCount
public import CFSG.YGroups.Y443.Native.AlignConj

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.YGroups.Y443

open CFSG.Monster CFSG.Monster.AxisCount CFSG.Monster.Griess CFSG.Monster.Generated
  CFSG.Monster.B CFSG.Monster.B.Short CFSG.Open CFSG.YGroups.Y443Native

theorem mem_shortClass_of_conj {W c : SpaceB ≃ₗ[ℚ] SpaceB} (hW : W ∈ Gmat)
    (h : W * c * W⁻¹ = tStar) : c ∈ shortClass :=
  ⟨W⁻¹, inv_mem hW, by rw [← h]; group⟩

theorem eq_conj_of_conj {W c t : SpaceB ≃ₗ[ℚ] SpaceB} (h : W * c * W⁻¹ = t) :
    c = W⁻¹ * t * W := by
  rw [← h]
  group

theorem commute_iff_conj {W c x : SpaceB ≃ₗ[ℚ] SpaceB} (h : W * c * W⁻¹ = tStar) :
    x * c = c * x ↔ (W * x * W⁻¹) * tStar = tStar * (W * x * W⁻¹) := by
  rw [← h]
  constructor
  · intro h'
    calc W * x * W⁻¹ * (W * c * W⁻¹) = W * (x * c) * W⁻¹ := by group
      _ = W * (c * x) * W⁻¹ := by rw [h']
      _ = W * c * W⁻¹ * (W * x * W⁻¹) := by group
  · intro h'
    have h2 : W * (x * c) * W⁻¹ = W * (c * x) * W⁻¹ :=
      calc W * (x * c) * W⁻¹ = W * x * W⁻¹ * (W * c * W⁻¹) := by group
        _ = W * c * W⁻¹ * (W * x * W⁻¹) := h'
        _ = W * (c * x) * W⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel h2)

theorem centralizer_eq_conj_Cgen
    {W c : SpaceB ≃ₗ[ℚ] SpaceB} (hW : W ∈ Gmat)
    (h : W * c * W⁻¹ = tStar) :
    Gmat ⊓ Subgroup.centralizer {c} = Cgen.map (MulAut.conj W⁻¹).toMonoidHom := by
  ext x
  rw [Subgroup.mem_map]
  constructor
  · intro hx
    obtain ⟨hxG, hxc⟩ := Subgroup.mem_inf.1 hx
    have hc := (commute_iff_conj h).1 (Subgroup.mem_centralizer_singleton_iff.1 hxc)
    have hy : W * x * W⁻¹ ∈ Cgen := by
      rw [← HS.centralizer_tStar_eq_Cgen]
      exact Subgroup.mem_inf.2
        ⟨mul_mem (mul_mem hW hxG) (inv_mem hW), Subgroup.mem_centralizer_singleton_iff.2 hc⟩
    refine ⟨_, hy, ?_⟩
    simp [mul_assoc]
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨hyG, hyc⟩ := Subgroup.mem_inf.1 (Cgen_le hy)
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact mul_mem (mul_mem (inv_mem hW) hyG) (by simpa using hW)
    · rw [Subgroup.mem_centralizer_singleton_iff, commute_iff_conj h]
      have hyc' := Subgroup.mem_centralizer_singleton_iff.1 hyc
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      simpa [mul_assoc] using hyc'

theorem conj_mem_Cgen_of_comm
    {W c x : SpaceB ≃ₗ[ℚ] SpaceB} (hW : W ∈ Gmat)
    (h : W * c * W⁻¹ = tStar) (hx : x ∈ Gmat) (hxc : x * c = c * x) :
    W * x * W⁻¹ ∈ Cgen := by
  rw [← HS.centralizer_tStar_eq_Cgen]
  exact Subgroup.mem_inf.2 ⟨mul_mem (mul_mem hW hx) (inv_mem hW),
    Subgroup.mem_centralizer_singleton_iff.2 ((commute_iff_conj h).1 hxc)⟩


theorem evalGL_slet_eq :
    evalGL slet = ((fM y443C : Gmat) : SpaceB ≃ₗ[ℚ] SpaceB) := by
  rw [fM_y443C_eq, wcWord, wordLin_wcWordOf slet slet_le]

theorem omega_conj_slet :
    wordLin omegaWord * evalGL slet * (wordLin omegaWord)⁻¹ = tStar := by
  rw [evalGL_slet_eq]
  exact omega_conj

theorem evalGL_slet_eq_conj :
    evalGL slet = (wordLin omegaWord)⁻¹ * tStar * wordLin omegaWord :=
  eq_conj_of_conj omega_conj_slet

end CFSG.YGroups.Y443
