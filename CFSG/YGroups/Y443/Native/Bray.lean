module

public import CFSG.YGroups.Y443.Native.BrayCheck
public import CFSG.YGroups.Y443.Native.AlignAlg
public import CFSG.Monster.B.Cbar.GenData

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.YGroups.Y443

open CFSG.Monster CFSG.Monster.AxisCount CFSG.Monster.Griess CFSG.Monster.Generated
  CFSG.Monster.B CFSG.Monster.B.Short CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Visible

theorem wordLin_xWord : wordLin xWord = xmat := by
  have h : Rep4371.pauliQ (true, 0, 0) = zQ := by
    unfold Rep4371.pauliQ zQ
    congr 1
    simp [Rep4371.toSC, SpinCoord.z, Rep4371.boolZ, Rep4371.toC_zero, Rep4371.toD_zero]
  show wordLin [Native.Gen.rho (true, 0, 0)] = xmat
  rw [wordLin_cons, wordLin_nil, one_mul, Native.Gen.toLin_rho, h]
  rfl

theorem wordLin_eWord : wordLin eWord = gL 4 := wordLin_Lw 4

theorem wordLin_kWord :
    wordLin kWord = wordLin omegaWord * gL 4 * (wordLin omegaWord)⁻¹ := by
  have h := bray_k_check
  rw [wordLin_append, wordLin_append, wordLin_eWord] at h
  exact eq_mul_inv_of_mul_eq h

theorem wordLin_gWord :
    wordLin gWord = wordLin kWord * xmat * wordLin kWord * xmat := by
  rw [bray_g_check]
  simp only [wordLin_append, wordLin_xWord, mul_assoc]

theorem bray_commute :
    wordLin gWord * xmat = xmat * wordLin gWord := by
  have h := bray_comm_check
  rw [wordLin_append, wordLin_append, wordLin_xWord] at h
  exact h

theorem bray_ne :
    wordLin gWord * tStar * (wordLin gWord)⁻¹ ≠ tStar ∧
      wordLin gWord * tStar * (wordLin gWord)⁻¹ ≠ xmat * tStar := by
  obtain ⟨h1, h2⟩ := bray_ne_check
  refine ⟨fun e => h1 ?_, fun e => h2 ?_⟩
  · have e' : wordLin gWord * tStar = tStar * wordLin gWord := by
      rw [mul_inv_eq_iff_eq_mul] at e
      exact e
    rw [wordLin_append, wordLin_append, wordLin_tWord, e']
  · have e' : wordLin gWord * tStar = xmat * tStar * wordLin gWord := by
      rw [mul_inv_eq_iff_eq_mul] at e
      exact e
    rw [wordLin_append, wordLin_append, wordLin_append, wordLin_tWord, wordLin_xWord, e', mul_assoc]

theorem bray_mem_of_e1
    {K' : Subgroup (SpaceB ≃ₗ[ℚ] SpaceB)}
    (hK : wordLin omegaWord * gL 4 * (wordLin omegaWord)⁻¹ ∈ K') (hC : Cgen ≤ K') :
    wordLin gWord ∈ K' := by
  rw [wordLin_gWord, wordLin_kWord]
  have hx : xmat ∈ K' := hC xmat_mem_Cgen
  exact K'.mul_mem (K'.mul_mem (K'.mul_mem hK hx) hK) hx

theorem bray_mem
    {K' : Subgroup (SpaceB ≃ₗ[ℚ] SpaceB)}
    (hK : ∀ s ≤ 11, wordLin omegaWord * gL s * (wordLin omegaWord)⁻¹ ∈ K') (hC : Cgen ≤ K') :
    wordLin gWord ∈ K' :=
  bray_mem_of_e1 (hK 4 (by norm_num)) hC

theorem bray_element
    {K' : Subgroup (SpaceB ≃ₗ[ℚ] SpaceB)}
    (hK : ∀ s ≤ 11, wordLin omegaWord * gL s * (wordLin omegaWord)⁻¹ ∈ K') (hC : Cgen ≤ K') :
    ∃ g ∈ K', g * xmat = xmat * g ∧ g * tStar * g⁻¹ ≠ tStar ∧ g * tStar * g⁻¹ ≠ xmat * tStar :=
  ⟨wordLin gWord, bray_mem hK hC, bray_commute, bray_ne.1, bray_ne.2⟩

theorem conj_gL_mem_image
    {s : ℕ} (hs : s ≤ 11) :
    wordLin omegaWord * gL s * (wordLin omegaWord)⁻¹ ∈
      (fM.range.map Gmat.subtype).map (MulAut.conj (wordLin omegaWord)).toMonoidHom :=
  ⟨gL s, ⟨fM (axL s), MonoidHom.mem_range.2 ⟨axL s, rfl⟩, fM_axL hs⟩, rfl⟩

theorem bray_element_image
    (hC : Cgen ≤ (fM.range.map Gmat.subtype).map (MulAut.conj (wordLin omegaWord)).toMonoidHom) :
    ∃ g ∈ (fM.range.map Gmat.subtype).map (MulAut.conj (wordLin omegaWord)).toMonoidHom,
      g * xmat = xmat * g ∧ g * tStar * g⁻¹ ≠ tStar ∧ g * tStar * g⁻¹ ≠ xmat * tStar :=
  bray_element (fun _ hs => conj_gL_mem_image hs) hC

end CFSG.YGroups.Y443
