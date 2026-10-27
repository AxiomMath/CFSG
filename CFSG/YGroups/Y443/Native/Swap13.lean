module

public import CFSG.YGroups.Y443.Native.Parabolic2Transfer
public import CFSG.YGroups.Y443.Native.Swap13A
public import CFSG.YGroups.Y443.Native.Swap13Word
import Certificates.Kernel.KDense.Y443
public meta import CFSG.YGroups.Y443.Native.Align
public meta import CFSG.YGroups.Y443.Native.Parabolic2Words
public meta import Certificates.Data.CFSGNative.MonsterAxis.Dense
public meta import Certificates.Data.CFSGNative.YGroups.Y443.MonsterWords
public meta import Certificates.Data.CFSGNative.YGroups.Y443.Witness
public meta import Certificates.Data.CFSGNative.YGroups.Y443.AlignWords
public import Certificates.Certificate6007
public import Certificates.Certificate10107
public import Certificates.Certificate10108
public import Certificates.Certificate10110
public import Certificates.Certificate10115
public import Certificates.Certificate10116
public import Certificates.Certificate10117
public import Certificates.Certificate10118
public import Certificates.Certificate10119
public import Certificates.Certificate10120
public import Certificates.Certificate10121
public import Certificates.Certificate10122
public import Certificates.Certificate10123
public import Certificates.Certificate10124
public import Certificates.Certificate10127
public import Certificates.Certificate16004
public import CFSG.YGroups.Y443.Native.AlignB
public import CFSG.YGroups.Y443.Native.AlignCgen
public import CFSG.YGroups.Y443.Native.AlignW
public import CFSG.YGroups.Y443.Native.Parabolic2CheckB
public import CFSG.YGroups.Y443.Native.Parabolic2CheckW

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.YGroups.Y443

open CFSG.Monster CFSG.Monster.AxisCount CFSG.Monster.Griess CFSG.Monster.Generated
  CFSG.Monster.B CFSG.Monster.B.Short CFSG.Open CFSG.YGroups.Y443Native

theorem swap13_comm_t :
    wordLin swap13Word * tStar = tStar * wordLin swap13Word := by
  have h := swap13_a.1
  rw [wordLin_append, wordLin_append, wordLin_tWord] at h
  exact h

theorem swap13_comm_u :
    wordLin swap13Word * (wordLin mWord * tStar * wordLin mWord) =
      (tStar * wordLin mWord * tStar * wordLin mWord) * wordLin swap13Word := by
  have h := swap13_a.2
  rw [wordLin_append, wordLin_append] at h
  have hu : wordLin mtmWord = wordLin mWord * tStar * wordLin mWord := by
    simp only [mtmWord, wordLin_append, wordLin_tWord, mul_assoc]
  have hz : wordLin zmWord = tStar * wordLin mWord * tStar * wordLin mWord := by
    simp only [zmWord, mtmWord, wordLin_append, wordLin_tWord, mul_assoc]
  rw [hu, hz] at h
  exact h

theorem swap13_conj_u :
    wordLin swap13Word * (wordLin mWord * tStar * wordLin mWord) * (wordLin swap13Word)⁻¹ =
      tStar * wordLin mWord * tStar * wordLin mWord :=
  mul_inv_eq_iff_eq_mul.2 swap13_comm_u

@[expose] noncomputable def swap13Op : SpaceB ≃ₗ[ℚ] SpaceB :=
  (wordLin omegaWord)⁻¹ * wordLin swap13Word * wordLin omegaWord

theorem swap13Op_mem : swap13Op ∈ Gmat :=
  mul_mem (mul_mem (inv_mem (wordLin_mem_Gmat _)) (wordLin_mem_Gmat _)) (wordLin_mem_Gmat _)

theorem swap13Op_comm_cbar :
    swap13Op * evalGL slet = evalGL slet * swap13Op := by
  rw [evalGL_slet_eq_conj]
  unfold swap13Op
  calc (wordLin omegaWord)⁻¹ * wordLin swap13Word * wordLin omegaWord *
        ((wordLin omegaWord)⁻¹ * tStar * wordLin omegaWord)
      = (wordLin omegaWord)⁻¹ * (wordLin swap13Word * tStar) * wordLin omegaWord := by group
    _ = (wordLin omegaWord)⁻¹ * (tStar * wordLin swap13Word) * wordLin omegaWord := by
        rw [swap13_comm_t]
    _ = (wordLin omegaWord)⁻¹ * tStar * wordLin omegaWord *
        ((wordLin omegaWord)⁻¹ * wordLin swap13Word * wordLin omegaWord) := by group

theorem swap13Op_conj_cbarP :
    swap13Op * evalGL sletP * swap13Op⁻¹ = evalGL slet * evalGL sletP := by
  rw [cbar_mul_cbarP_eq, eq_conj_of_conj omega_conj_cbarP]
  unfold swap13Op
  calc (wordLin omegaWord)⁻¹ * wordLin swap13Word * wordLin omegaWord *
        ((wordLin omegaWord)⁻¹ * (wordLin mWord * tStar * wordLin mWord) * wordLin omegaWord) *
        ((wordLin omegaWord)⁻¹ * wordLin swap13Word * wordLin omegaWord)⁻¹
      = (wordLin omegaWord)⁻¹ * (wordLin swap13Word * (wordLin mWord * tStar * wordLin mWord) *
        (wordLin swap13Word)⁻¹) * wordLin omegaWord := by group
    _ = (wordLin omegaWord)⁻¹ * (tStar * wordLin mWord * tStar * wordLin mWord) *
        wordLin omegaWord := by rw [swap13_conj_u]

theorem swap13Op_conj_cbarP' :
    swap13Op * evalGL sletP * swap13Op⁻¹ = evalGL sletP * evalGL slet := by
  rw [swap13Op_conj_cbarP, cbar_comm_cbarP]

@[expose] noncomputable def swap13 : Gmat := ⟨swap13Op, swap13Op_mem⟩

theorem swap13_exists :
    ∃ g : Gmat, g * fM y443C = fM y443C * g ∧ g * fM y443C' * g⁻¹ = fM y443C' * fM y443C := by
  refine ⟨swap13, Subtype.ext ?_, Subtype.ext ?_⟩
  · rw [Subgroup.coe_mul, Subgroup.coe_mul, ← evalGL_slet_eq]
    exact swap13Op_comm_cbar
  · rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, fM_y443C'_op_eq,
      ← evalGL_slet_eq]
    exact swap13Op_conj_cbarP'

theorem swap13_mem
    (hH : y443H.map fM = Subgroup.centralizer {fM y443C}) :
    ∃ g ∈ y443H, fM g * fM y443C' * (fM g)⁻¹ = fM y443C' * fM y443C := by
  obtain ⟨g, hg1, hg2⟩ := swap13_exists
  have hg : g ∈ y443H.map fM := by
    rw [hH]
    exact Subgroup.mem_centralizer_singleton_iff.2 hg1
  obtain ⟨h, hh, rfl⟩ := Subgroup.mem_map.1 hg
  exact ⟨h, hh, hg2⟩

end CFSG.YGroups.Y443
