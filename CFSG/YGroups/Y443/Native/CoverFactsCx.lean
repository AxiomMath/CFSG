module

public import CFSG.YGroups.Y443.Native.CoverFactsWords
public import CFSG.YGroups.Y443.Native.CoverFactsA
import Certificates.Kernel.KDense.Y443
public meta import CFSG.YGroups.Y443.Native.Align
public meta import CFSG.YGroups.Y443.Native.EdgeNoncomm
public meta import Certificates.Data.CFSGNative.MonsterAxis.Dense
public meta import Certificates.Data.CFSGNative.YGroups.Y443.MonsterWords
public meta import Certificates.Data.CFSGNative.YGroups.Y443.Witness
public meta import Certificates.Data.CFSGNative.YGroups.Y443.AlignWords
public import CFSG.YGroups.Y443.Native.AlignConj
public import Certificates.Certificate6007
public import Certificates.Certificate10093
public import Certificates.Certificate10098
public import Certificates.Certificate10103
public import Certificates.Certificate10107
public import Certificates.Certificate10108
public import Certificates.Certificate10110
public import Certificates.Certificate10112
public import Certificates.Certificate10115
public import Certificates.Certificate10116
public import Certificates.Certificate10117
public import Certificates.Certificate10118
public import Certificates.Certificate10119
public import Certificates.Certificate10123
public import Certificates.Certificate10127
public import CFSG.YGroups.Y443.Native.AlignB
public import CFSG.YGroups.Y443.Native.AlignW
public import CFSG.YGroups.Y443.Native.EdgeNoncomm

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.YGroups.Y443

open CFSG.Monster CFSG.Monster.AxisCount CFSG.Monster.Griess CFSG.Monster.Generated CFSG.Open
  CFSG.Monster.B.Short CFSG.YGroups.Y443Native

theorem cover_comm_p :
    wordLin omegaWord * wordLin (EdgeNoncomm.pairsWord EdgeNoncomm.nP) =
      wordLin coverPHat * wordLin omegaWord := by
  have h := cover_a.1
  rw [wordLin_append, wordLin_append] at h
  exact h

theorem cover_p_cube :
    wordLin coverPHat ^ 3 = 1 := by
  have h := cover_a.2.1
  rwa [wordLin_powL] at h

theorem cover_comm_q :
    wordLin omegaWord * wordLin coverQ = wordLin coverQHat * wordLin omegaWord := by
  have h := cover_a.2.2.1
  rw [wordLin_append, wordLin_append] at h
  exact h

theorem cover_comm_y :
    wordLin coverWy * (wordLin coverPHat * wordLin coverQHat) = tStar * wordLin coverWy := by
  have h := cover_a.2.2.2
  rw [wordLin_append, wordLin_append, wordLin_append, wordLin_tWord] at h
  exact h

theorem fM_cx_cube :
    (fM y443C * fM y443X) ^ 3 = 1 := by
  rw [EdgeNoncomm.fM_C_X]
  apply Subtype.ext
  rw [Subgroup.coe_pow, EdgeNoncomm.coe_pairsProd EdgeNoncomm.nP_lt, Subgroup.coe_one]
  have hP : wordLin (EdgeNoncomm.pairsWord EdgeNoncomm.nP) =
      (wordLin omegaWord)⁻¹ * wordLin coverPHat * wordLin omegaWord := by
    rw [mul_assoc, ← cover_comm_p, ← mul_assoc, inv_mul_cancel, one_mul]
  have hc := conj_pow (a := (wordLin omegaWord)⁻¹) (b := wordLin coverPHat) (i := 3)
  rw [inv_inv] at hc
  rw [hP, hc, cover_p_cube]
  group

theorem fM_X_mul_Y :
    fM y443X * fM y443Y = (EdgeNoncomm.agC 4)⁻¹ * EdgeNoncomm.agC 3 := by
  have h4 : y443GenOfLetter 4 = y443E1 := by
    simpa only [y443LetterOfGen_E1] using y443GenOfLetter_letterOfGen y443E1
  have h3 : y443GenOfLetter 3 = y443D1 := by
    simpa only [y443LetterOfGen_D1] using y443GenOfLetter_letterOfGen y443D1
  have h := congrArg fM (EdgeNoncomm.y443T_mul_eq y443E1 y443D1)
  rw [map_mul, map_mul, map_inv, EdgeNoncomm.fM_axS, EdgeNoncomm.fM_axS] at h
  rw [EdgeNoncomm.agC, EdgeNoncomm.agC, h4, h3]
  exact h

theorem fM_C_Y_lin :
    ((fM y443C * fM y443Y : Gmat) : SpaceB ≃ₗ[ℚ] SpaceB) =
      wordLin (EdgeNoncomm.pairsWord EdgeNoncomm.nP) * wordLin coverQ := by
  have hxx : fM y443X * fM y443X = 1 := by rw [← map_mul, y443X_mul_self, map_one]
  have h1 : fM y443C * fM y443Y = (fM y443C * fM y443X) * (fM y443X * fM y443Y) := by
    calc fM y443C * fM y443Y = fM y443C * (fM y443X * fM y443X) * fM y443Y := by
          rw [hxx, mul_one]
      _ = _ := by simp only [mul_assoc]
  rw [h1, fM_X_mul_Y, EdgeNoncomm.fM_C_X, Subgroup.coe_mul, Subgroup.coe_mul,
    EdgeNoncomm.coe_pairsProd EdgeNoncomm.nP_lt, EdgeNoncomm.coe_agC_I (by norm_num : 4 < 12),
    EdgeNoncomm.coe_agC_L (by norm_num : 3 < 12), coverQ, wordLin_append]

theorem cover_conj_aux {G : Type*} [Group G] {Ω W t c P q p q' : G} (hc : Ω * c * Ω⁻¹ = t)
    (hP : Ω * P = p * Ω) (hq : Ω * q = q' * Ω) (hW : W * (p * q') = t * W) :
    (Ω⁻¹ * W⁻¹ * Ω) * c * (Ω⁻¹ * W⁻¹ * Ω)⁻¹ = P * q := by
  have hPq : Ω * (P * q) = p * q' * Ω := by
    rw [← mul_assoc, hP, mul_assoc, hq, mul_assoc]
  have hWΩ : W * Ω * (P * q) = t * (W * Ω) := by
    rw [mul_assoc, hPq, ← mul_assoc W, hW, mul_assoc]
  have hPq' : P * q = (Ω⁻¹ * W⁻¹) * t * (W * Ω) := by
    rw [mul_assoc (Ω⁻¹ * W⁻¹), ← hWΩ]
    group
  have hc' : c = Ω⁻¹ * t * Ω := by rw [← hc]; group
  rw [hPq', hc']
  group

theorem fM_cy_conj :
    IsConj (fM y443C) (fM y443C * fM y443Y) := by
  rw [isConj_iff]
  have hg : (wordLin omegaWord)⁻¹ * (wordLin coverWy)⁻¹ * wordLin omegaWord ∈ Gmat :=
    mul_mem (mul_mem (inv_mem (wordLin_mem_Gmat _)) (inv_mem (wordLin_mem_Gmat _)))
      (wordLin_mem_Gmat _)
  refine ⟨⟨(wordLin omegaWord)⁻¹ * (wordLin coverWy)⁻¹ * wordLin omegaWord, hg⟩,
    Subtype.ext ?_⟩
  rw [fM_C_Y_lin]
  exact cover_conj_aux omega_conj cover_comm_p cover_comm_q cover_comm_y

end CFSG.YGroups.Y443
