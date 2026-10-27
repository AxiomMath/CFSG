module

public import CFSG.YGroups.Y443.Native.AlignAlg
public import CFSG.YGroups.Y443.Tri.Parabolic2
public import Certificates.Certificate16004
public import Certificates.Certificate6007
public import Certificates.Certificate10093
public import Certificates.Certificate10098
public import Certificates.Certificate10103
public import Certificates.Certificate10115
public import Certificates.Certificate10116
public import Certificates.Certificate10117
public import Certificates.Certificate10118
public import Certificates.Certificate10119
public import Certificates.Certificate10123
public import Certificates.Certificate10127

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.YGroups.Y443

open CFSG.Monster CFSG.Monster.AxisCount CFSG.Monster.Griess CFSG.Monster.Generated CFSG.Open

theorem y443RhoM_axL {s : ℕ} (hs : s ≤ 11) : y443RhoM (axL s) = axL (ρL s) := by
  refine Subtype.ext ?_
  rw [y443RhoM_coe, coe_axL, coe_axL, map_mul, y443Rho_gen (show 0 < 12 by norm_num),
    y443Rho_gen (show s < 12 by omega)]
  rfl

theorem y443RhoM_evalM : ∀ l : List ℕ, (∀ c ∈ l, c ≤ 11) →
    y443RhoM (evalM l) = evalM (l.map ρL)
  | [], _ => by simp [evalM]
  | [_], _ => by simp [evalM]
  | a :: b :: l, h => by
    simp only [evalM, List.map_cons, map_mul, map_inv]
    rw [y443RhoM_axL (h a (by simp)), y443RhoM_axL (h b (by simp)),
      y443RhoM_evalM l (fun c hc => h c (by simp [hc]))]

theorem slet_map_ρL : slet.map ρL =
    (List.replicate 9 [0, 5, 6, 7, 1, 2, 9]).flatten ++
      (List.replicate 9 [0, 9, 10, 11, 5, 6, 1]).flatten :=
  Certificates.certificate16004.1

theorem slet_map_ρL_le : ∀ c ∈ slet.map ρL, c ≤ 11 :=
  Certificates.certificate16004.2

theorem y443C'_eq_evalM : y443C' = evalM (slet.map ρL) := by
  show y443RhoM y443C = _
  rw [y443C_eq_evalM, y443RhoM_evalM slet slet_le]

theorem fM_y443C'_eq_evalGL :
    ((fM y443C' : Gmat) : SpaceB ≃ₗ[ℚ] SpaceB) = evalGL (slet.map ρL) := by
  rw [y443C'_eq_evalM, fM_evalM _ slet_map_ρL_le]

theorem fM_y443C'_eq :
    ((fM y443C' : Gmat) : SpaceB ≃ₗ[ℚ] SpaceB) = wordLin (wcWordOf (slet.map ρL)) := by
  rw [fM_y443C'_eq_evalGL, wordLin_wcWordOf _ slet_map_ρL_le]

theorem fM_rhoM_y443C_eq :
    ((fM (y443RhoM y443C) : Gmat) : SpaceB ≃ₗ[ℚ] SpaceB) = wordLin (wcWordOf (slet.map ρL)) :=
  fM_y443C'_eq

theorem axL_eq_Tl_mul
    (s : ℕ) : axL s = y443Tl 0 * y443Tl s := by
  refine Subtype.ext ?_
  have h := y443T_mul_coe (y443GenOfLetter 0) (y443GenOfLetter s)
  rw [coe_axL]
  exact h.symm

theorem axL_mem_H
    {s : ℕ} (hs : s < 12) (hs4 : s ≠ 4) : axL s ∈ y443H := by
  rw [axL_eq_Tl_mul]
  exact y443H.mul_mem (y443Tl_mem_H (by norm_num) (by norm_num)) (y443Tl_mem_H hs hs4)

theorem axElt_b1_eq_axL : axElt y443U11 = axL 1 := by
  refine Subtype.ext ?_
  show y443Gen 0 * y443Gen 1 = _
  rfl

theorem comp_rho_exists_order_three :
    ∃ h ∈ y443H.map (fM.comp y443RhoM.toMonoidHom), orderOf h = 3 := by
  refine ⟨fM.comp y443RhoM.toMonoidHom (axL 5), Subgroup.mem_map_of_mem _ (axL_mem_H (by norm_num)
    (by norm_num)), ?_⟩
  show orderOf (fM (y443RhoM (axL 5))) = 3
  rw [y443RhoM_axL (by norm_num)]
  have h1 : ρL 5 = 1 := rfl
  rw [h1, ← axElt_b1_eq_axL]
  exact orderOf_fM_b1

end CFSG.YGroups.Y443
