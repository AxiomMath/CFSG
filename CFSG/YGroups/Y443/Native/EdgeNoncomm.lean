
module

public import CFSG.YGroups.Y443.Native.EdgeNoncommBase

public import CFSG.YGroups.Y443.Native.Hom
public import CFSG.YGroups.Y443.CentralProjection
public import CFSG.YGroups.Y443.Native.EdgeNoncommInputs
public import Certificates.Certificate9356
public import CFSG.Monster.AxisCount.DenseNative
public import CFSG.YGroups.Defs
public import CFSG.YGroups.Exact.Y322Inputs
public import CFSG.YGroups.Y322CentralInputs
public import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public import CFSG.YGroups.Y443.Native.OrderRelInputs
public import CFSG.YGroups.Y443.Native.PairRelAInputs
public import CFSG.YGroups.Y443.Native.PairRelBInputs
public import CFSG.YGroups.Y443.Native.PairRelCInputs
public import CFSG.YGroups.Y443.Native.PairRelDInputs
public import CFSG.YGroups.Y443.Native.Words
public import CFSG.Monster.AxisCount.DenseWord
public import CFSG.Monster.Griess.ThreeVectorSeparation
public import CFSG.Monster.Griess.Invariance.Diagonal
public import CFSG.Monster.Griess.Invariance.Octad.Basic
public import Certificates.Data.CFSGNative.YGroups.Y443.Witness
public meta import CFSG.YGroups.Y443.Native.Words
public meta import Certificates.Data.CFSGNative.MonsterAxis.Dense
public meta import Certificates.Data.CFSGNative.YGroups.Y443.MonsterWords
public meta import Certificates.Data.CFSGNative.YGroups.Y443.Witness
public import Certificates.Certificate9356Base

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.YGroups.Y443

open CFSG.Monster CFSG.Monster.AxisCount CFSG.Monster.Griess CFSG.Monster.Generated
  CFSG.YGroups.Y443Native CFSG.Open

namespace EdgeNoncomm

theorem fM_axS
    (s : MonsterY443Gen) : fM (axS s) = agS s := by
  cases s with
  | none => exact map_one fM
  | some g => exact fM_ax g

theorem coe_agS_I
    (s : MonsterY443Gen) :
    (((agS s)⁻¹ : Gmat) : SpaceB ≃ₗ[ℚ] SpaceB) = wordLin (gI (y443LetterOfGen s)) := by
  cases s with
  | none =>
    exact congrArg Subtype.val (inv_one : (1 : Gmat)⁻¹ = 1)
  | some g =>
    rw [← wIdx_add_one g]
    exact M_inv_eq_wordLin (wIdx_lt g)

theorem coe_agC_I
    {c : ℕ} (hc : c < 12) :
    (((agC c)⁻¹ : Gmat) : SpaceB ≃ₗ[ℚ] SpaceB) = wordLin (gI c) := by
  rw [agC, coe_agS_I, y443LetterOfGen_genOfLetter c hc]

theorem coe_pairsProd
    {ps : List (ℕ × ℕ)} (h : ∀ p ∈ ps, p.1 < 12 ∧ p.2 < 12) :
    ((pairsProd ps : Gmat) : SpaceB ≃ₗ[ℚ] SpaceB) = wordLin (pairsWord ps) := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    have hp := h p List.mem_cons_self
    have ih' := ih fun q hq => h q (List.mem_cons_of_mem _ hq)
    rw [pairsProd, List.map_cons, List.prod_cons, Subgroup.coe_mul, ← pairsProd, ih',
      pairsWord_cons, wordLin_append, pw, wordLin_append, Subgroup.coe_mul, coe_agC_I hp.1,
      coe_agC_L hp.2]

theorem fM_C_X :
    fM y443C * fM y443X = pairsProd nP := by
  rw [← map_mul, y443C_mul_X, map_list_prod, List.map_map, pairsProd]
  refine congrArg List.prod (List.map_congr_left fun p _ => ?_)
  show fM (y443T (y443GenOfLetter p.1) * y443T (y443GenOfLetter p.2)) =
    (agS (y443GenOfLetter p.1))⁻¹ * agS (y443GenOfLetter p.2)
  rw [y443T_mul_eq, map_mul, map_inv, fM_axS, fM_axS]

theorem edge_moves : wordLin edgeWord ≠ 1 :=
  Certificates.certificate9356

end EdgeNoncomm

open EdgeNoncomm in
theorem fM_C_X_pow_four_ne_one :
    (fM y443C * fM y443X) ^ 4 ≠ 1 := by
  intro h
  rw [fM_C_X] at h
  have h1 := coe_pairsProd nP_lt
  have h2 : wordLin edgeWord = 1 := by
    rw [edgeWord, wordLin_powL, ← h1, ← Subgroup.coe_pow, h, Subgroup.coe_one]
  exact edge_moves h2

open EdgeNoncomm in
theorem fM_C_X_noncomm :
    fM y443C * (fM y443X * fM y443C * fM y443X) ≠ (fM y443X * fM y443C * fM y443X) * fM y443C := by
  intro h
  refine fM_C_X_pow_four_ne_one (pow_four_eq_one_of_comm ?_ ?_ h)
  · rw [← map_mul, y443C_mul_self, map_one]
  · rw [← map_mul, y443X_mul_self, map_one]

end CFSG.YGroups.Y443
