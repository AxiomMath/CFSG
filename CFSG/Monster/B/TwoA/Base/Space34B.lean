
module

public import CFSG.Monster.B.TwoA.Base.Space34BBase

public import CFSG.Monster.B.TwoA.Base.Space34A
public import CFSG.Monster.B.TwoA.Base.SevenPairC

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Lifts CFSG.Monster.Visible
  CFSG.Monster.VisQuot CFSG.Monster.ScalarKernel CFSG.Monster.SpinLattice
  CFSG.Monster.B.Short CFSG.Monster.B.Co2 CFSG.Monster.VisCert CFSG.Sporadic.Mathieu

open scoped Pointwise

theorem natCard_KofA3 :
    Nat.card (KofA A3) = 16 := by
  have h := natCard_ker_of_surj glHom3 glHom3_surjective
  rw [natCard_GL_three, natCard_FA3] at h
  rw [KofA3_eq, ← Nat.card_congr (glHom3.ker.equivMapOfInjective _
    Subtype.coe_injective).toEquiv]
  omega

theorem natCard_KofA2 :
    Nat.card (KofA A2) = 128 := by
  have h := natCard_ker_of_surj glHom2 glHom2_surjective
  rw [natCard_GL_two, natCard_FA2] at h
  rw [KofA2_eq, ← Nat.card_congr (glHom2.ker.equivMapOfInjective _
    Subtype.coe_injective).toEquiv]
  omega

theorem natCard_CU4 :
    Nat.card (wFix (U4 : Set (Wv v0))) = 2 ^ 11 := by
  rw [natCard_of_map (map_wFix_eq pairSpace_U4), natCard_monoSub, natCard_DofA3_quot,
    natCard_KofA3]
  norm_num

theorem natCard_CU3 :
    Nat.card (wFix (U3 : Set (Wv v0))) = 2 ^ 15 := by
  rw [natCard_of_map (map_wFix_eq pairSpace_U3), natCard_monoSub, natCard_DofA2_quot,
    natCard_KofA2]
  norm_num

theorem natCard_NU4w :
    Nat.card ↥(wSetStab U4 ⊓ Mfr) = 2752512 := by
  rw [natCard_of_map (map_wSetStab_inf_Mfr_eq pairSpace_U4), natCard_monoSub, natCard_Ceq_quot]
  change 2 ^ 10 * Nat.card FA3 = _
  rw [natCard_FA3]
  norm_num

theorem natCard_NU3w :
    Nat.card ↥(wSetStab U3 ⊓ Mfr) = 786432 := by
  rw [natCard_of_map (map_wSetStab_inf_Mfr_eq pairSpace_U3), natCard_monoSub, natCard_Ceq_quot]
  change 2 ^ 10 * Nat.card FA2 = _
  rw [natCard_FA2]
  norm_num

end CFSG.Monster.B.TwoA
