module

public import CFSG.LocalAnalysis.StandardType.GGSixE6TwoModel
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotNonsplit
import CFSG.LieType.Chevalley.E6GraphInvolutionForms
public import CFSG.LieType.Chevalley.LangStronglyOrthogonalCommute
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotLeviPerp
public import CFSG.Walter.Defs
import CFSG.LieType.Chevalley.C2E6StandardFixedData
import CFSG.LieType.Chevalley.C2E6UnitaryFourImages
import CFSG.LieType.Chevalley.E6GraphHighestRootNormalizer
import CFSG.LieType.Chevalley.SimplyLacedFieldTwoCover
import CFSG.LocalAnalysis.ComponentInitial.CentralCoverAbelian
import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField

public section

namespace CFSG.StandardType.GGSixE6Two

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Open CFSG.SeitzReduction
  CFSG.StandardType.GGHalf CFSG.Timmesfeld.LieEmbed

section Cent

private lemma uSL_one_mul_vSL_one :
    ((uSL (1 : F2) * vSL (1 : F2) : SL2 F2) : Matrix (Fin 2) (Fin 2) F2) = !![0,1;1,1] := by
  rw [Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [uSL, vSL, Matrix.mul_apply, Fin.sum_univ_two] <;>
    linear_combination gf2_two

private lemma uSL_one_mul_vSL_one_pow_three : (uSL (1 : F2) * vSL (1 : F2)) ^ 3 = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one, uSL_one_mul_vSL_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_succ, pow_zero, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] <;>
    linear_combination gf2_two

private lemma uSL_one_mul_vSL_one_ne_one : (uSL (1 : F2) * vSL (1 : F2)) ≠ 1 := by
  intro h
  have h' := congrArg (fun (A : SL2 F2) => (A : Matrix (Fin 2) (Fin 2) F2) 0 0) h
  rw [uSL_one_mul_vSL_one, Matrix.SpecialLinearGroup.coe_one] at h'
  exact zero_ne_one h'

private lemma zE_eq_rootSL2_omega :
    zE = ⟨rootSL2 .E6 F2 (highRoot .E6) (uSL 1 * vSL 1),
      E6Pilot.rootSL2_highRoot_mem_adjointGroup _⟩ := by
  haveI : CharP F2 2 := inferInstance
  have h2 : (2 : F2) = 0 := gf2_two
  apply Subtype.ext
  simp only [zE, xr, Subgroup.coe_mul]
  rw [map_mul, E6GraphInvolution.rootSL2_uSL_of_two h2,
    E6GraphInvolution.rootSL2_vSL_of_two h2 (isRoot_highRoot .E6)]

theorem orderOf_zE : orderOf zE = 3 := by
  refine orderOf_eq_prime ?_ ?_
  · rw [zE_eq_rootSL2_omega]
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one, ← map_pow, uSL_one_mul_vSL_one_pow_three, map_one]
  · intro h
    apply uSL_one_mul_vSL_one_ne_one
    apply E6Pilot.rootSL2_highRoot_injective
    have h' : (⟨rootSL2 .E6 F2 (highRoot .E6) (uSL 1 * vSL 1),
        E6Pilot.rootSL2_highRoot_mem_adjointGroup _⟩ : EC) = 1 := by
      rw [← zE_eq_rootSL2_omega]; exact h
    simpa using congrArg Subtype.val h'

theorem zE_pow_three : zE ^ 3 = 1 := by
  have h := pow_orderOf_eq_one zE
  rw [orderOf_zE] at h
  exact h

theorem zE_mem_sTheta : zE ∈ sTheta := by
  haveI : CharP F2 2 := inferInstance
  rw [zE_eq_rootSL2_omega, sTheta, Subgroup.mem_subgroupOf]
  exact E6Pilot.rootSL2_highRoot_mem_highRootSL2 _

theorem card_sTheta : Nat.card sTheta = 6 := by
  haveI : CharP F2 2 := inferInstance
  have hcardF : Nat.card F2 = 2 := by rw [GaloisField.card 2 1 (by norm_num), pow_one]
  have h1 : Nat.card sTheta = Nat.card (EPilot.highRootSL2 .E6 F2) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe EPilot.highRootSL2_le_adjointGroup).toEquiv
  rw [h1, ← E6Pilot.range_rootSL2_highRoot]
  have h2 : Nat.card (rootSL2 .E6 F2 (highRoot .E6)).range = Nat.card (SL2 F2) :=
    Nat.card_congr (MonoidHom.ofInjective (E6Pilot.rootSL2_highRoot_injective)).symm.toEquiv
  rw [h2]
  haveI : Fintype F2 := Fintype.ofFinite F2
  have hSL : Nat.card (SL2 F2) = Nat.card F2 * (Nat.card F2 ^ 2 - 1) := by
    have h := Matrix.card_SL_field (𝔽 := F2) 2
    rw [Fin.prod_univ_two] at h
    simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one] at h
    rw [h, Nat.card_eq_fintype_card (α := F2)]
    have hq : 2 ≤ Fintype.card F2 := Fintype.one_lt_card
    apply Nat.div_eq_of_eq_mul_left (by omega)
    have e1 : Fintype.card F2 ^ 2 - Fintype.card F2 =
        Fintype.card F2 * (Fintype.card F2 - 1) := by
      rw [Nat.mul_sub_one, sq]
    rw [e1]
    ring
  rw [hSL, hcardF]
  norm_num

theorem centralizer_zE :
    Subgroup.centralizer ({zE} : Set EC) = Subgroup.zpowers zE ⊔ lE ∧
      Disjoint (Subgroup.zpowers zE) lE ∧ Subgroup.zpowers zE ≤ Subgroup.centralizer (lE : Set EC) := by
  haveI : CharP F2 2 := inferInstance
  have hF : Nat.card F2 = 2 := by rw [GaloisField.card 2 1 (by norm_num), pow_one]
  have hXJ : Subgroup.zpowers zE ≤ sTheta := Subgroup.zpowers_le.2 zE_mem_sTheta
  have hX : Nat.card (Subgroup.zpowers zE) = Nat.card F2 + 1 := by
    rw [Nat.card_zpowers, orderOf_zE, hF]
  have hcyc : IsCyclic (Subgroup.zpowers zE) := Subgroup.isCyclic_zpowers zE
  have h := E6Pilot.centralizer_nonsplit_E6 (K := F2) hXJ hX hcyc
  have hc : Subgroup.centralizer (Subgroup.zpowers zE : Set EC) =
      Subgroup.centralizer ({zE} : Set EC) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  rw [hc] at h
  simpa [lE] using h

theorem lE_le_centralizer_zE : lE ≤ Subgroup.centralizer ({zE} : Set EC) := by
  intro d hd
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hcomm : zE ∈ Subgroup.centralizer (lE : Set EC) :=
    centralizer_zE.2.2 (Subgroup.mem_zpowers zE)
  exact Subgroup.mem_centralizer_iff.1 hcomm d hd

theorem centralizer_zE_inv :
    Subgroup.centralizer ({zE⁻¹} : Set EC) = Subgroup.centralizer ({zE} : Set EC) := by
  ext g
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  exact Commute.inv_right_iff

end Cent

end CFSG.StandardType.GGSixE6Two
