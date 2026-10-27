module

public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6ThreeAd
public import CFSG.LocalAnalysis.StandardType.GGTableBExcAdLinear
public import CFSG.LieType.Chevalley.ParabolicWeylStabilizer
public import CFSG.Monster.B.E6.StdF4Root
public import CFSG.LieType.Chevalley.C2E6D4NaturalOrthogonal
public import CFSG.LieType.Chevalley.C2E6ExactRootRestrictions
public import CFSG.LieType.Chevalley.C2E6FieldExtensionResidueActions
public import CFSG.LieType.Chevalley.C2E6FirstResidueUnitarySix
public import CFSG.LieType.Chevalley.C2E6FourthResidueMinusEight
public import CFSG.LocalAnalysis.SectionRank.ClassicalOdd
public import CFSG.LocalAnalysis.SectionRank.EvenCover.LinearStep
public import CFSG.LocalAnalysis.SectionRank.SporadicCover
public import CFSG.Monster.B.Geometry.CoxeterWords
public import CFSG.Sporadic.M23.M23Group
public import CFSG.Sporadic.Th.F2Spec

public section

namespace CFSG.StandardType

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley TableBExc.E6Three


theorem e6_root_coordinate_bounds {α : Fin Tag.E6.rank → ℤ} (hα : IsRoot Tag.E6 α)
    (j : Fin Tag.E6.rank) : -3 ≤ α j ∧ α j ≤ 3 := by
  have hmax : e6HighestRoot j ≤ 3 := by fin_cases j <;> decide +kernel
  have hu := CFSG.Monster.B.E6.StdF4.le_e6HighestRoot hα j
  have hl := CFSG.Monster.B.E6.StdF4.le_e6HighestRoot (IsRoot.neg hα) j
  change -(α j) ≤ e6HighestRoot j at hl
  omega

theorem e6_root_coordinate_eq_of_mod {p : ℕ} (hp : 4 < p)
    {α : Fin Tag.E6.rank → ℤ} (hα : IsRoot Tag.E6 α) (i j : Fin Tag.E6.rank)
    (hmod : (α j : ZMod p) = ((Pi.single i 1 : Fin Tag.E6.rank → ℤ) j : ZMod p)) :
    α j = (Pi.single i 1 : Fin Tag.E6.rank → ℤ) j := by
  have ha := e6_root_coordinate_bounds hα j
  have hb : 0 ≤ (Pi.single i 1 : Fin Tag.E6.rank → ℤ) j ∧
      (Pi.single i 1 : Fin Tag.E6.rank → ℤ) j ≤ 1 := by
    by_cases hij : j = i <;> simp [Pi.single_apply, hij, eq_comm]
  have hdiv : (p : ℤ) ∣ (Pi.single i 1 : Fin Tag.E6.rank → ℤ) j - α j :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ p).1 hmod
  by_cases hnonneg : 0 ≤ (Pi.single i 1 : Fin Tag.E6.rank → ℤ) j - α j
  · have hz := Int.eq_zero_of_dvd_of_nonneg_of_lt hnonneg (by omega) hdiv
    omega
  · have hdiv' : (p : ℤ) ∣ α j - (Pi.single i 1 : Fin Tag.E6.rank → ℤ) j := by
      rw [show α j - (Pi.single i 1 : Fin Tag.E6.rank → ℤ) j =
        -((Pi.single i 1 : Fin Tag.E6.rank → ℤ) j - α j) by ring]
      exact dvd_neg.mpr hdiv
    have hz := Int.eq_zero_of_dvd_of_nonneg_of_lt (by omega) (by omega) hdiv'
    omega

theorem mem_parabolicWeylGroup_of_adAct_fix {p : ℕ} (hp : 4 < p)
    {S : Set (Fin Tag.E6.rank)} {w : WeylGroup Tag.E6}
    (hfix : ∀ x : Fin Tag.E6.rank → ZMod p, (∀ j ∈ S, x j = 0) → adAct .E6 p w x = x) :
    w ∈ parabolicWeylGroup Tag.E6 S := by
  classical
  have hunit : ∀ i j : Fin Tag.E6.rank, j ∉ S →
      (w⁻¹ • (Pi.single i 1 : Fin Tag.E6.rank → ℤ)) j =
        (Pi.single i 1 : Fin Tag.E6.rank → ℤ) j := by
    intro i j hj
    have hx : ∀ k ∈ S, (Pi.single j 1 : Fin Tag.E6.rank → ZMod p) k = 0 := by
      intro k hk
      have hkj : k ≠ j := fun h => hj (h ▸ hk)
      simp [Pi.single_eq_of_ne hkj]
    have hm : ((w⁻¹ • (Pi.single i 1 : Fin Tag.E6.rank → ℤ)) j : ZMod p) =
        ((Pi.single i 1 : Fin Tag.E6.rank → ℤ) j : ZMod p) := by
      simpa [adAct, Pi.single_apply, eq_comm] using congrFun (hfix (Pi.single j 1) hx) i
    exact e6_root_coordinate_eq_of_mod hp (IsRoot.smul (isRoot_single Tag.E6 i) w⁻¹) i j hm
  have hcoords : ∀ v : Fin Tag.E6.rank → ℤ, ∀ j ∉ S, (w⁻¹ • v) j = v j := by
    intro v j hj
    calc
      (w⁻¹ • v) j = ∑ i, v i * (w⁻¹ • (Pi.single i 1 : Fin Tag.E6.rank → ℤ)) j := by
        rw [smul_eq_sum_smul_single, Finset.sum_apply]
        simp only [Pi.smul_apply, smul_eq_mul]
      _ = ∑ i, v i * (Pi.single i 1 : Fin Tag.E6.rank → ℤ) j :=
        Finset.sum_congr rfl fun i _ => congrArg (fun x : ℤ => v i * x) (hunit i j hj)
      _ = v j := by simp [Pi.single_apply, eq_comm]
  have hw := (mem_parabolicWeylGroup_of_coord (A := S)
    ((coxeterSystem Tag.E6).length w⁻¹) w⁻¹ rfl hcoords).1
  simpa only [inv_inv] using (parabolicWeylGroup Tag.E6 S).inv_mem hw

theorem adPerm_injective_of_four_lt {p : ℕ} (hp : 4 < p) :
    Function.Injective (adPerm Tag.E6 p) := by
  intro u v huv
  have hrep : adPerm Tag.E6 p (v⁻¹ * u) = 1 := by
    rw [map_mul, map_inv, huv, inv_mul_cancel]
  have hfix : ∀ x : Fin Tag.E6.rank → ZMod p, adAct Tag.E6 p (v⁻¹ * u) x = x := by
    intro x
    exact congrArg (fun f : Equiv.Perm (Fin Tag.E6.rank → ZMod p) => f x) hrep
  have hw := mem_parabolicWeylGroup_of_adAct_fix hp (S := ∅) (fun x _ => hfix x)
  have he : v⁻¹ * u = 1 := by
    simpa only [parabolicWeylGroup, Set.image_empty, Subgroup.closure_empty,
      Subgroup.mem_bot] using hw
  exact (inv_mul_eq_one.mp he).symm

theorem adMulAutHom_injective_of_four_lt {p : ℕ} (hp : 4 < p) :
    Function.Injective (adMulAutHom Tag.E6 p) := by
  intro u v huv
  apply adPerm_injective_of_four_lt hp
  apply Equiv.ext
  intro x
  have h := congrArg (fun f : MulAut (Fin Tag.E6.rank → Multiplicative (ZMod p)) =>
    f (fun j => Multiplicative.ofAdd (x j))) huv
  funext i
  have hi := congrFun h i
  rw [adMulAutHom_apply, adMulAutHom_apply] at hi
  exact congrArg Multiplicative.toAdd hi

end CFSG.StandardType

end
