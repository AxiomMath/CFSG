module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDCoxEven
public import CFSG.LocalAnalysis.StandardType.GGQTwoDRMDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRMModuleDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveZSInputs
import CFSG.LocalAnalysis.StandardType.GGQTwoDRMLin
import CFSG.LocalAnalysis.StandardType.GGWitOrthClassR35Aux4
import CFSG.LocalAnalysis.StandardType.GGWitOrthPolar
import CFSG.LocalAnalysis.StandardType.ZS.Basic

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

noncomputable section

@[expose] def dQuadTwo (n : ℕ) : QuadraticForm (ZMod 3) (DVec n) :=
  QuadraticMap.weightedSumSquares (ZMod 3) fun _ : Fin n => (2 : ZMod 3)

@[expose] def dNormTwo (n : ℕ) : Subgroup (DVec n ≃ₗ[ZMod 3] DVec n) :=
  Subgroup.closure (ZS.ClassRefl 3 (dQuadTwo n) 1)

theorem dQuadTwo_eq_two_dDot (n : ℕ) (v : DVec n) :
    dQuadTwo n v = 2 * dDot n v v := by
  simp only [dQuadTwo, QuadraticMap.weightedSumSquares_apply, smul_eq_mul, dDot_apply,
    dotProduct, Finset.mul_sum]

theorem dQuadTwo_polar_eq {n : ℕ} (x y : DVec n) :
    QuadraticMap.polar (dQuadTwo n) x y = x ⬝ᵥ y := by
  rw [dQuadTwo, CFSG.StandardType.ZS.owPo_polar_weightedSumSquares, dotProduct,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h22 : (2 : ZMod 3) * 2 = 1 := by decide
  calc 2 * (2 * (x i * y i)) = ((2 : ZMod 3) * 2) * (x i * y i) := by ring
    _ = 1 * (x i * y i) := by rw [h22]
    _ = x i * y i := one_mul _

theorem dQuadTwo_polar_nondegenerate (n : ℕ) :
    (QuadraticMap.polarBilin (dQuadTwo n)).Nondegenerate := by
  refine LinearMap.BilinForm.Nondegenerate.ofSeparatingLeft fun v hv => ?_
  funext i
  have h := hv (dBasis n i)
  rw [QuadraticMap.polarBilin_apply_apply, dQuadTwo_polar_eq] at h
  rw [dBasis, Pi.basisFun_apply, dotProduct_single, mul_one] at h
  exact h

private lemma dDot_dRootAB (m : ℕ) (ε : Bool) (a b : Fin m) :
    dDot m (dRootAB m ε a b) = dFormAB m ε a b := by
  refine (dBasis m).ext fun j => ?_
  rw [dDot_apply, dFormAB_apply]
  simp [dRootAB, dBasis, Pi.basisFun_apply, Pi.single_apply, eq_comm]

private lemma dQuadTwo_dRootAB (m : ℕ) (ε : Bool) {a b : Fin m} (hab : a ≠ b) :
    dQuadTwo m (dRootAB m ε a b) = 1 := by
  rw [dQuadTwo_eq_two_dDot, dDot_dRootAB, dFormAB_dRootAB m ε hab]
  decide

private lemma dTau_mem_classRefl (m : ℕ) (ε : Bool) {a b : Fin m} (hab : a ≠ b) :
    dTau m ε a b ∈ ZS.ClassRefl 3 (dQuadTwo m) 1 := by
  have : Fact (Nat.Prime 3) := Nat.fact_prime_three
  have hD : dTau m ε a b = Module.reflection (dFormAB_dRootAB m ε hab) := by
    refine (dBasis m).ext' fun i => ?_
    rw [dTau_apply_vec m ε hab (dBasis m i), Module.reflection_apply]
  refine ⟨?_, ?_, dRootAB m ε a b, dQuadTwo_dRootAB m ε hab, ?_⟩
  · rw [hD]
    exact ZS.isRefl_reflection (p := 3) (by norm_num) (dFormAB_dRootAB m ε hab)
  · intro v
    rw [dQuadTwo_eq_two_dDot, dQuadTwo_eq_two_dDot]
    rw [dEven_dDot (dTau_mem_dEven m ε hab) v v]
  · rw [dTau_apply_vec m ε hab, dFormAB_dRootAB m ε hab]
    module

theorem dEven_le_dNormTwo {m : ℕ} (hm : 4 ≤ m) : dEven m ≤ dNormTwo m := by
  obtain ⟨e, he⟩ := dEven_equiv hm
  intro g hg
  obtain ⟨w, hw⟩ := e.surjective ⟨g, hg⟩
  have hw' : w ∈ Subgroup.closure (Set.range (ggCoxeterMatrixD m).simple) := by
    have h := (ggCoxeterMatrixD m).toCoxeterSystem.subgroup_closure_range_simple
    rw [CoxeterMatrix.toCoxeterSystem_simple] at h
    rw [h]
    exact Subgroup.mem_top w
  have hmem : ((e w : dEven m) : DVec m ≃ₗ[ZMod 3] DVec m) ∈ dNormTwo m := by
    refine Subgroup.closure_induction
      (p := fun w _ => ((e w : dEven m) : DVec m ≃ₗ[ZMod 3] DVec m) ∈ dNormTwo m)
      ?_ ?_ ?_ ?_ hw'
    · rintro x ⟨t, rfl⟩
      rw [he t]
      exact Subgroup.subset_closure (dTau_mem_classRefl m _
        (OrthTorus.simpleLo_ne_simpleHi (by omega) t))
    · simp
    · intro x y _ _ hx hy
      rw [map_mul]
      exact mul_mem hx hy
    · intro x _ hx
      rw [map_inv]
      exact inv_mem hx
  have hgw : ((e w : dEven m) : DVec m ≃ₗ[ZMod 3] DVec m) = g :=
    congrArg Subtype.val hw
  rw [← hgw]
  exact hmem

theorem linWeyl_dNormTwo_five : ZS.LinWeyl 3 (dNormTwo 5) := by
  have hw : ∀ i : Fin 5, ZS.owR35_wcan 5 i = 2 := by
    intro i
    simp [ZS.owR35_wcan]
  have he : ∀ v : DVec 5, dQuadTwo 5 v =
      ∑ i : Fin 5, (ZS.owR35_wcan 5) i *
        (LinearEquiv.refl (ZMod 3) (DVec 5) v i) ^ 2 := by
    intro v
    simp only [dQuadTwo, QuadraticMap.weightedSumSquares_apply, smul_eq_mul,
      LinearEquiv.refl_apply]
    exact Finset.sum_congr rfl fun i _ => by rw [hw i]; ring
  exact ZS.owR35_e6_canon_5 (dQuadTwo 5) (LinearEquiv.refl (ZMod 3) (DVec 5)) he

end

end CFSG.StandardType.QTwo

end
