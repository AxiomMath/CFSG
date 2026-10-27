module

public import CFSG.LieType.Chevalley.RootDiagonalWeylTransporter

public section

namespace CFSG.RankThree.PartOne.KFU

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

variable {K : Type} [Field K]

@[expose] def d4i0 : Fin TwistTag.D4.tag.rank := ⟨0, by decide⟩
@[expose] def d4i1 : Fin TwistTag.D4.tag.rank := ⟨1, by decide⟩
@[expose] def d4i2 : Fin TwistTag.D4.tag.rank := ⟨2, by decide⟩
@[expose] def d4i3 : Fin TwistTag.D4.tag.rank := ⟨3, by decide⟩

theorem fin_D4_cases (j : Fin TwistTag.D4.tag.rank) :
    j = d4i0 ∨ j = d4i1 ∨ j = d4i2 ∨ j = d4i3 := by
  revert j
  decide

theorem perm_D4_values :
    TwistTag.D4.perm d4i0 = d4i1 ∧ TwistTag.D4.perm d4i1 = d4i3 ∧
      TwistTag.D4.perm d4i3 = d4i0 ∧ TwistTag.D4.perm d4i2 = d4i2 := by
  decide

theorem cartan_d4_sum (i : Fin TwistTag.D4.tag.rank) (v : Fin TwistTag.D4.tag.rank → ℤ) :
    ∑ x, TwistTag.D4.tag.cartan i x * v x =
      TwistTag.D4.tag.cartan i d4i0 * v d4i0 + TwistTag.D4.tag.cartan i d4i1 * v d4i1 +
        TwistTag.D4.tag.cartan i d4i2 * v d4i2 + TwistTag.D4.tag.cartan i d4i3 * v d4i3 :=
  Fin.sum_univ_four (fun x => TwistTag.D4.tag.cartan i x * v x)

theorem reflect_d4_two (v : Fin TwistTag.D4.tag.rank → ℤ) :
    reflect TwistTag.D4.tag d4i2 v d4i0 = v d4i0 ∧ reflect TwistTag.D4.tag d4i2 v d4i1 = v d4i1 ∧
      reflect TwistTag.D4.tag d4i2 v d4i2 = v d4i0 + v d4i1 - v d4i2 + v d4i3 ∧
      reflect TwistTag.D4.tag d4i2 v d4i3 = v d4i3 := by
  have e0 : TwistTag.D4.tag.cartan d4i2 d4i0 = -1 := by decide
  have e1 : TwistTag.D4.tag.cartan d4i2 d4i1 = -1 := by decide
  have e2 : TwistTag.D4.tag.cartan d4i2 d4i2 = 2 := by decide
  have e3 : TwistTag.D4.tag.cartan d4i2 d4i3 = -1 := by decide
  have n01 : d4i0 ≠ d4i2 := by decide
  have n12 : d4i1 ≠ d4i2 := by decide
  have n32 : d4i3 ≠ d4i2 := by decide
  simp [reflect, cartan_d4_sum, e0, e1, e2, e3, n01, n12, n32]
  ring

theorem reflect_d4_zero (v : Fin TwistTag.D4.tag.rank → ℤ) :
    reflect TwistTag.D4.tag d4i0 v d4i0 = v d4i2 - v d4i0 ∧
      reflect TwistTag.D4.tag d4i0 v d4i1 = v d4i1 ∧
      reflect TwistTag.D4.tag d4i0 v d4i2 = v d4i2 ∧
      reflect TwistTag.D4.tag d4i0 v d4i3 = v d4i3 := by
  have e0 : TwistTag.D4.tag.cartan d4i0 d4i0 = 2 := by decide
  have e1 : TwistTag.D4.tag.cartan d4i0 d4i1 = 0 := by decide
  have e2 : TwistTag.D4.tag.cartan d4i0 d4i2 = -1 := by decide
  have e3 : TwistTag.D4.tag.cartan d4i0 d4i3 = 0 := by decide
  have n1 : d4i1 ≠ d4i0 := by decide
  have n2 : d4i2 ≠ d4i0 := by decide
  have n3 : d4i3 ≠ d4i0 := by decide
  simp [reflect, cartan_d4_sum, e0, e1, e2, e3, n1, n2, n3]
  ring

theorem reflect_d4_one (v : Fin TwistTag.D4.tag.rank → ℤ) :
    reflect TwistTag.D4.tag d4i1 v d4i0 = v d4i0 ∧
      reflect TwistTag.D4.tag d4i1 v d4i1 = v d4i2 - v d4i1 ∧
      reflect TwistTag.D4.tag d4i1 v d4i2 = v d4i2 ∧
      reflect TwistTag.D4.tag d4i1 v d4i3 = v d4i3 := by
  have e0 : TwistTag.D4.tag.cartan d4i1 d4i0 = 0 := by decide
  have e1 : TwistTag.D4.tag.cartan d4i1 d4i1 = 2 := by decide
  have e2 : TwistTag.D4.tag.cartan d4i1 d4i2 = -1 := by decide
  have e3 : TwistTag.D4.tag.cartan d4i1 d4i3 = 0 := by decide
  have n0 : d4i0 ≠ d4i1 := by decide
  have n2 : d4i2 ≠ d4i1 := by decide
  have n3 : d4i3 ≠ d4i1 := by decide
  simp [reflect, cartan_d4_sum, e0, e1, e2, e3, n0, n2, n3]
  ring

theorem reflect_d4_three (v : Fin TwistTag.D4.tag.rank → ℤ) :
    reflect TwistTag.D4.tag d4i3 v d4i0 = v d4i0 ∧
      reflect TwistTag.D4.tag d4i3 v d4i1 = v d4i1 ∧
      reflect TwistTag.D4.tag d4i3 v d4i2 = v d4i2 ∧
      reflect TwistTag.D4.tag d4i3 v d4i3 = v d4i2 - v d4i3 := by
  have e0 : TwistTag.D4.tag.cartan d4i3 d4i0 = 0 := by decide
  have e1 : TwistTag.D4.tag.cartan d4i3 d4i1 = 0 := by decide
  have e2 : TwistTag.D4.tag.cartan d4i3 d4i2 = -1 := by decide
  have e3 : TwistTag.D4.tag.cartan d4i3 d4i3 = 2 := by decide
  have n0 : d4i0 ≠ d4i3 := by decide
  have n1 : d4i1 ≠ d4i3 := by decide
  have n2 : d4i2 ≠ d4i3 := by decide
  simp [reflect, cartan_d4_sum, e0, e1, e2, e3, n0, n1, n2]
  ring

theorem orbitWord_D4_zero : TwistTag.D4.orbitWord ⟨0, by decide⟩ = [d4i0, d4i1, d4i3] := by
  rfl

theorem orbitWord_D4_one : TwistTag.D4.orbitWord ⟨1, by decide⟩ = [d4i2] := by
  rfl

theorem orbitReflection_D4_zero_smul (v : Fin TwistTag.D4.tag.rank → ℤ) :
    (TwistTag.D4.orbitReflection ⟨0, by decide⟩ • v) d4i0 = v d4i2 - v d4i0 ∧
      (TwistTag.D4.orbitReflection ⟨0, by decide⟩ • v) d4i1 = v d4i2 - v d4i1 ∧
      (TwistTag.D4.orbitReflection ⟨0, by decide⟩ • v) d4i2 = v d4i2 ∧
      (TwistTag.D4.orbitReflection ⟨0, by decide⟩ • v) d4i3 = v d4i2 - v d4i3 := by
  have h : TwistTag.D4.orbitReflection ⟨0, by decide⟩ • v =
      reflect TwistTag.D4.tag d4i0
        (reflect TwistTag.D4.tag d4i1 (reflect TwistTag.D4.tag d4i3 v)) := by
    unfold TwistTag.orbitReflection
    rw [orbitWord_D4_zero]
    simp only [CoxeterSystem.wordProd_cons, CoxeterSystem.wordProd_nil, mul_one, mul_smul,
      simple_smul]
  rw [h]
  obtain ⟨a0, a1, a2, a3⟩ := reflect_d4_three v
  obtain ⟨b0, b1, b2, b3⟩ := reflect_d4_one (reflect TwistTag.D4.tag d4i3 v)
  obtain ⟨c0, c1, c2, c3⟩ :=
    reflect_d4_zero (reflect TwistTag.D4.tag d4i1 (reflect TwistTag.D4.tag d4i3 v))
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [c0, b2, a2, b0, a0]
  · rw [c1, b1, a2, a1]
  · rw [c2, b2, a2]
  · rw [c3, b3, a3]

theorem orbitReflection_D4_one_smul (v : Fin TwistTag.D4.tag.rank → ℤ) :
    TwistTag.D4.orbitReflection ⟨1, by decide⟩ • v = reflect TwistTag.D4.tag d4i2 v := by
  unfold TwistTag.orbitReflection
  rw [orbitWord_D4_one]
  simp only [CoxeterSystem.wordProd_cons, CoxeterSystem.wordProd_nil, mul_one, simple_smul]

@[expose] def d4Tuple (x y : Kˣ) : Fin TwistTag.D4.tag.rank → Kˣ :=
  fun j => if j = d4i2 then y else x

theorem d4Tuple_zero (x y : Kˣ) : d4Tuple x y d4i0 = x := by
  have h : d4i0 ≠ d4i2 := by decide
  simp [d4Tuple, h]

theorem d4Tuple_one (x y : Kˣ) : d4Tuple x y d4i1 = x := by
  have h : d4i1 ≠ d4i2 := by decide
  simp [d4Tuple, h]

theorem d4Tuple_two (x y : Kˣ) : d4Tuple x y d4i2 = y := by simp [d4Tuple]

theorem d4Tuple_three (x y : Kˣ) : d4Tuple x y d4i3 = x := by
  have h : d4i3 ≠ d4i2 := by decide
  simp [d4Tuple, h]

theorem rootChar_d4Tuple (x y : Kˣ) (v : Fin TwistTag.D4.tag.rank → ℤ) :
    rootChar (d4Tuple x y) v = x ^ (v d4i0 + v d4i1 + v d4i3) * y ^ v d4i2 := by
  rw [rootChar]
  refine (Fin.prod_univ_four (fun i => d4Tuple x y i ^ v i)).trans ?_
  show d4Tuple x y d4i0 ^ v d4i0 * d4Tuple x y d4i1 ^ v d4i1 * d4Tuple x y d4i2 ^ v d4i2 *
    d4Tuple x y d4i3 ^ v d4i3 = _
  rw [d4Tuple_zero, d4Tuple_one, d4Tuple_two, d4Tuple_three, zpow_add, zpow_add]
  ac_rfl

theorem zpow_calc3 {G : Type*} [CommGroup G] (x y : G) (S m : ℤ) :
    (x * y) ^ S * y⁻¹ ^ (S - m) = x ^ S * y ^ m := by
  rw [inv_zpow', mul_zpow, mul_assoc, ← zpow_add, show S + -(S - m) = m by ring]

theorem zpow_calc4 {G : Type*} [CommGroup G] (x y : G) (S m : ℤ) :
    x⁻¹ ^ (3 * m - S) * (x ^ 3 * y) ^ m = x ^ S * y ^ m := by
  rw [inv_zpow', mul_zpow, ← zpow_natCast x 3, ← zpow_mul, ← mul_assoc, ← zpow_add,
    show -(3 * m - S) + ↑(3 : ℕ) * m = S by push_cast; ring]


theorem canonicalRep_orbit_one_conj (x y : Kˣ) :
    canonicalRep (coxeterSystem TwistTag.D4.tag) K (TwistTag.D4.orbitReflection ⟨1, by decide⟩) *
      rootDiagUnit TwistTag.D4.tag (d4Tuple x y) *
      (canonicalRep (coxeterSystem TwistTag.D4.tag) K
        (TwistTag.D4.orbitReflection ⟨1, by decide⟩))⁻¹ =
      rootDiagUnit TwistTag.D4.tag (d4Tuple (x * y) y⁻¹) := by
  refine ((rootDiagUnit_eq_conj_canonicalRep_iff (K := K) (d4Tuple (x * y) y⁻¹)
    (d4Tuple x y) (TwistTag.D4.orbitReflection ⟨1, by decide⟩)).2 (fun v => ?_)).symm
  rw [orbitReflection_D4_one_smul, rootChar_d4Tuple, rootChar_d4Tuple]
  obtain ⟨a0, a1, a2, a3⟩ := reflect_d4_two v
  rw [a0, a1, a2, a3]
  have e : v d4i0 + v d4i1 - v d4i2 + v d4i3 = (v d4i0 + v d4i1 + v d4i3) - v d4i2 := by ring
  rw [e]
  exact zpow_calc3 _ _ _ _

theorem canonicalRep_orbit_zero_conj (x y : Kˣ) :
    canonicalRep (coxeterSystem TwistTag.D4.tag) K (TwistTag.D4.orbitReflection ⟨0, by decide⟩) *
      rootDiagUnit TwistTag.D4.tag (d4Tuple x y) *
      (canonicalRep (coxeterSystem TwistTag.D4.tag) K
        (TwistTag.D4.orbitReflection ⟨0, by decide⟩))⁻¹ =
      rootDiagUnit TwistTag.D4.tag (d4Tuple x⁻¹ (x ^ 3 * y)) := by
  refine ((rootDiagUnit_eq_conj_canonicalRep_iff (K := K) (d4Tuple x⁻¹ (x ^ 3 * y))
    (d4Tuple x y) (TwistTag.D4.orbitReflection ⟨0, by decide⟩)).2 (fun v => ?_)).symm
  rw [rootChar_d4Tuple, rootChar_d4Tuple]
  obtain ⟨a0, a1, a2, a3⟩ := orbitReflection_D4_zero_smul v
  rw [a0, a1, a2, a3]
  have e : v d4i2 - v d4i0 + (v d4i2 - v d4i1) + (v d4i2 - v d4i3) =
      3 * v d4i2 - (v d4i0 + v d4i1 + v d4i3) := by ring
  rw [e]
  exact zpow_calc4 _ _ _ _

end CFSG.RankThree.PartOne.KFU
