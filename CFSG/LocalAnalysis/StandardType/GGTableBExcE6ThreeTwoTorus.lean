module

public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6ThreeTwo
public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6Three
public import CFSG.LieType.Chevalley.ParabolicRadicalLevi
public import CFSG.LieType.Chevalley.StandardParabolicCells
public import CFSG.LieType.Chevalley.GraphFixedSylowOpposition
public import CFSG.LieType.Chevalley.OrthogonalFixedOrbitMaps
public import CFSG.LieType.Chevalley.GraphFixedCoordinateDetection
public import CFSG.LieType.Chevalley.LangStronglyOrthogonalCommute
public import CFSG.LieType.Chevalley.RootCommutatorReduction

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.RankThree.CentralCover

namespace TableBExc.E6Three

section SL2Two

variable {K : Type} [Field K]

theorem coe_uvSL (h2 : (2 : K) = 0) :
    ((uSL (1 : K) * vSL 1 : SL2 K) : Matrix (Fin 2) (Fin 2) K) = !![0, 1; 1, 1] := by
  have h11 : (1 : K) + 1 = 0 := by rw [one_add_one_eq_two, h2]
  rw [Matrix.SpecialLinearGroup.coe_mul]
  simp only [uSL, vSL, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h11]

theorem uvSL_pow_three (h2 : (2 : K) = 0) : (uSL (1 : K) * vSL 1) ^ 3 = 1 := by
  have h11 : (1 : K) + 1 = 0 := by rw [one_add_one_eq_two, h2]
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, coe_uvSL h2, Matrix.SpecialLinearGroup.coe_one,
    pow_succ, pow_succ, pow_one]
  simp only [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h11]

theorem uvSL_mul_n_mul (h2 : (2 : K) = 0) :
    (uSL (1 : K) * vSL 1) * (uSL 1 * vSL 1 * uSL 1) * (uSL 1 * vSL 1) =
      uSL 1 * vSL 1 * uSL 1 := by
  have h11 : (1 : K) + 1 = 0 := by rw [one_add_one_eq_two, h2]
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul]
  rw [← Matrix.SpecialLinearGroup.coe_mul (uSL 1) (vSL 1), coe_uvSL h2]
  simp only [uSL, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h11]

theorem nSL_conj_uvSL (h2 : (2 : K) = 0) :
    (uSL (1 : K) * vSL 1 * uSL 1) * (uSL 1 * vSL 1) * (uSL 1 * vSL 1 * uSL 1)⁻¹ =
      (uSL 1 * vSL 1)⁻¹ := by
  have h := uvSL_mul_n_mul h2
  rw [mul_inv_eq_iff_eq_mul, eq_inv_mul_iff_mul_eq, ← mul_assoc, h]

end SL2Two

local instance tableBExcE6ThreeTwoTorusNeZeroRank : NeZero Tag.E6.rank := ⟨by decide⟩

@[expose] def bE6 : Fin 4 → Fin Tag.E6.rank → ℤ :=
  ![Pi.single 1 1, Pi.single 2 1, Pi.single 4 1, ![0, 1, 1, 2, 1, 0]]

theorem isRootB_bE6 : ∀ i : Fin 4,
    RootOps.isRootB .E6 (bE6 i) = true ∧ RootOps.isRootB .E6 (-bE6 i) = true := by
  decide +kernel

section Roots


theorem isRoot_bE6 (i : Fin 4) : IsRoot .E6 (bE6 i) :=
  RootOps.isRootB_iff.mp (isRootB_bE6 i).1

theorem isRoot_neg_bE6 (i : Fin 4) : IsRoot .E6 (-bE6 i) :=
  RootOps.isRootB_iff.mp (isRootB_bE6 i).2

end Roots

theorem height_bE6_pos : ∀ i : Fin 4, 0 < height (bE6 i) := by
  decide +kernel

theorem iform_bE6 : ∀ i j : Fin 4, i ≠ j →
    iform (bE6 i) (bE6 j) = 0 ∧ iform (bE6 i) (-bE6 j) = 0 ∧ iform (-bE6 i) (bE6 j) = 0 ∧
      iform (-bE6 i) (-bE6 j) = 0 := by
  decide +kernel

theorem isRootB_add_bE6 : ∀ i j : Fin 4, i ≠ j →
    RootOps.isRootB .E6 (bE6 i + bE6 j) = false ∧ RootOps.isRootB .E6 (bE6 i + -bE6 j) = false ∧
      RootOps.isRootB .E6 (-bE6 i + bE6 j) = false ∧
        RootOps.isRootB .E6 (-bE6 i + -bE6 j) = false := by
  decide +kernel

theorem not_isRoot_of_isRootB
    {v : Fin Tag.E6.rank → ℤ} (h : RootOps.isRootB .E6 v = false) :
    ¬ IsRoot .E6 v := fun hv => by
  rw [← RootOps.isRootB_iff] at hv
  rw [hv] at h
  exact Bool.noConfusion h

theorem wordProd_bE6_three :
    (coxeterSystem .E6).wordProd [3, 1, 2, 3] • (-(Pi.single 4 1 : Fin Tag.E6.rank → ℤ)) =
      -bE6 3 := by
  rw [smul_neg, wordProd_smul]
  decide +kernel

section Elts

variable {K : Type} [Field K]

theorem rootSL2_uSL_of_two (h2 : (2 : K) = 0) (β : Fin Tag.E6.rank → ℤ) (z : K) :
    rootSL2 .E6 K β (uSL z) = pinnedX .E6 K β z := by
  rw [rootSL2_uSL_eq]
  rcases pinnedSign_eq .E6 β with h | h <;> rw [h]
  · rw [one_smul]
  · rw [neg_smul, one_smul, show -z = z from by
      rw [neg_eq_iff_add_eq_zero, ← two_mul, h2, zero_mul]]

theorem rootSL2_vSL_of_two (h2 : (2 : K) = 0) {β : Fin Tag.E6.rank → ℤ} (hβ : IsRoot .E6 β)
    (z : K) : rootSL2 .E6 K β (vSL z) = pinnedX .E6 K (-β) z := by
  obtain ⟨ε, hε, h⟩ := exists_rootSL2_vSL_eq (K := K) hβ
  have hε1 : ε = 1 := by
    have h0 : (ε - 1) * (ε - 1) = 0 := by
      have : (ε - 1) * (ε - 1) = ε * ε - 2 * ε + 1 := by ring
      rw [this, hε, h2, zero_mul, sub_zero, one_add_one_eq_two, h2]
    exact sub_eq_zero.mp (mul_self_eq_zero.mp h0)
  rw [h, hε1, one_mul]

@[expose] noncomputable def uE6Two (i : Fin 4) : adjointGroup .E6 K :=
  ⟨pinnedX .E6 K (bE6 i) 1 * pinnedX .E6 K (-bE6 i) 1,
    mul_mem (pinnedX_mem_adjointGroup _ _) (pinnedX_mem_adjointGroup _ _)⟩

@[expose] noncomputable def nE6Two (i : Fin 4) : adjointGroup .E6 K :=
  ⟨pinnedX .E6 K (bE6 i) 1 * pinnedX .E6 K (-bE6 i) 1 * pinnedX .E6 K (bE6 i) 1,
    mul_mem (mul_mem (pinnedX_mem_adjointGroup _ _) (pinnedX_mem_adjointGroup _ _))
      (pinnedX_mem_adjointGroup _ _)⟩

theorem coe_uE6Two_eq (h2 : (2 : K) = 0) (i : Fin 4) :
    ((uE6Two (K := K) i : adjointGroup .E6 K) : ModGL .E6 K) =
      rootSL2 .E6 K (bE6 i) (uSL 1 * vSL 1) := by
  rw [map_mul, rootSL2_uSL_of_two h2, rootSL2_vSL_of_two h2 (isRoot_bE6 i)]
  rfl

theorem coe_nE6Two_eq (h2 : (2 : K) = 0) (i : Fin 4) :
    ((nE6Two (K := K) i : adjointGroup .E6 K) : ModGL .E6 K) =
      rootSL2 .E6 K (bE6 i) (uSL 1 * vSL 1 * uSL 1) := by
  rw [map_mul, map_mul, rootSL2_uSL_of_two h2, rootSL2_vSL_of_two h2 (isRoot_bE6 i)]
  rfl

theorem uE6Two_pow_three (h2 : (2 : K) = 0) (i : Fin 4) : (uE6Two (K := K) i) ^ 3 = 1 :=
  Subtype.ext (by
    rw [Subgroup.coe_pow, coe_uE6Two_eq h2, ← map_pow, uvSL_pow_three h2, map_one]
    rfl)

theorem nE6Two_conj_self (h2 : (2 : K) = 0) (i : Fin 4) :
    nE6Two i * uE6Two (K := K) i * (nE6Two i)⁻¹ = (uE6Two i)⁻¹ :=
  Subtype.ext (by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_uE6Two_eq h2, coe_nE6Two_eq h2]
    rw [← map_inv, ← map_mul, ← map_mul, ← map_inv, nSL_conj_uvSL h2])


theorem commute_pinnedX_bE6 {i j : Fin 4} (hij : i ≠ j) (c d : K) :
    Commute (pinnedX .E6 K (bE6 i) c) (pinnedX .E6 K (bE6 j) d) ∧
      Commute (pinnedX .E6 K (bE6 i) c) (pinnedX .E6 K (-bE6 j) d) ∧
      Commute (pinnedX .E6 K (-bE6 i) c) (pinnedX .E6 K (bE6 j) d) ∧
      Commute (pinnedX .E6 K (-bE6 i) c) (pinnedX .E6 K (-bE6 j) d) := by
  obtain ⟨h1, h2, h3, h4⟩ := iform_bE6 i j hij
  obtain ⟨r1, r2, r3, r4⟩ := isRootB_add_bE6 i j hij
  exact ⟨pinnedX_commute_of_iform_eq_zero K (isRoot_bE6 i) (isRoot_bE6 j) h1
      (not_isRoot_of_isRootB r1) c d,
    pinnedX_commute_of_iform_eq_zero K (isRoot_bE6 i) (isRoot_neg_bE6 j) h2
      (not_isRoot_of_isRootB r2) c d,
    pinnedX_commute_of_iform_eq_zero K (isRoot_neg_bE6 i) (isRoot_bE6 j) h3
      (not_isRoot_of_isRootB r3) c d,
    pinnedX_commute_of_iform_eq_zero K (isRoot_neg_bE6 i) (isRoot_neg_bE6 j) h4
      (not_isRoot_of_isRootB r4) c d⟩

theorem uE6Two_comm {i j : Fin 4} (hij : i ≠ j) :
    uE6Two (K := K) i * uE6Two j = uE6Two j * uE6Two i := by
  obtain ⟨h1, h2, h3, h4⟩ := commute_pinnedX_bE6 (K := K) hij 1 1
  apply Subtype.ext
  exact ((h1.mul_right h2).mul_left (h3.mul_right h4)).eq

theorem nE6Two_comm_uE6Two {i j : Fin 4} (hij : i ≠ j) :
    nE6Two (K := K) i * uE6Two j = uE6Two j * nE6Two i := by
  obtain ⟨h1, h2, h3, h4⟩ := commute_pinnedX_bE6 (K := K) hij 1 1
  apply Subtype.ext
  exact (((h1.mul_right h2).mul_left (h3.mul_right h4)).mul_left (h1.mul_right h2)).eq

end Elts

@[expose] def reflFunE6Two (i : Fin 4) : (Fin 4 → ZMod 3) →ₗ[ZMod 3] ZMod 3 :=
  2 • LinearMap.proj i

theorem reflFunE6Two_apply (i : Fin 4) (v : Fin 4 → ZMod 3) : reflFunE6Two i v = 2 * v i := by
  simp [reflFunE6Two]

theorem reflFunE6Two_single (i : Fin 4) : reflFunE6Two i (Pi.single i 1) = 2 := by
  simp [reflFunE6Two]

@[expose] noncomputable def reflLinE6Two (i : Fin 4) :
    (Fin 4 → ZMod 3) →ₗ[ZMod 3] (Fin 4 → ZMod 3) where
  toFun v := v - reflFunE6Two i v • Pi.single i 1
  map_add' v w := by
    rw [map_add, add_smul]
    abel
  map_smul' c v := by
    rw [map_smul, smul_eq_mul, mul_smul, RingHom.id_apply, smul_sub]

@[expose] noncomputable def reflE6Two (i : Fin 4) :
    Multiplicative (Fin 4 → ZMod 3) →* Multiplicative (Fin 4 → ZMod 3) :=
  AddMonoidHom.toMultiplicative (reflLinE6Two i).toAddMonoidHom

theorem toAdd_reflE6Two (i : Fin 4) (v : Fin 4 → ZMod 3) :
    Multiplicative.toAdd (reflE6Two i (.ofAdd v)) = v - reflFunE6Two i v • Pi.single i 1 :=
  rfl

theorem neg_bE6_ne : ∀ i : Fin 4, -bE6 i ≠ bE6 i := by
  decide +kernel

section Lift

variable {K : Type} [Field K]

theorem uE6Two_pairwise (h2 : (2 : K) = 0) :
    Pairwise fun i j : Fin 4 => ∀ x y : Multiplicative (ZMod 3),
      Commute (zmodPowHom (uE6Two (K := K) i) (uE6Two_pow_three h2 i) x)
        (zmodPowHom (uE6Two (K := K) j) (uE6Two_pow_three h2 j) y) := by
  intro i j hij x y
  change Commute (uE6Two (K := K) i ^ (Multiplicative.toAdd x).val)
    (uE6Two (K := K) j ^ (Multiplicative.toAdd y).val)
  exact Commute.pow_pow (uE6Two_comm (K := K) hij) _ _

@[expose] noncomputable def torusE6Two (h2 : (2 : K) = 0) :
    Multiplicative (Fin 4 → ZMod 3) →* adjointGroup .E6 K :=
  (MonoidHom.noncommPiCoprod (fun i => zmodPowHom (uE6Two i) (uE6Two_pow_three h2 i))
    (uE6Two_pairwise h2)).comp (MulEquiv.funMultiplicative (Fin 4) (ZMod 3)).toMonoidHom

theorem torusE6Two_single (h2 : (2 : K) = 0) (i : Fin 4) (a : ZMod 3) :
    torusE6Two h2 (.ofAdd (Pi.single i a)) =
      zmodPowHom (uE6Two (K := K) i) (uE6Two_pow_three h2 i) (.ofAdd a) := by
  have e : (MulEquiv.funMultiplicative (Fin 4) (ZMod 3)) (.ofAdd (Pi.single i a)) =
      Pi.mulSingle i (.ofAdd a) := by
    funext j
    by_cases hj : j = i
    · subst hj
      simp
    · simp [hj]
  rw [torusE6Two, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, e,
    MonoidHom.noncommPiCoprod_mulSingle]

theorem nE6Two_conj_torus (h2 : (2 : K) = 0) (i : Fin 4) (v : Fin 4 → ZMod 3) :
    nE6Two i * torusE6Two h2 (.ofAdd v) * (nE6Two i)⁻¹ =
      torusE6Two (K := K) h2 (.ofAdd (v - reflFunE6Two i v • Pi.single i 1)) := by
  have key : (MulAut.conj (nE6Two (K := K) i)).toMonoidHom.comp (torusE6Two h2) =
      (torusE6Two h2).comp (reflE6Two i) := by
    refine Three.hom_ext_of_single fun j a => ?_
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [torusE6Two_single, zmodPowHom_apply, ← conj_pow]
    by_cases hj : j = i
    · subst hj
      have hv : reflE6Two j (.ofAdd (Pi.single j a)) = .ofAdd (Pi.single j (-a)) := by
        apply Multiplicative.toAdd.injective
        rw [toAdd_reflE6Two, reflFunE6Two_apply, toAdd_ofAdd, Pi.single_eq_same]
        funext k
        by_cases hk : k = j
        · subst hk
          have e3 : ∀ b : ZMod 3, b - 2 * b = -b := by decide
          simpa using e3 a
        · simp [hk]
      rw [hv, torusE6Two_single, nE6Two_conj_self h2, inv_pow,
        ← zmodPowHom_apply (uE6Two j) (uE6Two_pow_three h2 j), ← map_inv, ← ofAdd_neg]
      rfl
    · have hv : reflE6Two i (.ofAdd (Pi.single j a)) = .ofAdd (Pi.single j a) := by
        apply Multiplicative.toAdd.injective
        rw [toAdd_reflE6Two, reflFunE6Two_apply, toAdd_ofAdd, Pi.single_eq_of_ne (Ne.symm hj)]
        simp
      rw [hv, torusE6Two_single, zmodPowHom_apply, nE6Two_comm_uE6Two (Ne.symm hj),
        mul_inv_cancel_right]
  have h := DFunLike.congr_fun key (.ofAdd v)
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h
  rw [h]
  congr 1


theorem uE6Two_ne_one (i : Fin 4) : uE6Two (K := K) i ≠ 1 := by
  intro h
  have h1 : pinnedX .E6 K (bE6 i) 1 * pinnedX .E6 K (-bE6 i) 1 = 1 := congrArg Subtype.val h
  have h2 : pinnedX .E6 K (-bE6 i) 1 = pinnedX .E6 K (bE6 i) (-1) := by
    rw [← pinnedX_neg]
    exact eq_inv_of_mul_eq_one_right h1
  exact neg_bE6_ne i (CFSG.SeitzReduction.EPilot.eq_of_pinnedX_eq_pinnedX_of_pos
    (isRoot_neg_bE6 i) (isRoot_bE6 i) (height_bE6_pos i) (neg_ne_zero.mpr one_ne_zero) h2)

theorem orderOf_uE6Two (h2 : (2 : K) = 0) (i : Fin 4) : orderOf (uE6Two (K := K) i) = 3 := by
  have := Fact.mk Nat.prime_three
  exact orderOf_eq_prime (uE6Two_pow_three h2 i) (uE6Two_ne_one i)

theorem torusE6Two_injective (h2 : (2 : K) = 0) : Function.Injective (torusE6Two (K := K) h2) := by
  rw [injective_iff_map_eq_one]
  intro w hw
  set v := Multiplicative.toAdd w with hv
  have hw' : w = .ofAdd v := rfl
  apply Multiplicative.toAdd.injective
  funext i
  have h1 : torusE6Two h2 (.ofAdd (v - reflFunE6Two i v • Pi.single i 1)) = 1 := by
    rw [← nE6Two_conj_torus h2 i v, ← hw', hw, mul_one, mul_inv_cancel]
  have e : (Multiplicative.ofAdd (reflFunE6Two i v • Pi.single i 1) :
      Multiplicative (Fin 4 → ZMod 3)) * .ofAdd (v - reflFunE6Two i v • Pi.single i 1) =
      .ofAdd v := by
    apply Multiplicative.toAdd.injective
    simp only [toAdd_ofAdd, toAdd_mul]
    abel
  have h3 : torusE6Two h2 (.ofAdd (reflFunE6Two i v • Pi.single i 1)) = 1 := by
    have h := congrArg (torusE6Two h2) e
    rw [map_mul, h1, mul_one, ← hw', hw] at h
    exact h
  have hs : (2 * v i) • (Pi.single i 1 : Fin 4 → ZMod 3) = Pi.single i (2 * v i) := by
    funext k
    rw [Pi.smul_apply, smul_eq_mul]
    by_cases hk : k = i
    · subst hk
      rw [Pi.single_eq_same, Pi.single_eq_same, mul_one]
    · rw [Pi.single_eq_of_ne hk, Pi.single_eq_of_ne hk, mul_zero]
  rw [reflFunE6Two_apply, hs, torusE6Two_single] at h3
  have h4 := zmodPowHom_injective (orderOf_uE6Two h2 i) (uE6Two_pow_three h2 i)
    (h3.trans (map_one _).symm)
  have h5 : 2 * v i = 0 := congrArg Multiplicative.toAdd h4
  have h6 : ∀ b : ZMod 3, 2 * b = 0 → b = 0 := by decide
  exact h6 _ h5

@[expose] def jE6Two : Set (Fin Tag.E6.rank) := {1, 2, 3, 4}

theorem pinnedX_neg_single_mem_parabolic {j : Fin Tag.E6.rank} (hj : j ∈ jE6Two) (c : K) :
    pinnedX .E6 K (-Pi.single j 1) c ∈ parabolicSubgroup .E6 K jE6Two := by
  rw [pinnedX_neg_single]
  exact parabolicLevi_le_parabolicSubgroup _
    (Subgroup.mem_sup_right (Subgroup.subset_closure ⟨j, hj, c, Or.inr rfl⟩))

theorem coe_uE6Two_mem_parabolic (i : Fin 4) :
    ((uE6Two (K := K) i : adjointGroup .E6 K) : ModGL .E6 K) ∈
      parabolicSubgroup .E6 K jE6Two := by
  have hx : pinnedX .E6 K (bE6 i) 1 ∈ parabolicSubgroup .E6 K jE6Two :=
    borelGroup_le_parabolicSubgroup _ (Subgroup.mem_sup_right
      (pinnedX_mem_rootSpan (S := {α | IsRoot .E6 α ∧ 0 < height α})
        ⟨isRoot_bE6 i, height_bE6_pos i⟩ 1))
  have hy : pinnedX .E6 K (-bE6 i) 1 ∈ parabolicSubgroup .E6 K jE6Two := by
    fin_cases i
    · exact pinnedX_neg_single_mem_parabolic (j := 1) (by simp [jE6Two]) 1
    · exact pinnedX_neg_single_mem_parabolic (j := 2) (by simp [jE6Two]) 1
    · exact pinnedX_neg_single_mem_parabolic (j := 4) (by simp [jE6Two]) 1
    · obtain ⟨ε, hε, hconj⟩ := exists_prod_weylElt_mul_pinnedX_mul_inv K [3, 1, 2, 3]
        (isRoot_neg_single .E6 4)
      have h := hconj ε
      rw [hε, wordProd_bE6_three] at h
      change pinnedX .E6 K (-bE6 3) 1 ∈ _
      rw [← h]
      have hW : (([3, 1, 2, 3] : List (Fin Tag.E6.rank)).map fun i => weylElt .E6 K i 1).prod ∈
          parabolicSubgroup .E6 K jE6Two := by
        refine Subgroup.list_prod_mem _ fun g hg => ?_
        simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hg
        rcases hg with rfl | rfl | rfl | rfl <;>
          exact weylElt_mem_parabolicSubgroup (by simp [jE6Two])
      exact mul_mem (mul_mem hW (pinnedX_neg_single_mem_parabolic (j := 4) (by simp [jE6Two]) ε))
        (inv_mem hW)
  exact mul_mem hx hy

theorem coe_torusE6Two_mem_parabolic (h2 : (2 : K) = 0) (v : Multiplicative (Fin 4 → ZMod 3)) :
    ((torusE6Two (K := K) h2 v : adjointGroup .E6 K) : ModGL .E6 K) ∈
      parabolicSubgroup .E6 K jE6Two := by
  have hle : (MonoidHom.noncommPiCoprod (fun i => zmodPowHom (uE6Two (K := K) i)
      (uE6Two_pow_three h2 i)) (uE6Two_pairwise h2)).range ≤
      (parabolicSubgroup .E6 K jE6Two).subgroupOf (adjointGroup .E6 K) := by
    rw [MonoidHom.noncommPiCoprod_range]
    refine iSup_le fun i => ?_
    rintro _ ⟨x, rfl⟩
    exact Subgroup.pow_mem _ (Subgroup.mem_subgroupOf.mpr (coe_uE6Two_mem_parabolic i)) _
  exact Subgroup.mem_subgroupOf.mp (hle ⟨(MulEquiv.funMultiplicative (Fin 4) (ZMod 3)) v, rfl⟩)

end Lift

section Final

variable {K : Type} [Field K]

theorem ggTorusLift_adjoint_E6_two [Finite K] [CharP K 2] :
    GGTorusLift 3 4 (adjointGroup .E6 K) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have := Fact.mk Nat.prime_two
  have hQC : parabolicRadical .E6 K jE6Two ≤ adjointGroup .E6 K :=
    ((parabolicRadical_le_posUnipotent jE6Two).trans le_sup_right).trans
      borelGroup_le_adjointGroup'
  set U := (parabolicRadical .E6 K jE6Two).subgroupOf (adjointGroup .E6 K) with hUdef
  have h0 : (Pi.single 0 1 : Fin Tag.E6.rank → ℤ) ∈ parabolicRadicalRoots .E6 jE6Two := by
    refine ⟨⟨isRoot_single .E6 0, by simp⟩, fun h => ?_⟩
    have h1 := h.1.2 0 (by
      simp only [jE6Two, Set.mem_insert_iff, Set.mem_singleton_iff]
      decide)
    simp at h1
  have hU : U ≠ ⊥ := by
    intro hbot
    have hx : (⟨pinnedX .E6 K (Pi.single 0 1) 1, pinnedX_mem_adjointGroup _ _⟩ :
        adjointGroup .E6 K) ∈ U :=
      Subgroup.mem_subgroupOf.mpr (pinnedX_mem_rootSpan (S := parabolicRadicalRoots .E6 jE6Two)
        h0 1)
    rw [hbot, Subgroup.mem_bot] at hx
    have hx' : pinnedX .E6 K (Pi.single 0 1) 1 = pinnedX .E6 K (Pi.single 0 1) 0 := by
      rw [pinnedX_zero]
      exact congrArg Subtype.val hx
    exact one_ne_zero (pinnedX_injective .E6 K _ hx')
  have hU2 : IsPGroup 2 U :=
    ((isPGroup_posUnipotent 2 .E6).to_le
      (parabolicRadical_le_posUnipotent jE6Two)).comap_of_injective _
        (adjointGroup .E6 K).subtype_injective
  have hTU : ∀ v, ∀ u ∈ U, torusE6Two h2 v * u * (torusE6Two h2 v)⁻¹ ∈ U := by
    intro v u hu
    rw [Subgroup.mem_subgroupOf] at hu ⊢
    have hN := parabolicSubgroup_le_normalizer_parabolicRadical jE6Two
      (coe_torusE6Two_mem_parabolic h2 v)
    have h3 := (Subgroup.mem_normalizer_iff.mp hN u).1 hu
    simpa using h3
  refine ggTorusLift_of_reflections_of_injOn Nat.prime_three (by norm_num) (torusE6Two h2)
    reflFunE6Two reflFunE6Two_single nE6Two (nE6Two_conj_torus h2) (W := ⊤) ?_
    (fun w _ hw => torusE6Two_injective h2 (hw.trans (map_one _).symm)) hU hU2 hTU
  rw [Subgroup.card_top, card_multiplicative_fin_zmod (p := 3) 4]

theorem ggTorusLift_E6_two [Finite K] [CharP K 2] : GGTorusLift 3 4 (RecipeGroup .E6 K) :=
  TableBF4.ggTorusLift_of_mulEquiv (recipeEquiv .E6 K) ggTorusLift_adjoint_E6_two

end Final

end TableBExc.E6Three

end CFSG.StandardType
