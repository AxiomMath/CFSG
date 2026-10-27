module

public import CFSG.RankThree.GF2n.Smith81.S81YE5Def

public section

namespace CFSG.RankThree.GF2n.Smith81.RootGenE5

open CFSG.LieType.Steinberg.Minuscule CFSG.Blueprint.Chevalley CFSG.RankThree.GF2n.Smith81
  CFSG.RankThree.GF2n.Smith81.E7Model CFSG.RankThree.GF2n.Smith81.RootGen

variable
  {K : Type} [Field K]

theorem sl2_orderOf_odd [CharP K 2] [Finite K] (m : Matrix.SpecialLinearGroup (Fin 2) K)
    (h10 : (m : Matrix (Fin 2) (Fin 2) K) 1 0 ≠ 0)
    (ht : (m : Matrix (Fin 2) (Fin 2) K) 0 0 + (m : Matrix (Fin 2) (Fin 2) K) 1 1 ≠ 0) :
    Odd (orderOf m) := by
  haveI : Finite (Matrix.SpecialLinearGroup (Fin 2) K) :=
    Finite.of_injective (fun x : Matrix.SpecialLinearGroup (Fin 2) K =>
      (x : Matrix (Fin 2) (Fin 2) K)) (fun x y h => Subtype.ext h)
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hdet : (m : Matrix (Fin 2) (Fin 2) K) 0 0 * (m : Matrix (Fin 2) (Fin 2) K) 1 1 -
      (m : Matrix (Fin 2) (Fin 2) K) 0 1 * (m : Matrix (Fin 2) (Fin 2) K) 1 0 = 1 := by
    have h := Matrix.SpecialLinearGroup.det_coe m
    rwa [Matrix.det_fin_two] at h
  set M : Matrix (Fin 2) (Fin 2) K := (m : Matrix (Fin 2) (Fin 2) K) with hM
  have hCH : M * M = (M 0 0 + M 1 1) • M + 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]
    all_goals first
      | ring1
      | linear_combination (-1 : K) * hdet - h2
  have hpow : ∀ n : ℕ, ∃ α β : K, ((m ^ n : Matrix.SpecialLinearGroup (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K) = α • M + β • (1 : Matrix (Fin 2) (Fin 2) K) := by
    intro n
    induction n with
    | zero => exact ⟨0, 1, by simp⟩
    | succ n ih =>
      obtain ⟨α, β, hn⟩ := ih
      refine ⟨α * (M 0 0 + M 1 1) + β, α, ?_⟩
      rw [pow_succ, Matrix.SpecialLinearGroup.coe_mul, hn, Matrix.add_mul, Matrix.smul_mul,
        Matrix.smul_mul, Matrix.one_mul, hCH]
      module
  have hfin : 0 < orderOf m := orderOf_pos m
  rcases Nat.even_or_odd (orderOf m) with ⟨j, hj⟩ | hodd
  · exfalso
    have hj0 : j ≠ 0 := by omega
    have hjlt : j < orderOf m := by omega
    have hNN : m ^ j * m ^ j = 1 := by
      rw [← pow_add, ← hj, pow_orderOf_eq_one]
    have hne1 : m ^ j ≠ 1 := pow_ne_one_of_lt_orderOf hj0 hjlt
    obtain ⟨α, β, hN⟩ := hpow j
    have hPP : ((m ^ j : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *
        ((m ^ j : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, hNN, Matrix.SpecialLinearGroup.coe_one]
    set P : Matrix (Fin 2) (Fin 2) K :=
      ((m ^ j : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) with hP
    have hP10 : P 1 0 = α * M 1 0 := by rw [hN]; simp
    have hP00 : P 0 0 = α * M 0 0 + β := by rw [hN]; simp
    have hP11 : P 1 1 = α * M 1 1 + β := by rw [hN]; simp
    have hP01 : P 0 1 = α * M 0 1 := by rw [hN]; simp
    have hPP10 : P 1 0 * P 0 0 + P 1 1 * P 1 0 = 0 := by
      have h := congrFun (congrFun hPP 1) 0
      simpa [Matrix.mul_apply, Fin.sum_univ_two] using h
    have key : α * α * (M 1 0 * (M 0 0 + M 1 1)) = 0 := by
      rw [hP10, hP00, hP11] at hPP10
      linear_combination hPP10 - (α * β * M 1 0) * h2
    have hα : α = 0 := by
      rcases mul_eq_zero.mp key with h | h
      · exact mul_self_eq_zero.mp h
      · exact absurd h (mul_ne_zero h10 ht)
    subst hα
    have hP00' : P 0 0 = β := by rw [hP00, zero_mul, zero_add]
    have hP01' : P 0 1 = 0 := by rw [hP01, zero_mul]
    have hP10' : P 1 0 = 0 := by rw [hP10, zero_mul]
    have hPP00 : P 0 0 * P 0 0 + P 0 1 * P 1 0 = 1 := by
      have h := congrFun (congrFun hPP 0) 0
      simpa [Matrix.mul_apply, Fin.sum_univ_two] using h
    rw [hP00', hP01', hP10'] at hPP00
    have hβ2 : β * β = 1 := by linear_combination hPP00
    have hβ1 : β = 1 := by
      have h' : (β - 1) ^ 2 = 0 := by linear_combination hβ2 + (1 - β) * h2
      linear_combination (pow_eq_zero_iff two_ne_zero).mp h'
    have hPeq : P = 1 := by
      rw [hN, zero_smul, zero_add, hβ1, one_smul]
    exact hne1 (Subtype.ext (hPeq.trans Matrix.SpecialLinearGroup.coe_one.symm))
  · exact hodd

theorem exists_pr_theta_one [CharP K 2] : ∃ b : Fin e7Data.d, pr b theta = 1 := by
  by_contra hcon
  apply e7Data_valid.rootOp_ne_zero (R := K) isRoot_theta
  have hall : ∀ x : Fin e7Data.d, x ∉ ((Finset.univ.filter fun b : Fin e7Data.d => pr b theta = 1 :
      Finset (Fin e7Data.d)) : Set (Fin e7Data.d)) := by
    intro x hx
    exact hcon ⟨x, by simpa using hx⟩
  refine LinearMap.ext fun v => Finsupp.ext fun x => ?_
  have hv := LinearMap.mem_range_self (e7Data.rootOp K theta) v
  rw [rootOp_range_eq_supported (K := K) isRoot_theta, Finsupp.mem_supported'] at hv
  simpa using hv x (hall x)

theorem jHom_eq_one_imp [CharP K 2] (P : Matrix.SpecialLinearGroup (Fin 2) K)
    (h : jHom P = 1) : P = 1 := by
  have hJ : jOp (P : Matrix (Fin 2) (Fin 2) K) = 1 := by
    rw [← jHom_val, h, Units.val_one]
  have hfix : ∀ v : V K, jOp (P : Matrix (Fin 2) (Fin 2) K) v = v := fun v => by
    rw [hJ, Module.End.one_apply]
  obtain ⟨b1, hb1⟩ := exists_pr_theta_one (K := K)
  have hb2 : pr (shift (-theta) b1) theta = -1 := pr_shift_neg isRoot_theta hb1
  have hs : shift theta (shift (-theta) b1) = b1 := shift_shift_neg isRoot_theta hb1
  have hne : shift (-theta) b1 ≠ b1 := by
    intro h'
    rw [h', hb1] at hb2
    norm_num at hb2
  have hne' : b1 ≠ shift (-theta) b1 := fun h' => hne h'.symm
  have e10 : (P : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := by
    have key : jOp (P : Matrix (Fin 2) (Fin 2) K) (Finsupp.single (shift (-theta) b1) 1) b1 =
        (Finsupp.single (shift (-theta) b1) 1) b1 := by
      rw [hfix]
    rw [jOp_apply, jFun_of_pos hb1] at key
    simpa [Finsupp.single_apply, hne, hne'] using key
  have e11 : (P : Matrix (Fin 2) (Fin 2) K) 1 1 = 1 := by
    have key : jOp (P : Matrix (Fin 2) (Fin 2) K) (Finsupp.single b1 1) b1 =
        (Finsupp.single b1 1) b1 := by
      rw [hfix]
    rw [jOp_apply, jFun_of_pos hb1] at key
    simpa [Finsupp.single_apply, hne'] using key
  have e01 : (P : Matrix (Fin 2) (Fin 2) K) 0 1 = 0 := by
    have key : jOp (P : Matrix (Fin 2) (Fin 2) K) (Finsupp.single b1 1)
        (shift (-theta) b1) = (Finsupp.single b1 1) (shift (-theta) b1) := by
      rw [hfix]
    rw [jOp_apply, jFun_of_neg hb2] at key
    simpa [Finsupp.single_apply, hs, hne] using key
  have e00 : (P : Matrix (Fin 2) (Fin 2) K) 0 0 = 1 := by
    have key : jOp (P : Matrix (Fin 2) (Fin 2) K) (Finsupp.single (shift (-theta) b1) 1)
        (shift (-theta) b1) = (Finsupp.single (shift (-theta) b1) 1) (shift (-theta) b1) := by
      rw [hfix]
    rw [jOp_apply, jFun_of_neg hb2] at key
    simpa [Finsupp.single_apply, hs, hne] using key
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [e00, e01, e10, e11]

theorem xm_theta_neg_odd [CharP K 2] [Finite K] {a b : K} (ha : a ≠ 0) (hb : b ≠ 0) :
    Odd (orderOf (e7Data_valid.xm K theta a * e7Data_valid.xm K (-theta) b)) ∧
      e7Data_valid.xm K theta a * e7Data_valid.xm K (-theta) b ≠ 1 := by
  set m : Matrix.SpecialLinearGroup (Fin 2) K :=
    MinData.Valid.slLower K a * MinData.Valid.slUpper K b with hm
  have hcoe : ((e7Data_valid.xm K theta a * e7Data_valid.xm K (-theta) b :
      e7Data_valid.minGroup K) : (Module.End K (V K))ˣ) = jHom m := by
    have e1 : jHom (MinData.Valid.slLower K a) = e7Data_valid.xu K theta a := (xu_theta a).symm
    have e2 : jHom (MinData.Valid.slUpper K b) = e7Data_valid.xu K (-theta) b :=
      (xu_neg_theta b).symm
    rw [hm, map_mul, e1, e2]
    rfl
  have hjinj : Function.Injective (jHom (K := K)) :=
    (injective_iff_map_eq_one (jHom (K := K))).2 fun P hP => jHom_eq_one_imp P hP
  have hord : orderOf (e7Data_valid.xm K theta a * e7Data_valid.xm K (-theta) b) = orderOf m := by
    have h1 := orderOf_injective (e7Data_valid.minGroup K).subtype
      (Subgroup.subtype_injective _) (e7Data_valid.xm K theta a * e7Data_valid.xm K (-theta) b)
    have h2 := orderOf_injective (jHom (K := K)) hjinj m
    rw [← h1, ← h2]
    exact congrArg orderOf hcoe
  have hm10 : (m : Matrix (Fin 2) (Fin 2) K) 1 0 = a := by
    rw [hm, Matrix.SpecialLinearGroup.coe_mul, MinData.Valid.slLower_val,
      MinData.Valid.slUpper_val]
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  have hmtr : (m : Matrix (Fin 2) (Fin 2) K) 0 0 + (m : Matrix (Fin 2) (Fin 2) K) 1 1 = a * b := by
    have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
    rw [hm, Matrix.SpecialLinearGroup.coe_mul, MinData.Valid.slLower_val,
      MinData.Valid.slUpper_val]
    simp [Matrix.mul_apply, Fin.sum_univ_two]
    linear_combination h2
  have hodd : Odd (orderOf m) :=
    sl2_orderOf_odd m (by rw [hm10]; exact ha) (by rw [hmtr]; exact mul_ne_zero ha hb)
  refine ⟨?_, ?_⟩
  · rw [hord]
    exact hodd
  · intro h
    have hx1 : jHom m = 1 := by
      rw [← hcoe, h]
      rfl
    have hm1 : m = 1 := jHom_eq_one_imp m hx1
    apply ha
    rw [← hm10, hm1, Matrix.SpecialLinearGroup.coe_one]
    simp

set_option maxRecDepth 20000 in
theorem e7_odd_disj [CharP K 2] {r s : V K ≃ₗ[K] V K} (hr : IsRt5 r) (hs : IsRt5 s)
    (hodd : Odd (orderOf (r * s))) (hne : r * s ≠ 1) :
    LinearMap.range ((r : V K →ₗ[K] V K) - 1) ⊓ LinearMap.range ((s : V K →ₗ[K] V K) - 1) = ⊥ := by
  obtain ⟨gr, hgr, rfl⟩ := isRt5_iff.mp hr
  obtain ⟨gs, hgs, rfl⟩ := isRt5_iff.mp hs
  let actHom : G7 K →* (V K ≃ₗ[K] V K) :=
    { toFun := act7, map_one' := act7_one, map_mul' := act7_mul }
  have hodd' : Odd (orderOf (gr * gs)) := by
    have h := orderOf_injective actHom act7_injective (gr * gs)
    have h2 : actHom (gr * gs) = act7 gr * act7 gs := act7_mul gr gs
    rw [h2] at h
    rw [← h]
    exact hodd
  have hne' : gr * gs ≠ 1 := by
    intro h
    apply hne
    rw [← act7_mul, h, act7_one]
  obtain ⟨e, a, b, -, -, hxe, hye⟩ := fe3_conj_core hgr hgs hodd' hne'
  have h1 : e * gr = e7Data_valid.xm K theta a * e := by
    rw [← hxe]
    simp
  have h1' : e * gs = e7Data_valid.xm K (-theta) b * e := by
    rw [← hye]
    simp
  have hA : act7 e * act7 gr = act7 (e7Data_valid.xm K theta a) * act7 e := by
    rw [← act7_mul e gr, ← act7_mul (e7Data_valid.xm K theta a) e, h1]
  have hB : act7 e * act7 gs = act7 (e7Data_valid.xm K (-theta) b) * act7 e := by
    rw [← act7_mul e gs, ← act7_mul (e7Data_valid.xm K (-theta) b) e, h1']
  have hvA : ∀ u : V K, act7 e (act7 gr u) = act7 (e7Data_valid.xm K theta a) (act7 e u) := by
    intro u
    have h := congrArg (fun f : V K ≃ₗ[K] V K => f u) hA
    simpa only [LinearEquiv.mul_apply] using h
  have hvB : ∀ u : V K, act7 e (act7 gs u) = act7 (e7Data_valid.xm K (-theta) b) (act7 e u) := by
    intro u
    have h := congrArg (fun f : V K ≃ₗ[K] V K => f u) hB
    simpa only [LinearEquiv.mul_apply] using h
  rw [Submodule.eq_bot_iff]
  intro w hw
  obtain ⟨hw1, hw2⟩ := Submodule.mem_inf.mp hw
  have hmem1 : act7 e w ∈ LinearMap.range (e7Data.rootOp K theta) := by
    obtain ⟨u, hu⟩ := LinearMap.mem_range.mp hw1
    subst hu
    refine LinearMap.mem_range.mpr ⟨a • act7 e u, ?_⟩
    simp only [LinearMap.sub_apply, Module.End.one_apply, LinearEquiv.coe_coe, map_sub, map_smul]
    rw [hvA u, act7_xm]
    abel
  have hmem2 : act7 e w ∈ LinearMap.range (e7Data.rootOp K (-theta)) := by
    obtain ⟨u, hu⟩ := LinearMap.mem_range.mp hw2
    subst hu
    refine LinearMap.mem_range.mpr ⟨b • act7 e u, ?_⟩
    simp only [LinearMap.sub_apply, Module.End.one_apply, LinearEquiv.coe_coe, map_sub, map_smul]
    rw [hvB u, act7_xm]
    abel
  rw [rootOp_range_eq_supported (K := K) isRoot_theta, Finsupp.mem_supported'] at hmem1
  rw [rootOp_range_eq_supported (K := K) (isRoot_neg isRoot_theta), Finsupp.mem_supported'] at hmem2
  have hz : act7 e w = 0 := by
    ext c
    by_cases h : pr c theta = 1
    · have h' : ¬ (pr c (-theta) = 1) := by
        rw [pr_neg, h]
        norm_num
      apply hmem2 c
      simpa using h'
    · apply hmem1 c
      simpa using h
  calc w = (act7 e).symm (act7 e w) := ((act7 e).symm_apply_apply w).symm
    _ = 0 := by rw [hz, map_zero]

end CFSG.RankThree.GF2n.Smith81.RootGenE5
