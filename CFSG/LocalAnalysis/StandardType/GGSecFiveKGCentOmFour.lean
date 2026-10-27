module

public import CFSG.LocalAnalysis.StandardType.GGRootCentKGOTwoOmPlusStep
public import CFSG.LocalAnalysis.StandardType.GGSixAutSteinbergTrialityModel

import CFSG.LocalAnalysis.StandardType.GGRootCentralizerOmegaSpin

public section

namespace CFSG.StandardType.KGCentOm

open CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.StandardType.KGOm
  CFSG.StandardType.Triality

private theorem iterate_tri_mem_roots (k : ℕ) :
    ∀ {γ : Fin 4 → ℤ}, γ ∈ rootsD4 → (⇑tri)^[k] γ ∈ rootsD4 := by
  induction k with
  | zero => intro γ hγ; simpa using hγ
  | succ k ih =>
      intro γ hγ
      rw [Function.iterate_succ_apply]
      exact ih (tri_mem_roots hγ)

theorem triSpinAut_pow_xr {K : Type} [Field K] [Finite K] [CharP K 2] (j : ℕ) {δ : Fin 4 → ℤ}
    (hδ : δ ∈ rootsD4) (b : K) :
    ((triSpinAut : MulAut (Sp8 K)) ^ j) (xr δ b) = xr ((⇑tri)^[j] δ) b := by
  induction j generalizing δ with
  | zero => rw [pow_zero, MulAut.one_apply, Function.iterate_zero_apply]
  | succ j ih =>
      rw [pow_succ, MulAut.mul_apply, triSpinAut_xr hδ, ih (tri_mem_roots hδ),
        Function.iterate_succ_apply]

theorem map_rootGroup_triSpinAut_pow {K : Type} [Field K] [Finite K] [CharP K 2] (j : ℕ)
    {δ : Fin 4 → ℤ} (hδ : δ ∈ rootsD4) :
    ((plusDatum 4 K three_le_four).rootGroup δ).map
        ((triSpinAut : MulAut (Sp8 K)) ^ j).toMonoidHom =
      (plusDatum 4 K three_le_four).rootGroup ((⇑tri)^[j] δ) := by
  have hP := CFSG.LieType.Steinberg.SpinPlus.isParametrization (K := K) three_le_four
  ext z
  rw [Subgroup.mem_map, (hP _ (iterate_tri_mem_roots j hδ)).1 z]
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨b, rfl⟩ := ((hP δ hδ).1 y).1 hy
    exact ⟨b, (triSpinAut_pow_xr j hδ b).symm⟩
  · rintro ⟨b, rfl⟩
    exact ⟨xr δ b, ((hP δ hδ).1 _).2 ⟨b, rfl⟩, triSpinAut_pow_xr j hδ b⟩

theorem triSpinAut_pow_mem_ggTorus {K : Type} [Field K] [Finite K] [CharP K 2] (j : ℕ) {h : Sp8 K}
    (hh : h ∈ ggTorus (plusDatum 4 K three_le_four)) :
    ((triSpinAut : MulAut (Sp8 K)) ^ j) h ∈ ggTorus (plusDatum 4 K three_le_four) := by
  simp only [ggTorus, Subgroup.mem_iInf] at hh ⊢
  refine fun (γ : Fin 4 → ℤ) hγ => ?_
  have hδ := iterate_tri_mem_roots (2 * j) hγ
  have hδγ : (⇑tri)^[j] ((⇑tri)^[2 * j] γ) = γ := by
    have h3 : Function.IsPeriodicPt (⇑tri) 3 γ := tri_tri_tri γ
    rw [← Function.iterate_add_apply, show j + 2 * j = 3 * j by omega]
    exact h3.mul_const j
  have hm := Subgroup.mem_map_of_mem ((triSpinAut : MulAut (Sp8 K)) ^ j).toMonoidHom (hh _ hδ)
  rwa [Subgroup.map_equiv_normalizer_eq, map_rootGroup_triSpinAut_pow j hδ, hδγ] at hm

private theorem tri_cover_check : ∀ r < 3, r ≠ 0 → ∀ (ε : Bool) (i₀ m : Fin 4) (u : Bool),
    ∃ (i j : Fin 4) (s t : Bool), i ≠ j ∧ i₀ ≠ i ∧ i₀ ≠ j ∧
      toStdD 4 ((⇑tri)^[r] (if ε then refl0 (fromStd (lv i j s t)) else fromStd (lv i j s t)))
        m = boolSign u := by
  decide

private theorem lv_apply_eq_boolSign : ∀ (i j m : Fin 4) (s t u : Bool), i ≠ j →
    lv i j s t m = boolSign u → (m = i ∧ u = s) ∨ (m = j ∧ u = t) := by
  decide

private theorem polar_plusVec_eq_zero_of_fix {K : Type} [Field K] {i j : Fin 4} (hij : i ≠ j)
    (s t : Bool) {v : Fin 4 ⊕ Fin 4 → K}
    (hv : spinAction (quadPlus 4 K)
      ((plusFrame 4 K three_le_four).longRoot hij s t (.ofAdd 1)) v = v) :
    QuadraticMap.polar (quadPlus 4 K) (plusVec 4 K i s) v = 0 ∧
      QuadraticMap.polar (quadPlus 4 K) (plusVec 4 K j t) v = 0 := by
  rw [HypFrame.spinAction_longRoot, one_mul, one_mul, add_sub_assoc, add_eq_left,
    sub_eq_zero] at hv
  obtain ⟨h1, h2⟩ :=
    ((plusFrame 4 K three_le_four).linearIndependent_vec_pair hij s t).eq_zero_of_pair' hv
  exact ⟨(QuadraticMap.polar_comm _ _ _).trans h2, (QuadraticMap.polar_comm _ _ _).trans h1⟩

private theorem polar_eq_zero_of_conj_fix {K : Type} [Field K] [CharP K 2] {c : Sp8 K →* Sp8 K}
    {γ : Sp8 K} {δ π : Fin 4 → ℤ} {i j i' j' i₀ : Fin 4} {s t s' t' : Bool} (hij : i ≠ j)
    (hi : i₀ ≠ i) (hj : i₀ ≠ j) (hδ : toStdD 4 δ = lv i j s t) (hij' : i' ≠ j')
    (hπ : toStdD 4 π = lv i' j' s' t') (hc : c (xr δ 1) = xr π 1)
    (hfix : γ * c (xr δ 1) * γ⁻¹ = xr δ 1) :
    QuadraticMap.polar (quadPlus 4 K) (plusVec 4 K i' s')
        (spinAction (quadPlus 4 K) γ⁻¹ (plusVec 4 K i₀ true)) = 0 ∧
      QuadraticMap.polar (quadPlus 4 K) (plusVec 4 K j' t')
        (spinAction (quadPlus 4 K) γ⁻¹ (plusVec 4 K i₀ true)) = 0 := by
  have he : spinAction (quadPlus 4 K) (xr δ 1) (plusVec 4 K i₀ true) = plusVec 4 K i₀ true := by
    rw [xr_eq_longRoot hij hδ 1]
    exact (plusFrame 4 K three_le_four).spinAction_longRoot_vec_of_ne hij s t 1 hi hj true
  have hrel : xr π 1 * γ⁻¹ = γ⁻¹ * xr δ 1 := by
    rw [← hc]
    calc c (xr δ 1) * γ⁻¹ = γ⁻¹ * (γ * c (xr δ 1) * γ⁻¹) := by
          rw [mul_assoc, inv_mul_cancel_left]
      _ = γ⁻¹ * xr δ 1 := by rw [hfix]
  refine polar_plusVec_eq_zero_of_fix hij' s' t' ?_
  rw [← xr_eq_longRoot hij' hπ 1, ← LinearEquiv.mul_apply, ← map_mul, hrel, map_mul,
    LinearEquiv.mul_apply, he]

theorem mod_three_eq_zero_of_conj_xr {K : Type} [Field K] [CharP K 2] {c : Sp8 K →* Sp8 K}
    {k : ℕ} {ε : Bool}
    (hcA : ∀ δ ∈ rootsD4, ∀ b : K, c (xr δ b) = xr ((⇑tri)^[k] (if ε then refl0 δ else δ)) b)
    {γ : Sp8 K} (i₀ : Fin 4)
    (hfix : ∀ δ ∈ rootsD4, toStdD 4 δ i₀ = 0 → ∀ b : K, γ * c (xr δ b) * γ⁻¹ = xr δ b) :
    k % 3 = 0 := by
  by_contra hk
  have hv : ∀ (m : Fin 4) (u : Bool), QuadraticMap.polar (quadPlus 4 K) (plusVec 4 K m u)
      (spinAction (quadPlus 4 K) γ⁻¹ (plusVec 4 K i₀ true)) = 0 := by
    intro m u
    obtain ⟨i, j, s, t, hij, hi, hj, hm⟩ :=
      tri_cover_check (k % 3) (Nat.mod_lt _ (by norm_num)) hk ε i₀ m u
    have hstd := (roots_check i j s t hij).1
    have hδ : fromStd (lv i j s t) ∈ rootsD4 := mem_rootsD4_iff.2 ⟨i, j, hij, s, t, hstd⟩
    have hε : (if ε then refl0 (fromStd (lv i j s t)) else fromStd (lv i j s t)) ∈ rootsD4 := by
      cases ε
      · exact hδ
      · exact refl0_mem_roots hδ
    obtain ⟨i', j', s', t', hij', hstd', -⟩ := exists_eq_fromStd (iterate_tri_mem_roots k hε)
    have hp : Function.IsPeriodicPt (⇑tri) 3
        (if ε then refl0 (fromStd (lv i j s t)) else fromStd (lv i j s t)) := tri_tri_tri _
    rw [hp.iterate_mod_apply k, hstd'] at hm
    have h0 : toStdD 4 (fromStd (lv i j s t)) i₀ = 0 := by
      rw [hstd]
      exact CFSG.LieType.Steinberg.SpinFrame.single_add_single_apply_of_ne hi hj _ _
    obtain ⟨h1, h2⟩ :=
      polar_eq_zero_of_conj_fix hij hi hj hstd hij' hstd' (hcA _ hδ 1) (hfix _ hδ h0 1)
    rcases lv_apply_eq_boolSign i' j' m s' t' u hij' hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    exacts [h1, h2]
  have h0 := (LinearEquiv.map_eq_zero_iff _).1 (RootCentOmega.eq_zero_of_polar_plusVec hv)
  have h1 := congrFun h0 (.inl i₀)
  simp at h1

private theorem plusSemiReflection_plusVec_flip0 {K : Type} [Field K] [CharP K 2] (hn : 1 ≤ 4)
    (m : Fin 4) (r : Bool) :
    plusSemiReflection hn (plusVec 4 K m r) = plusVec 4 K m (flip0 m r) := by
  by_cases hm : m = 0
  · subst hm
    have h2 : ∀ x : Fin 4 ⊕ Fin 4 → K, x + x = 0 := fun x => by
      rw [← two_smul K x, CharTwo.two_eq_zero, zero_smul]
    have hv : vPlusS (K := K) hn = plusVec 4 K 0 true + plusVec 4 K 0 false := rfl
    have hc : QuadraticMap.polar (quadPlus 4 K) (vPlusS hn) (plusVec 4 K 0 r) = 1 := by
      rw [hv, QuadraticMap.polar_add_left, polar_quadPlus_plusVec, polar_quadPlus_plusVec]
      cases r <;> simp
    rw [plusSemiReflection_apply, hc, one_smul, hv]
    cases r
    · show _ = plusVec 4 K 0 true
      rw [add_left_comm, h2, add_zero]
    · show _ = plusVec 4 K 0 false
      rw [← add_assoc, h2, zero_add]
  · rw [plusSemiReflection_plusVec hn (fun h => hm h), flip0, if_neg hm]

theorem spinAction_plusSemi_of_conj_xr {K : Type} [Field K] [CharP K 2] {c : Sp8 K →* Sp8 K}
    {ε : Bool}
    (hcA : ∀ δ ∈ rootsD4, ∀ b : K, c (xr δ b) = xr (if ε then refl0 δ else δ) b)
    (k : Sp8 K) (y : Fin 4 ⊕ Fin 4 → K) :
    spinAction (quadPlus 4 K) (c k) (plusSemi (by norm_num) ε 1 y) =
      plusSemi (by norm_num) ε 1 (spinAction (quadPlus 4 K) k y) := by
  cases ε
  · have hc : c = MonoidHom.id (Sp8 K) := Triality.ext_xr fun δ hδ b => by
      rw [hcA δ hδ b, if_neg Bool.false_ne_true, MonoidHom.id_apply]
    rw [hc, MonoidHom.id_apply, plusSemi_false_one, plusSemi_false_one]
  · have hhom : (spinAction (quadPlus 4 K)).comp c =
        (MulAut.conj (plusSemiReflection (K := K) (n := 4) (by norm_num))).toMonoidHom.comp
          (spinAction (quadPlus 4 K)) := by
      refine Triality.ext_xr fun δ hδ b => ?_
      obtain ⟨i, j, s, t, hij, hstd, -⟩ := exists_eq_fromStd hδ
      rw [MonoidHom.comp_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        MulAut.conj_apply, hcA δ hδ b, if_pos rfl,
        xr_eq_longRoot hij (toStdD_refl0_of_eq hij hstd) b, xr_eq_longRoot hij hstd b,
        RootCentOmega.spinAction_longRoot_eq_eichler,
        RootCentOmega.spinAction_longRoot_eq_eichler,
        CFSG.ClassicalGroups.Orthogonal.eichler_conj (plusSemiReflection_mem _), map_smul,
        plusFrame_vec, plusSemiReflection_plusVec_flip0, plusSemiReflection_plusVec_flip0]
    have hk := DFunLike.congr_fun hhom k
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply] at hk
    rw [plusSemi_true_one_apply, plusSemi_true_one_apply, hk, LinearEquiv.mul_apply,
      LinearEquiv.mul_apply, CFSG.ClassicalGroups.Orthogonal.LinearEquiv.inv_apply_apply']

end CFSG.StandardType.KGCentOm

end
