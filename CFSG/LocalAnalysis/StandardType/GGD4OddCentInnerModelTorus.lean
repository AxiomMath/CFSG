module

public import CFSG.LocalAnalysis.StandardType.GGD4OddCentInnerModelTri
public import CFSG.LocalAnalysis.StandardType.GGD4OddCentInnerLeafDefs
public import CFSG.LieType.D4Small.Om8Datum

public section

namespace CFSG.StandardType

namespace D4Inner

open CFSG.StandardType.Triality CFSG.StandardType.D4Rank
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData CFSG.LieType.Chevalley QuadraticMap
open CFSG.LieType.Universal.Spin (toStdD upperSL2 lowerSL2 plusFrame
  exists_eq_lowerSL2_mul_upperSL2_mul_lowerSL2_mul_upperSL2)
open scoped Matrix

variable {K : Type} [Field K]

section SL2Gen

variable {G : Type*} [Group G]

private theorem sl2_hom_apply_eq {f g : Matrix.SpecialLinearGroup (Fin 2) K →* G}
    (hu : ∀ c, f (upperSL2 c) = g (upperSL2 c)) (hl : ∀ c, f (lowerSL2 c) = g (lowerSL2 c))
    (M : Matrix.SpecialLinearGroup (Fin 2) K) : f M = g M := by
  obtain ⟨a, b, c, d, rfl⟩ := exists_eq_lowerSL2_mul_upperSL2_mul_lowerSL2_mul_upperSL2 M
  simp only [map_mul, hu, hl]

private theorem sl2_commute_of {f : Matrix.SpecialLinearGroup (Fin 2) K →* G} {z : G}
    (hu : ∀ c, Commute (f (upperSL2 c)) z) (hl : ∀ c, Commute (f (lowerSL2 c)) z)
    (M : Matrix.SpecialLinearGroup (Fin 2) K) : Commute (f M) z := by
  obtain ⟨a, b, c, d, rfl⟩ := exists_eq_lowerSL2_mul_upperSL2_mul_lowerSL2_mul_upperSL2 M
  simp only [map_mul]
  exact (((hl a).mul_left (hu b)).mul_left (hl c)).mul_left (hu d)

private theorem sl2_commute_of₂ {f g : Matrix.SpecialLinearGroup (Fin 2) K →* G}
    (huu : ∀ c d, Commute (f (upperSL2 c)) (g (upperSL2 d)))
    (hul : ∀ c d, Commute (f (upperSL2 c)) (g (lowerSL2 d)))
    (hlu : ∀ c d, Commute (f (lowerSL2 c)) (g (upperSL2 d)))
    (hll : ∀ c d, Commute (f (lowerSL2 c)) (g (lowerSL2 d)))
    (M N : Matrix.SpecialLinearGroup (Fin 2) K) : Commute (f M) (g N) :=
  sl2_commute_of
    (fun c => (sl2_commute_of (fun d => (huu c d).symm) (fun d => (hul c d).symm) N).symm)
    (fun c => (sl2_commute_of (fun d => (hlu c d).symm) (fun d => (hll c d).symm) N).symm) M

end SL2Gen

private noncomputable def iota8 {i j : Fin 4} (hij : i ≠ j) (s t : Bool) :
    Matrix.SpecialLinearGroup (Fin 2) K →* Om8 K :=
  model8.comp ((plusFrame 4 K three_le_four).longSL2 hij s t)

private def PlaneAct (ρ : Matrix.SpecialLinearGroup (Fin 2) K →* Om8 K) (e e' : Fin (2 * 4) → K)
    (M : Matrix.SpecialLinearGroup (Fin 2) K) : Prop :=
  act (ρ M) e = M 0 0 • e + M 1 0 • e' ∧ act (ρ M) e' = M 0 1 • e + M 1 1 • e'

private theorem PlaneAct.mul {ρ : Matrix.SpecialLinearGroup (Fin 2) K →* Om8 K}
    {e e' : Fin (2 * 4) → K} {M N : Matrix.SpecialLinearGroup (Fin 2) K}
    (hM : PlaneAct ρ e e' M) (hN : PlaneAct ρ e e' N) : PlaneAct ρ e e' (M * N) := by
  obtain ⟨hM1, hM2⟩ := hM
  obtain ⟨hN1, hN2⟩ := hN
  refine ⟨?_, ?_⟩
  · rw [map_mul, act_mul, hN1, act_add, act_smul, act_smul, hM1, hM2]
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
    module
  · rw [map_mul, act_mul, hN2, act_add, act_smul, act_smul, hM1, hM2]
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
    module

private theorem planeAct_of_gen {ρ : Matrix.SpecialLinearGroup (Fin 2) K →* Om8 K}
    {e e' : Fin (2 * 4) → K} (hu : ∀ c, PlaneAct ρ e e' (upperSL2 c))
    (hl : ∀ c, PlaneAct ρ e e' (lowerSL2 c)) (M : Matrix.SpecialLinearGroup (Fin 2) K) :
    PlaneAct ρ e e' M := by
  obtain ⟨a, b, c, d, rfl⟩ := exists_eq_lowerSL2_mul_upperSL2_mul_lowerSL2_mul_upperSL2 M
  exact (((hl a).mul (hu b)).mul (hl c)).mul (hu d)

section CharTwo

variable [CharP K 2]

private theorem iota8_upper {γ : Fin 4 → ℤ} {i j : Fin 4} (hij : i ≠ j) {s t : Bool}
    (h : toStdD 4 γ = lv i j s t) (c : K) : iota8 hij s t (upperSL2 c) = X8 γ c := by
  rw [iota8, MonoidHom.comp_apply,
    CFSG.LieType.Universal.Spin.HypFrame.longSL2_upperSL2, ← xr_eq_longRoot hij h]

private theorem iota8_lower {γ : Fin 4 → ℤ} {i j : Fin 4} (hij : i ≠ j) {s t : Bool}
    (h : toStdD 4 γ = lv j i (!t) (!s)) (c : K) : iota8 hij s t (lowerSL2 c) = X8 γ c := by
  rw [iota8, MonoidHom.comp_apply,
    CFSG.LieType.Universal.Spin.HypFrame.longSL2_lowerSL2, ← xr_eq_longRoot hij.symm h]

private theorem planeAct_iota8 {i j : Fin 4} (hij : i ≠ j) (s t : Bool)
    (M : Matrix.SpecialLinearGroup (Fin 2) K) :
    PlaneAct (iota8 (K := K) hij s t) (AutOm.pvec i s) (AutOm.pvec j (!t)) M := by
  refine planeAct_of_gen (fun c => ?_) (fun c => ?_) M
  · have h := (roots_check i j s t hij).1
    rw [PlaneAct, iota8_upper hij h, CFSG.LieType.D4Small.act_X8_pvec hij h,
      CFSG.LieType.D4Small.act_X8_pvec hij h]
    cases s <;> cases t <;> simp [hij, hij.symm, add_comm]
  · have h := (roots_check j i (!t) (!s) hij.symm).1
    rw [PlaneAct, iota8_lower hij h, CFSG.LieType.D4Small.act_X8_pvec hij.symm h,
      CFSG.LieType.D4Small.act_X8_pvec hij.symm h]
    cases s <;> cases t <;> simp [hij, hij.symm, add_comm]

private theorem act_iota8_of_ne {i j : Fin 4} (hij : i ≠ j) (s t : Bool) {k : Fin 4}
    (hki : k ≠ i) (hkj : k ≠ j) (r : Bool) (M : Matrix.SpecialLinearGroup (Fin 2) K) :
    act (iota8 (K := K) hij s t M) (AutOm.pvec k r) = AutOm.pvec k r := by
  have hu : ∀ c, act (iota8 (K := K) hij s t (upperSL2 c)) (AutOm.pvec k r) = AutOm.pvec k r := by
    intro c
    have h := (roots_check i j s t hij).1
    rw [iota8_upper hij h, CFSG.LieType.D4Small.act_X8_pvec hij h]
    simp [hki, hkj]
  have hl : ∀ c, act (iota8 (K := K) hij s t (lowerSL2 c)) (AutOm.pvec k r) = AutOm.pvec k r := by
    intro c
    have h := (roots_check j i (!t) (!s) hij.symm).1
    rw [iota8_lower hij h, CFSG.LieType.D4Small.act_X8_pvec hij.symm h]
    simp [hki, hkj]
  obtain ⟨a, b, c, d, rfl⟩ := exists_eq_lowerSL2_mul_upperSL2_mul_lowerSL2_mul_upperSL2 M
  simp only [map_mul, act_mul, hu, hl]

private noncomputable abbrev iotaA : Matrix.SpecialLinearGroup (Fin 2) K →* Om8 K :=
  iota8 OrdPTriLayer.idx12 true false

private noncomputable abbrev iotaC : Matrix.SpecialLinearGroup (Fin 2) K →* Om8 K :=
  iota8 OrdPTriLayer.idx03 false true

private noncomputable abbrev iotaD : Matrix.SpecialLinearGroup (Fin 2) K →* Om8 K :=
  iota8 OrdPTriLayer.idx03 true true

private theorem iotaA_upper (c : K) : iotaA (upperSL2 c) = X8 rootA c :=
  iota8_upper _ toStdD_rootA c

private theorem iotaA_lower (c : K) : iotaA (lowerSL2 c) = X8 (-rootA) c :=
  iota8_lower _ (by decide) c

private theorem iotaC_upper (c : K) : iotaC (upperSL2 c) = X8 rootC c :=
  iota8_upper _ toStdD_rootC c

private theorem iotaC_lower (c : K) : iotaC (lowerSL2 c) = X8 (-rootC) c :=
  iota8_lower _ (by decide) c

private theorem iotaD_upper (c : K) : iotaD (upperSL2 c) = X8 rootD c :=
  iota8_upper _ toStdD_rootD c

private theorem iotaD_lower (c : K) : iotaD (lowerSL2 c) = X8 (-rootD) c :=
  iota8_lower _ (by decide) c

private theorem commute_iota8 {i j k l : Fin 4} (hij : i ≠ j) (hkl : k ≠ l) (s t u v : Bool)
    (h₁ : 0 ≤ lv i j s t ⬝ᵥ lv k l u v) (h₂ : 0 ≤ lv i j s t ⬝ᵥ lv l k (!v) (!u))
    (h₃ : 0 ≤ lv j i (!t) (!s) ⬝ᵥ lv k l u v) (h₄ : 0 ≤ lv j i (!t) (!s) ⬝ᵥ lv l k (!v) (!u))
    (M N : Matrix.SpecialLinearGroup (Fin 2) K) :
    Commute (iota8 hij s t M) (iota8 hkl u v N) := by
  have hu := iota8_upper (K := K) hij (roots_check i j s t hij).1
  have hl := iota8_lower (K := K) hij (roots_check j i (!t) (!s) hij.symm).1
  have hu' := iota8_upper (K := K) hkl (roots_check k l u v hkl).1
  have hl' := iota8_lower (K := K) hkl (roots_check l k (!v) (!u) hkl.symm).1
  have r₁ := CFSG.LieType.D4Small.isD4Root_lv i j s t hij
  have r₂ := CFSG.LieType.D4Small.isD4Root_lv j i (!t) (!s) hij.symm
  have r₃ := CFSG.LieType.D4Small.isD4Root_lv k l u v hkl
  have r₄ := CFSG.LieType.D4Small.isD4Root_lv l k (!v) (!u) hkl.symm
  refine sl2_commute_of₂ (fun c d => ?_) (fun c d => ?_) (fun c d => ?_) (fun c d => ?_) M N
  · rw [hu, hu']
    exact CFSG.LieType.D4Small.commute_X8 r₁ r₃ h₁ c d
  · rw [hu, hl']
    exact CFSG.LieType.D4Small.commute_X8 r₁ r₄ h₂ c d
  · rw [hl, hu']
    exact CFSG.LieType.D4Small.commute_X8 r₂ r₃ h₃ c d
  · rw [hl, hl']
    exact CFSG.LieType.D4Small.commute_X8 r₂ r₄ h₄ c d

private theorem commute_iotaC_iotaA (M N : Matrix.SpecialLinearGroup (Fin 2) K) :
    Commute (iotaC M) (iotaA N) :=
  commute_iota8 _ _ _ _ _ _ (by decide) (by decide) (by decide) (by decide) M N

private theorem commute_iotaD_iotaA (M N : Matrix.SpecialLinearGroup (Fin 2) K) :
    Commute (iotaD M) (iotaA N) :=
  commute_iota8 _ _ _ _ _ _ (by decide) (by decide) (by decide) (by decide) M N

private theorem commute_iotaC_iotaD (M N : Matrix.SpecialLinearGroup (Fin 2) K) :
    Commute (iotaC M) (iotaD N) :=
  commute_iota8 _ _ _ _ _ _ (by decide) (by decide) (by decide) (by decide) M N

private theorem sZero_eq_iota :
    (sZero (K := K)) = iotaA tThree * iotaC tThree * iotaD tThree := by
  have ht : (tThree : Matrix.SpecialLinearGroup (Fin 2) K) = upperSL2 1 * lowerSL2 1 := by
    rw [tThree_eq]
    rfl
  rw [sZero, sUp, sLow, ← iotaA_upper, ← iotaA_lower, ← iotaC_upper, ← iotaC_lower,
    ← iotaD_upper, ← iotaD_lower, ht, map_mul, map_mul, map_mul]
  simp only [mul_assoc]
  rw [(commute_iotaD_iotaA (upperSL2 1) (lowerSL2 1)).left_comm,
    (commute_iotaC_iotaA (upperSL2 1) (lowerSL2 1)).left_comm,
    (commute_iotaC_iotaD (lowerSL2 1) (upperSL2 1)).symm.left_comm]

private theorem act_iotaA_e1 (M : Matrix.SpecialLinearGroup (Fin 2) K) :
    act (iotaA M) (AutOm.pvec 1 true) = M 0 0 • AutOm.pvec 1 true + M 1 0 • AutOm.pvec 2 true :=
  (planeAct_iota8 OrdPTriLayer.idx12 true false M).1

private theorem act_iotaC_f3 (M : Matrix.SpecialLinearGroup (Fin 2) K) :
    act (iotaC M) (AutOm.pvec 3 false) =
      M 0 1 • AutOm.pvec 0 false + M 1 1 • AutOm.pvec 3 false :=
  (planeAct_iota8 OrdPTriLayer.idx03 false true M).2

private theorem act_iotaD_f3 (M : Matrix.SpecialLinearGroup (Fin 2) K) :
    act (iotaD M) (AutOm.pvec 3 false) =
      M 0 1 • AutOm.pvec 0 true + M 1 1 • AutOm.pvec 3 false :=
  (planeAct_iota8 OrdPTriLayer.idx03 true true M).2

private theorem act_iotaC_of {k : Fin 4} (hk0 : k ≠ 0) (hk3 : k ≠ 3) (r : Bool)
    (M : Matrix.SpecialLinearGroup (Fin 2) K) : act (iotaC M) (AutOm.pvec k r) = AutOm.pvec k r :=
  act_iota8_of_ne OrdPTriLayer.idx03 false true hk0 hk3 r M

private theorem act_iotaD_of {k : Fin 4} (hk0 : k ≠ 0) (hk3 : k ≠ 3) (r : Bool)
    (M : Matrix.SpecialLinearGroup (Fin 2) K) : act (iotaD M) (AutOm.pvec k r) = AutOm.pvec k r :=
  act_iota8_of_ne OrdPTriLayer.idx03 true true hk0 hk3 r M

omit [CharP K 2] in
private theorem cd_smul_add_smul (a b : K) (k l : Fin 4) (r u : Bool) (m : Fin 4) (w : Bool) :
    cd (a • AutOm.pvec k r + b • AutOm.pvec l u) m w =
      a * (if k = m ∧ r = !w then 1 else 0) + b * (if l = m ∧ u = !w then 1 else 0) := by
  simp only [cd, polar_add_left, polar_smul_left, AutOm.polar_pvec, smul_eq_mul]

section Theta

variable [Finite K]

private theorem theta_iotaC (M : Matrix.SpecialLinearGroup (Fin 2) K) :
    theta (iotaC M) = iotaD M :=
  sl2_hom_apply_eq (f := (theta : MulAut (Om8 K)).toMonoidHom.comp iotaC) (g := iotaD)
    (fun c => by
      simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom, iotaC_upper,
        iotaD_upper, theta_X8 rootC_mem, tri_rootC])
    (fun c => by
      simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom, iotaC_lower,
        iotaD_lower, theta_X8 neg_rootC_mem, tri_neg_rootC]) M

private theorem theta_iotaD (M : Matrix.SpecialLinearGroup (Fin 2) K) :
    theta (iotaD M) = iotaA M :=
  sl2_hom_apply_eq (f := (theta : MulAut (Om8 K)).toMonoidHom.comp iotaD) (g := iotaA)
    (fun c => by
      simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom, iotaD_upper,
        iotaA_upper, theta_X8 rootD_mem, tri_rootD])
    (fun c => by
      simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom, iotaD_lower,
        iotaA_lower, theta_X8 neg_rootD_mem, tri_neg_rootD]) M

end Theta

private abbrev centT : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K) :=
  Subgroup.centralizer {tThree}

private theorem centT_entries {x : Matrix.SpecialLinearGroup (Fin 2) K} (hx : x ∈ centT) :
    x 1 0 = x 0 1 ∧ x 1 1 = x 0 0 + x 0 1 := by
  rw [Subgroup.mem_centralizer_singleton_iff] at hx
  have h00 := congrArg (fun M : Matrix.SpecialLinearGroup (Fin 2) K => M 0 0) hx
  have h01 := congrArg (fun M : Matrix.SpecialLinearGroup (Fin 2) K => M 0 1) hx
  simp [Matrix.mul_apply, Fin.sum_univ_two, coe_tThree] at h00 h01
  exact ⟨by linear_combination -h00, by linear_combination -h01⟩

private theorem centT_ext {x y : Matrix.SpecialLinearGroup (Fin 2) K} (hx : x ∈ centT)
    (hy : y ∈ centT) (h0 : x 0 0 = y 0 0) (h1 : x 1 0 = y 1 0) : x = y := by
  obtain ⟨hx1, hx2⟩ := centT_entries hx
  obtain ⟨hy1, hy2⟩ := centT_entries hy
  have h01 : x 0 1 = y 0 1 := by rw [← hx1, ← hy1, h1]
  ext i j
  fin_cases i <;> fin_cases j
  · exact h0
  · exact h01
  · exact h1
  · change x 1 1 = y 1 1
    rw [hx2, hy2, h0, h01]

private theorem eq_one_of_centT {x : Matrix.SpecialLinearGroup (Fin 2) K} (hx : x ∈ centT)
    (h : x 0 1 = 0) : x = 1 := by
  obtain ⟨hx1, hx2⟩ := centT_entries hx
  have hdet : x 0 0 * x 1 1 - x 0 1 * x 1 0 = 1 := by
    have := x.2
    rwa [Matrix.det_fin_two] at this
  rw [hx2, hx1, h, add_zero, mul_zero, sub_zero] at hdet
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hsq : (x 0 0 + 1) ^ 2 = 0 := by linear_combination hdet + (x 0 0 + 1) * h2
  have ha : x 0 0 = 1 := by
    have := (pow_eq_zero_iff (n := 2) two_ne_zero).1 hsq
    linear_combination this - h2
  ext i j
  fin_cases i <;> fin_cases j
  · simpa using ha
  · simpa using h
  · simpa [hx1] using h
  · simpa [hx2, h] using ha

private def normElt (a b : K) (h : a * (a + b) - b * b = 1) :
    Matrix.SpecialLinearGroup (Fin 2) K :=
  ⟨!![a, b; b, a + b], by rw [Matrix.det_fin_two_of]; exact h⟩

private theorem normElt_mem (a b : K) (h : a * (a + b) - b * b = 1) : normElt a b h ∈ centT := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_tThree]
  change !![a, b; b, a + b] * !![0, 1; 1, 1] = !![0, 1; 1, 1] * !![a, b; b, a + b]
  rw [Matrix.mul_fin_two, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

private theorem torNorm (l : K) (hD : l ^ 2 + l + 1 ≠ 0) :
    (l ^ 2 + 1) / (l ^ 2 + l + 1) * ((l ^ 2 + 1) / (l ^ 2 + l + 1) + 1 / (l ^ 2 + l + 1)) -
      1 / (l ^ 2 + l + 1) * (1 / (l ^ 2 + l + 1)) = 1 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  rw [← add_div, div_mul_div_comm, div_mul_div_comm, ← sub_div,
    div_eq_one_iff_eq (mul_ne_zero hD hD)]
  linear_combination (-(l ^ 3 + l)) * h2

private theorem sq_add_add_one_ne_zero [Finite K] {n : ℕ} (hK : Nat.card K = 2 ^ n)
    (hn : Odd n) (x : K) : x ^ 2 + x + 1 ≠ 0 := by
  intro hx
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hx3 : x ^ 3 = 1 := by linear_combination (x - 1) * hx
  have hx1 : x ≠ 1 := by
    rintro rfl
    exact one_ne_zero (by linear_combination hx - h2 : (1 : K) = 0)
  have hx0 : x ≠ 0 := by
    rintro rfl
    norm_num at hx
  have := Fintype.ofFinite K
  have hord : orderOf x = 3 := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact orderOf_eq_prime hx3 hx1
  have hdvd : orderOf x ∣ Fintype.card K - 1 :=
    orderOf_dvd_of_pow_eq_one (FiniteField.pow_card_sub_one_eq_one x hx0)
  rw [hord, ← Nat.card_eq_fintype_card, hK] at hdvd
  obtain ⟨m, rfl⟩ := hn
  have h4 : 4 ^ m % 3 = 1 := by
    rw [Nat.pow_mod]
    norm_num
  have h2n : 2 ^ (2 * m + 1) = 2 * 4 ^ m := by
    rw [pow_succ, pow_mul]
    norm_num [mul_comm]
  rw [h2n] at hdvd
  have hpos : 0 < 4 ^ m := by positivity
  omega

private theorem le_card_centT [Finite K] {n : ℕ} (hK : Nat.card K = 2 ^ n) (hn : Odd n) :
    2 ^ n + 1 ≤ Nat.card (centT (K := K)) := by
  have hD := sq_add_add_one_ne_zero hK hn
  let g : Option K → centT (K := K) := fun o => o.elim 1 fun l =>
    ⟨normElt _ _ (torNorm l (hD l)), normElt_mem _ _ _⟩
  have h01 : ∀ l, (((g (some l) : centT (K := K)) : Matrix.SpecialLinearGroup (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K) 0 1 = 1 / (l ^ 2 + l + 1) := fun l => rfl
  have h00 : ∀ l, (((g (some l) : centT (K := K)) : Matrix.SpecialLinearGroup (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K) 0 0 = (l ^ 2 + 1) / (l ^ 2 + l + 1) := fun l => rfl
  have hne : ∀ l, g (some l) ≠ 1 := fun l h => one_div_ne_zero (hD l) (by
    have e := congrArg (fun z : centT (K := K) =>
      ((z : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 1) h
    simpa only [h01, OneMemClass.coe_one, Matrix.SpecialLinearGroup.coe_one,
      Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1)] using e)
  have hg : Function.Injective g := by
    rintro (_ | l) (_ | m) h
    · rfl
    · exact absurd h.symm (hne m)
    · exact absurd h (hne l)
    · have e1 := congrArg (fun z : centT (K := K) =>
        ((z : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 1) h
      have e0 := congrArg (fun z : centT (K := K) =>
        ((z : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 0) h
      simp only [h01, h00] at e0 e1
      have hDD : l ^ 2 + l + 1 = m ^ 2 + m + 1 := by
        rwa [one_div, one_div, inv_inj] at e1
      rw [hDD, div_left_inj' (hD m)] at e0
      exact congrArg some (by linear_combination hDD - e0)
  have := Nat.card_le_card_of_injective g hg
  rwa [Finite.card_option, hK] at this

private theorem commute_iotaC_sZero {x : Matrix.SpecialLinearGroup (Fin 2) K} (hx : x ∈ centT) :
    Commute (iotaC x) (sZero (K := K)) := by
  have hxt : Commute (iotaC x) (iotaC tThree) := by
    have h := Subgroup.mem_centralizer_singleton_iff.1 hx
    change iotaC x * iotaC tThree = iotaC tThree * iotaC x
    rw [← map_mul, ← map_mul, h]
  rw [sZero_eq_iota]
  exact ((commute_iotaC_iotaA x tThree).mul_right hxt).mul_right (commute_iotaC_iotaD x tThree)

private theorem commute_iotaD_sZero {y : Matrix.SpecialLinearGroup (Fin 2) K} (hy : y ∈ centT) :
    Commute (iotaD y) (sZero (K := K)) := by
  have hyt : Commute (iotaD y) (iotaD tThree) := by
    have h := Subgroup.mem_centralizer_singleton_iff.1 hy
    change iotaD y * iotaD tThree = iotaD tThree * iotaD y
    rw [← map_mul, ← map_mul, h]
  rw [sZero_eq_iota]
  exact ((commute_iotaD_iotaA y tThree).mul_right (commute_iotaC_iotaD tThree y).symm).mul_right
    hyt

private theorem act_e1 (x y : Matrix.SpecialLinearGroup (Fin 2) K) :
    act ((iotaC x * iotaD y)⁻¹ * (iotaD x * iotaA y)) (AutOm.pvec 1 true) =
      y 0 0 • AutOm.pvec 1 true + y 1 0 • AutOm.pvec 2 true := by
  rw [mul_inv_rev, ← map_inv, ← map_inv]
  simp only [act_mul, act_iotaA_e1, act_add, act_smul,
    act_iotaC_of (k := 1) (by decide) (by decide), act_iotaC_of (k := 2) (by decide) (by decide),
    act_iotaD_of (k := 1) (by decide) (by decide), act_iotaD_of (k := 2) (by decide) (by decide)]

private theorem eq_one_of_iotaC_eq_iotaD {g : Matrix.SpecialLinearGroup (Fin 2) K}
    (hg : g ∈ centT) (h : iotaC g = iotaD g) : g = 1 := by
  refine eq_one_of_centT hg ?_
  have e := congrArg (fun z => cd (act z (AutOm.pvec 3 false)) 0 true) h
  simp only [act_iotaC_f3, act_iotaD_f3, cd_smul_add_smul] at e
  simpa using e

end CharTwo

section Norm

variable [Finite K] [CharP K 2]

omit [Finite K] [CharP K 2] in
private theorem conj_mem_centDer {s τ : Om8 K} (hτ : Commute τ s) {y : Om8 K}
    (hy : y ∈ centDer s) : τ * y * τ⁻¹ ∈ centDer s := by
  have hC : (Subgroup.centralizer ({s} : Set (Om8 K))).map (MulAut.conj τ).toMonoidHom ≤
      Subgroup.centralizer {s} := by
    rintro _ ⟨g, hg, rfl⟩
    have hg' : Commute g s := Subgroup.mem_centralizer_singleton_iff.1 hg
    exact Subgroup.mem_centralizer_singleton_iff.2 ((hτ.mul_left hg').mul_left hτ.inv_left).eq
  have hmem : (MulAut.conj τ).toMonoidHom y ∈
      (centDer s).map (MulAut.conj τ).toMonoidHom := ⟨y, hy, rfl⟩
  rw [Subgroup.map_commutator] at hmem
  exact Subgroup.commutator_mono hC hC hmem

private theorem inv_mul_theta_mem {τ : Om8 K} (hτ : Commute τ sZero)
    (hfix : ∀ y ∈ centDer (sZero (K := K)), (theta : MulAut (Om8 K)) y = y) :
    τ⁻¹ * theta τ ∈ Subgroup.centralizer (centDer (sZero (K := K)) : Set (Om8 K)) := by
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have h1 := hfix _ (conj_mem_centDer hτ hy)
  rw [map_mul, map_mul, map_inv, hfix y hy] at h1
  calc y * (τ⁻¹ * theta τ) = τ⁻¹ * (τ * y * τ⁻¹) * theta τ := by group
    _ = τ⁻¹ * (theta τ * y * (theta τ)⁻¹) * theta τ := by rw [h1]
    _ = τ⁻¹ * theta τ * y := by group

private theorem norm_inv_mul_theta (τ : Om8 K) :
    τ⁻¹ * theta τ * theta (τ⁻¹ * theta τ) * theta (theta (τ⁻¹ * theta τ)) = 1 := by
  have h3 : theta (theta (theta τ)) = τ := by
    have := congrArg (fun φ : MulAut (Om8 K) => φ τ) (theta_cube (K := K))
    simpa [pow_succ, MulAut.mul_apply] using this
  simp only [map_mul, map_inv, h3]
  group

theorem theta_norm_centralizer_centDer_sZero {n : ℕ} (hK : Nat.card K = 2 ^ n) (hn : Odd n)
    (hfix : ∀ y ∈ centDer (sZero (K := K)), (theta : MulAut (Om8 K)) y = y)
    (hcard : Nat.card (Subgroup.centralizer (centDer (sZero (K := K)) : Set (Om8 K))) =
      (2 ^ n + 1) ^ 2) :
    ∀ p ∈ Subgroup.centralizer (centDer (sZero (K := K)) : Set (Om8 K)),
      p * theta p * theta (theta p) = 1 := by
  set C := Subgroup.centralizer (centDer (sZero (K := K)) : Set (Om8 K))
  let τ : centT (K := K) × centT (K := K) → Om8 K := fun xy =>
    iotaC (xy.1 : Matrix.SpecialLinearGroup (Fin 2) K) *
      iotaD (xy.2 : Matrix.SpecialLinearGroup (Fin 2) K)
  have hτ : ∀ xy, Commute (τ xy) sZero := fun xy =>
    (commute_iotaC_sZero xy.1.2).mul_left (commute_iotaD_sZero xy.2.2)
  let F : centT (K := K) × centT (K := K) → C := fun xy =>
    ⟨(τ xy)⁻¹ * theta (τ xy), inv_mul_theta_mem (hτ xy) hfix⟩
  have hF : Function.Injective F := by
    rintro ⟨x, y⟩ ⟨x', y'⟩ h
    have h' : (τ (x, y))⁻¹ * theta (τ (x, y)) = (τ (x', y'))⁻¹ * theta (τ (x', y')) :=
      congrArg Subtype.val h
    simp only [τ, map_mul, theta_iotaC, theta_iotaD] at h'
    have hyy : y = y' := by
      have e := congrArg (fun z => act z (AutOm.pvec 1 true)) h'
      simp only [act_e1] at e
      have e0 := congrArg (fun v => cd v 1 false) e
      have e1 := congrArg (fun v => cd v 2 false) e
      simp only [cd_smul_add_smul] at e0 e1
      simp at e0 e1
      exact Subtype.ext (centT_ext y.2 y'.2 e0 e1)
    subst hyy
    set A := iotaC (x : Matrix.SpecialLinearGroup (Fin 2) K)
    set A' := iotaC (x' : Matrix.SpecialLinearGroup (Fin 2) K)
    set B := iotaD (y : Matrix.SpecialLinearGroup (Fin 2) K)
    set C₀ := iotaD (x : Matrix.SpecialLinearGroup (Fin 2) K)
    set C₀' := iotaD (x' : Matrix.SpecialLinearGroup (Fin 2) K)
    set D := iotaA (y : Matrix.SpecialLinearGroup (Fin 2) K)
    have h2 : A⁻¹ * C₀ = A'⁻¹ * C₀' := by
      have k1 : A⁻¹ * C₀ = B * ((A * B)⁻¹ * (C₀ * D)) * D⁻¹ := by group
      have k2 : A'⁻¹ * C₀' = B * ((A' * B)⁻¹ * (C₀' * D)) * D⁻¹ := by group
      rw [k1, k2, h']
    have h3 : iotaC ((x' : Matrix.SpecialLinearGroup (Fin 2) K) *
        (x : Matrix.SpecialLinearGroup (Fin 2) K)⁻¹) =
        iotaD ((x' : Matrix.SpecialLinearGroup (Fin 2) K) *
          (x : Matrix.SpecialLinearGroup (Fin 2) K)⁻¹) := by
      rw [map_mul, map_mul, map_inv, map_inv]
      calc A' * A⁻¹ = A' * (A⁻¹ * C₀) * C₀⁻¹ := by group
        _ = A' * (A'⁻¹ * C₀') * C₀⁻¹ := by rw [h2]
        _ = C₀' * C₀⁻¹ := by group
    have hxx : (x' : Matrix.SpecialLinearGroup (Fin 2) K) = x :=
      mul_inv_eq_one.1 (eq_one_of_iotaC_eq_iotaD (mul_mem x'.2 (inv_mem x.2)) h3)
    rw [Subtype.ext hxx]
  have : Finite C := Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
  have hS := le_card_centT (K := K) hK hn
  have hle : Nat.card C ≤ Nat.card (centT (K := K) × centT (K := K)) := by
    rw [hcard, Nat.card_prod, _root_.sq]
    exact Nat.mul_le_mul hS hS
  have hsurj := (hF.bijective_of_nat_card_le hle).2
  intro p hp
  obtain ⟨xy, hxy⟩ := hsurj ⟨p, hp⟩
  have hp' : (τ xy)⁻¹ * theta (τ xy) = p := congrArg Subtype.val hxy
  rw [← hp']
  exact norm_inv_mul_theta (τ xy)

end Norm

end D4Inner

end CFSG.StandardType

end
