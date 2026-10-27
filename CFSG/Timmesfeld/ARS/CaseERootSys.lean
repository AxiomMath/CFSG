module

public import CFSG.LieType.RootSystem.Cartan

public section

namespace CFSG.Timmesfeld.ARS

open CFSG.LieType.RootSystem

variable {I : Type} [Fintype I] [DecidableEq I]

@[expose] def cartanForm (A : Matrix I I ℤ) (v : I → ℤ) : ℤ := ∑ m, v m * coroot A m v

section Form

variable {A : Matrix I I ℤ}

omit [DecidableEq I] in
theorem sum_mul_cartan_eq_coroot (hsymm : ∀ i j, A i j = A j i) (u : I → ℤ) (k : I) :
    ∑ m, u m * A m k = coroot A k u := by
  rw [coroot_apply]
  exact Finset.sum_congr rfl fun m _ => by rw [hsymm m k, mul_comm]

theorem cartanForm_add_smul_single (hsymm : ∀ i j, A i j = A j i) {k : I} (h2 : A k k = 2)
    (u : I → ℤ) (t : ℤ) :
    cartanForm A (u + t • Pi.single k 1) = cartanForm A u + 2 * t * coroot A k u + 2 * t ^ 2 := by
  have hc : ∀ m, coroot A m (u + t • Pi.single k 1) = coroot A m u + t * A m k := fun m => by
    rw [map_add, map_zsmul, coroot_single, smul_eq_mul]
  set e : I → ℤ := Pi.single k 1 with he
  have key : ∀ m, (u + t • e) m * (coroot A m u + t * A m k) =
      u m * coroot A m u + t * (u m * A m k) + t * (e m * coroot A m u) +
        t ^ 2 * (e m * A m k) := fun m => by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  unfold cartanForm
  simp only [hc]
  rw [Finset.sum_congr rfl fun m _ => key m]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [sum_mul_cartan_eq_coroot hsymm u k]
  have e2 : ∑ m, e m * coroot A m u = coroot A k u := by
    rw [Finset.sum_eq_single k (fun m _ hm => by simp [he, Pi.single_eq_of_ne hm])
      (fun h => absurd (Finset.mem_univ k) h)]
    simp [he]
  have e3 : ∑ m, e m * A m k = 2 := by
    rw [Finset.sum_eq_single k (fun m _ hm => by simp [he, Pi.single_eq_of_ne hm])
      (fun h => absurd (Finset.mem_univ k) h)]
    simp [he, h2]
  rw [e2, e3]
  ring

theorem cartanForm_reflection (hsymm : ∀ i j, A i j = A j i) {k : I} (h2 : A k k = 2)
    (u : I → ℤ) : cartanForm A (reflection A k u) = cartanForm A u := by
  rw [reflection_apply_coroot, sub_eq_add_neg, ← neg_smul, cartanForm_add_smul_single hsymm h2]
  ring

theorem cartanForm_single (i : I) : cartanForm A (Pi.single i 1) = A i i := by
  rw [cartanForm, Finset.sum_eq_single i (fun m _ hm => by simp [Pi.single_eq_of_ne hm])
    (fun h => absurd (Finset.mem_univ i) h)]
  simp [coroot_single]

end Form

section FiniteType

variable {A : Matrix I I ℤ} (hA : TauCeti.IsFiniteType A)

include hA in
theorem cartanForm_weylAction (hsymm : ∀ i j, A i j = A j i)
    (w : (coxeterMatrix hA).Group) (u : I → ℤ) :
    cartanForm A (weylAction hA w u) = cartanForm A u := by
  obtain ⟨ω, rfl⟩ := (coxeterMatrix hA).toCoxeterSystem.wordProd_surjective w
  induction ω with
  | nil => simp
  | cons j ω ih =>
    rw [CoxeterSystem.wordProd_cons, weylAction_mul_apply, weylAction_simple,
      cartanForm_reflection hsymm (hA.apply_self j), ih]

include hA in
theorem cartanForm_eq_two (hsymm : ∀ i j, A i j = A j i) {γ : I → ℤ} (hγ : γ ∈ roots hA ∅) :
    cartanForm A γ = 2 := by
  rcases hγ with ⟨w, i, rfl⟩ | ⟨w, i, hi, -⟩
  · rw [cartanForm_weylAction hA hsymm, cartanForm_single, hA.apply_self]
  · exact absurd hi (Set.notMem_empty i)

omit [Fintype I] [DecidableEq I] in
theorem cartan_symm_of_posDef (hpd : (A.map (Int.cast : ℤ → ℚ)).PosDef) (i j : I) :
    A i j = A j i := by
  have h := hpd.isHermitian.apply i j
  simp only [Matrix.map_apply, star_trivial] at h
  exact_mod_cast h.symm

omit [DecidableEq I] in
theorem cartanForm_pos (hpd : (A.map (Int.cast : ℤ → ℚ)).PosDef) {v : I → ℤ} (hv : v ≠ 0) :
    0 < cartanForm A v := by
  set x : I → ℚ := fun i => (v i : ℚ)
  have hx : x ≠ 0 := fun h => hv (funext fun i => by
    have h1 := congrFun h i
    simp only [x, Pi.zero_apply, Int.cast_eq_zero] at h1
    exact h1)
  have h := hpd.dotProduct_mulVec_pos hx
  simp only [star_trivial, dotProduct, Matrix.mulVec, Matrix.map_apply] at h
  have e : (cartanForm A v : ℚ) = ∑ i, x i * ∑ j, (A i j : ℚ) * x j := by
    simp [cartanForm, coroot_apply, x]
  exact_mod_cast e ▸ h

include hA in
theorem coroot_le_one (hpd : (A.map (Int.cast : ℤ → ℚ)).PosDef) {γ : I → ℤ}
    (hγ : γ ∈ roots hA ∅) {k : I} (hne : γ ≠ Pi.single k 1) : coroot A k γ ≤ 1 := by
  have hsymm := cartan_symm_of_posDef hpd
  have h1 := cartanForm_pos hpd (v := γ + (-1 : ℤ) • Pi.single k 1)
    (by rw [neg_one_smul, ← sub_eq_add_neg, sub_ne_zero]; exact hne)
  rw [cartanForm_add_smul_single hsymm (hA.apply_self k), cartanForm_eq_two hA hsymm hγ] at h1
  linarith

include hA in
theorem neg_one_le_coroot (hpd : (A.map (Int.cast : ℤ → ℚ)).PosDef) {γ : I → ℤ}
    (hγ : γ ∈ roots hA ∅) {k : I} (hne : γ ≠ -Pi.single k 1) : -1 ≤ coroot A k γ := by
  have hsymm := cartan_symm_of_posDef hpd
  have h1 := cartanForm_pos hpd (v := γ + (1 : ℤ) • Pi.single k 1)
    (by rw [one_smul, ← sub_neg_eq_add, sub_ne_zero]; exact hne)
  rw [cartanForm_add_smul_single hsymm (hA.apply_self k), cartanForm_eq_two hA hsymm hγ] at h1
  linarith


include hA in
theorem weylAction_apply_of_mem_parabolic {J : Set I} {z : (coxeterMatrix hA).Group}
    (hz : z ∈ (coxeterMatrix hA).toCoxeterSystem.parabolic J) (v : I → ℤ) {k : I}
    (hk : k ∉ J) : weylAction hA z v k = v k := by
  obtain ⟨ω, hω, rfl⟩ :=
    (coxeterMatrix hA).toCoxeterSystem.mem_parabolic_iff_exists_wordProd_eq.1 hz
  clear hz
  induction ω generalizing v with
  | nil => simp
  | cons j ω ih =>
    rw [CoxeterSystem.wordProd_cons, weylAction_mul_apply,
      weylAction_simple_apply_of_ne hA j _ fun e => hk (by rw [e]; exact hω j List.mem_cons_self),
      ih _ (fun i hi => hω i (List.mem_cons_of_mem j hi))]

include hA in
theorem sq_add_sq_eq_one_of_support (hsymm : ∀ i j, A i j = A j i) {i j : I} (hij : i ≠ j)
    {γ : I → ℤ} (hγ : γ ∈ roots hA ∅) (hsupp : ∀ k, k ≠ i → k ≠ j → γ k = 0) :
    γ i ^ 2 + A i j * γ i * γ j + γ j ^ 2 = 1 := by
  have e : γ = (0 + γ i • Pi.single i 1) + γ j • Pi.single j 1 := by
    funext k
    by_cases hki : k = i
    · subst hki
      simp [Pi.single_eq_of_ne hij]
    · by_cases hkj : k = j
      · subst hkj
        simp [Pi.single_eq_of_ne hki]
      · simp [Pi.single_eq_of_ne hki, Pi.single_eq_of_ne hkj, hsupp k hki hkj]
  have h2 := cartanForm_eq_two hA hsymm hγ
  rw [e, cartanForm_add_smul_single hsymm (hA.apply_self j),
    cartanForm_add_smul_single hsymm (hA.apply_self i)] at h2
  simp only [cartanForm, Pi.zero_apply, map_zero, mul_zero, Finset.sum_const_zero, zero_add,
    map_zsmul, coroot_single, smul_eq_mul] at h2
  rw [hsymm j i] at h2
  linarith

include hA in
theorem exists_weylAction_pair (hpd : (A.map (Int.cast : ℤ → ℚ)).PosDef) {γ δ : I → ℤ}
    (hγ : γ ∈ roots hA ∅) (hδ : δ ∈ roots hA ∅) (hγδ : γ + δ ∈ roots hA ∅) :
    ∃ (w : (coxeterMatrix hA).Group) (a b : I), A a b = -1 ∧
      weylAction hA w (Pi.single a 1) = γ ∧ weylAction hA w (Pi.single b 1) = δ := by
  classical
  have hsymm := cartan_symm_of_posDef hpd
  set cs := (coxeterMatrix hA).toCoxeterSystem
  obtain ⟨u, J₂, hcard, hsupp⟩ := exists_weylAction_support_subset hA ∅ hγ hδ
  have hsγ : ∀ k ∉ J₂, weylAction hA u γ k = 0 :=
    hsupp γ hγ ⟨1, 0, fun k => by simp⟩
  have hsδ : ∀ k ∉ J₂, weylAction hA u δ k = 0 :=
    hsupp δ hδ ⟨0, 1, fun k => by simp⟩
  have hsγδ : ∀ k ∉ J₂, weylAction hA u (γ + δ) k = 0 :=
    hsupp (γ + δ) hγδ ⟨1, 1, fun k => by simp⟩
  obtain ⟨w', l, hw'⟩ : ∃ w' l, weylAction hA u γ = weylAction hA w' (Pi.single l 1) := by
    rcases hγ with ⟨w, l, rfl⟩ | ⟨w, l, hl, -⟩
    · exact ⟨u * w, l, by rw [weylAction_mul_apply]⟩
    · exact absurd hl (Set.notMem_empty l)
  obtain ⟨z, hz, m, hm, hzm⟩ := exists_parabolic_of_support hA (↑J₂) w' l
    (fun k hk => by rw [← hw']; exact hsγ k hk)
  rw [← hw'] at hzm
  set δ'' := weylAction hA z (weylAction hA u δ) with hδ''
  have hδ''r : δ'' ∈ roots hA ∅ := weylAction_mem_roots hA z (weylAction_mem_roots hA u hδ)
  have hsδ'' : ∀ k ∉ J₂, δ'' k = 0 := fun k hk => by
    rw [hδ'', weylAction_apply_of_mem_parabolic hA hz _ (by exact_mod_cast hk), hsδ k hk]
  have hsum : Pi.single m 1 + δ'' = weylAction hA z (weylAction hA u (γ + δ)) := by
    rw [map_add (weylAction hA u), map_add (weylAction hA z), hzm]
  have hsumr : Pi.single m 1 + δ'' ∈ roots hA ∅ := by
    rw [hsum]
    exact weylAction_mem_roots hA z (weylAction_mem_roots hA u hγδ)
  have hssum : ∀ k ∉ J₂, ((Pi.single m 1 : I → ℤ) + δ'') k = 0 := fun k hk => by
    rw [hsum, weylAction_apply_of_mem_parabolic hA hz _ (by exact_mod_cast hk), hsγδ k hk]
  obtain ⟨j, hjm, hj⟩ : ∃ j, j ≠ m ∧ δ'' j ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hd : δ'' = δ'' m • Pi.single m 1 := by
      funext k
      by_cases hk : k = m
      · subst hk
        simp
      · simp [Pi.single_eq_of_ne hk, hcon k hk]
    have h1 := cartanForm_eq_two hA hsymm hδ''r
    have h2 := cartanForm_eq_two hA hsymm hsumr
    rw [hd] at h1 h2
    rw [show Pi.single m 1 + δ'' m • Pi.single m 1 = (1 + δ'' m) • (Pi.single m 1 : I → ℤ) by
      rw [add_smul, one_smul]] at h2
    rw [show δ'' m • (Pi.single m 1 : I → ℤ) = 0 + δ'' m • Pi.single m 1 by rw [zero_add],
      cartanForm_add_smul_single hsymm (hA.apply_self m)] at h1
    rw [show (1 + δ'' m) • (Pi.single m 1 : I → ℤ) = 0 + (1 + δ'' m) • Pi.single m 1 by
      rw [zero_add], cartanForm_add_smul_single hsymm (hA.apply_self m)] at h2
    simp only [cartanForm, Pi.zero_apply, map_zero, Finset.sum_const_zero, mul_zero,
      zero_add] at h1 h2
    nlinarith
  have hjJ : j ∈ J₂ := by
    by_contra hjJ
    exact hj (hsδ'' j hjJ)
  have hJ₂ : ∀ k, k ≠ m → k ≠ j → k ∉ J₂ := by
    intro k hkm hkj hkJ
    have h3 : ({m, j, k} : Finset I).card = 3 := by
      rw [Finset.card_insert_of_notMem (by simp [hjm.symm, (Ne.symm hkm)]),
        Finset.card_pair (Ne.symm hkj)]
    have h4 : ({m, j, k} : Finset I) ⊆ J₂ := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl <;> assumption
    have := Finset.card_le_card h4
    omega
  have hs1 := sq_add_sq_eq_one_of_support hA hsymm hjm.symm hδ''r
    fun k hkm hkj => hsδ'' k (hJ₂ k hkm hkj)
  have hs2 := sq_add_sq_eq_one_of_support hA hsymm hjm.symm hsumr
    fun k hkm hkj => hssum k (hJ₂ k hkm hkj)
  simp only [Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne hjm] at hs2
  have hAle : A m j ≤ 0 := hA.apply_le_zero_of_ne hjm.symm
  have hAge : -1 ≤ A m j := by
    have := neg_one_le_coroot hA hpd (Or.inl ⟨1, j, by simp⟩ : Pi.single j 1 ∈ roots hA ∅)
      (k := m) (fun e => by
        have := congrFun e j
        simp [Pi.single_eq_of_ne hjm] at this)
    rwa [coroot_single] at this
  have hA1 : A m j = -1 := by
    rcases (show A m j = 0 ∨ A m j = -1 by omega) with h0 | h1
    · rw [h0] at hs1 hs2
      have h3 : 2 * δ'' m + 1 = 0 := by nlinarith
      omega
    · exact h1
  rw [hA1] at hs1 hs2
  have hcd : (δ'' m = 0 ∧ δ'' j = 1) ∨ (δ'' m = -1 ∧ δ'' j = -1) := by
    have hd : δ'' j = 1 + 2 * δ'' m := by nlinarith
    rw [hd] at hs1
    have hc : δ'' m * (δ'' m + 1) = 0 := by nlinarith
    rcases mul_eq_zero.1 hc with h0 | h0
    · left
      exact ⟨h0, by rw [hd, h0]; norm_num⟩
    · right
      refine ⟨by omega, by rw [hd]; omega⟩
  have hδ''eq : ∀ a b : ℤ, δ'' m = a → δ'' j = b →
      δ'' = a • Pi.single m 1 + b • Pi.single j 1 := by
    intro a b ha hb
    funext k
    by_cases hkm : k = m
    · subst hkm
      simp [Pi.single_eq_of_ne hjm.symm, ha]
    · by_cases hkj : k = j
      · subst hkj
        simp [Pi.single_eq_of_ne hjm, hb]
      · simp [Pi.single_eq_of_ne hkm, Pi.single_eq_of_ne hkj, hsδ'' k (hJ₂ k hkm hkj)]
  have hzγ : weylAction hA z⁻¹ (Pi.single m 1) = weylAction hA u γ := by
    rw [← hzm, weylAction_inv_apply_apply]
  have hzδ : weylAction hA z⁻¹ δ'' = weylAction hA u δ := by
    rw [hδ'', weylAction_inv_apply_apply]
  rcases hcd with ⟨h1, h2⟩ | ⟨h1, h2⟩
  ·
    have hd := hδ''eq 0 1 h1 h2
    simp only [zero_smul, one_smul, zero_add] at hd
    refine ⟨u⁻¹ * z⁻¹, m, j, hA1, ?_, ?_⟩
    · rw [weylAction_mul_apply, hzγ, weylAction_inv_apply_apply]
    · rw [weylAction_mul_apply, ← hd, hzδ, weylAction_inv_apply_apply]
  ·
    have hd := hδ''eq (-1) (-1) h1 h2
    have hAjm : A j m = -1 := by rw [hsymm]; exact hA1
    have hr : ∀ a b : I, weylAction hA (cs.simple a) (Pi.single b 1) =
        Pi.single b 1 - A a b • Pi.single a 1 := fun a b => by
      rw [weylAction_simple, reflection_apply_coroot, coroot_single]
    have hy1 : weylAction hA (cs.simple j * cs.simple m) (Pi.single j 1) = Pi.single m 1 := by
      rw [weylAction_mul_apply, hr m j, map_sub, map_zsmul, hr j j, hr j m, hA1, hAjm,
        hA.apply_self]
      abel
    have hy2 : weylAction hA (cs.simple j * cs.simple m) (Pi.single m 1) =
        -(Pi.single m 1 + Pi.single j 1) := by
      rw [weylAction_mul_apply, hr m m, map_sub, map_zsmul, hr j m, hAjm, hA.apply_self]
      abel
    refine ⟨u⁻¹ * z⁻¹ * (cs.simple j * cs.simple m), j, m, hAjm, ?_, ?_⟩
    · rw [weylAction_mul_apply, hy1, weylAction_mul_apply, hzγ, weylAction_inv_apply_apply]
    · rw [weylAction_mul_apply, hy2, weylAction_mul_apply,
        show -(Pi.single m 1 + Pi.single j 1 : I → ℤ) = δ'' by
          rw [hd]; simp only [neg_smul, one_smul, neg_add_rev]; abel,
        hzδ, weylAction_inv_apply_apply]


include hA in
theorem exists_sub_single_mem_roots (hpd : (A.map (Int.cast : ℤ → ℚ)).PosDef) {β : I → ℤ}
    (hβ : β ∈ roots hA ∅) (hβ0 : 0 ≤ β) (hns : ∀ k, β ≠ Pi.single k 1) :
    ∃ l, β - Pi.single l 1 ∈ roots hA ∅ ∧ 0 ≤ β - Pi.single l 1 := by
  have hsymm := cartan_symm_of_posDef hpd
  have hq := cartanForm_eq_two hA hsymm hβ
  have hβ0' : ∀ m, 0 ≤ β m := fun m => by simpa using hβ0 m
  obtain ⟨l, hβl, hcl⟩ : ∃ l, 0 < β l ∧ 0 < coroot A l β := by
    by_contra hcon
    push Not at hcon
    have h1 : cartanForm A β ≤ 0 := Finset.sum_nonpos fun m _ => by
      rcases (hβ0' m).lt_or_eq with hpos | hzero
      · nlinarith [hcon m hpos]
      · rw [← hzero, zero_mul]
    omega
  have hcl1 : coroot A l β = 1 := le_antisymm (coroot_le_one hA hpd hβ (hns l)) hcl
  refine ⟨l, ?_, fun i => ?_⟩
  · have e : weylAction hA ((coxeterMatrix hA).toCoxeterSystem.simple l) β =
        β - Pi.single l 1 := by
      rw [weylAction_simple, reflection_apply_coroot, hcl1, one_smul]
    rw [← e]
    exact weylAction_mem_roots hA _ hβ
  · by_cases hil : i = l
    · subst hil
      simp only [Pi.sub_apply, Pi.single_eq_same, Pi.zero_apply]
      omega
    · simp [Pi.single_eq_of_ne hil, hβ0' i]

include hA in
theorem weylAction_nonpos_of_forall_length_le {w₀ : (coxeterMatrix hA).Group}
    (hw₀ : ∀ w, (coxeterMatrix hA).toCoxeterSystem.length w ≤
      (coxeterMatrix hA).toCoxeterSystem.length w₀) {γ : I → ℤ} (hγ0 : 0 ≤ γ) :
    weylAction hA w₀ γ ≤ 0 := by
  have hdesc : ∀ i, weylAction hA w₀ (Pi.single i 1) ≤ 0 := fun i => by
    refine (isRightDescent_iff hA w₀ i).1 (by_contra fun hi => ?_)
    have h := (coxeterMatrix hA).toCoxeterSystem.not_isRightDescent_iff.mp hi
    have := hw₀ (w₀ * (coxeterMatrix hA).toCoxeterSystem.simple i)
    omega
  have hsum : weylAction hA w₀ γ = ∑ j, γ j • weylAction hA w₀ (Pi.single j 1) := by
    conv_lhs => rw [← sum_smul_single γ]
    simp only [map_sum, map_zsmul]
  intro k
  rw [hsum, Finset.sum_apply]
  refine Finset.sum_nonpos fun j _ => ?_
  rw [Pi.smul_apply, smul_eq_mul]
  exact mul_nonpos_of_nonneg_of_nonpos (hγ0 j) (hdesc j k)

include hA in
theorem exists_weylAction_eq_neg_single (hpd : (A.map (Int.cast : ℤ → ℚ)).PosDef)
    {w₀ : (coxeterMatrix hA).Group}
    (hw₀ : ∀ w, (coxeterMatrix hA).toCoxeterSystem.length w ≤
      (coxeterMatrix hA).toCoxeterSystem.length w₀) (k : I) :
    ∃ m, weylAction hA w₀ (Pi.single k 1) = -Pi.single m 1 := by
  set cs := (coxeterMatrix hA).toCoxeterSystem
  have hroot : ∀ (w : (coxeterMatrix hA).Group) i,
      weylAction hA w (Pi.single i 1) ∈ roots hA ∅ := fun w i => Or.inl ⟨w, i, rfl⟩
  have hw₀' : ∀ w, cs.length w ≤ cs.length w₀⁻¹ := fun w => by
    rw [CoxeterSystem.length_inv]
    exact hw₀ w
  set β := -weylAction hA w₀ (Pi.single k 1) with hβ
  have hβr : β ∈ roots hA ∅ := by
    have e : β = weylAction hA (w₀ * cs.simple k) (Pi.single k 1) := by
      rw [weylAction_mul_apply, weylAction_simple_single, map_neg]
    rw [e]
    exact hroot _ _
  have hβ0 : 0 ≤ β := by
    have := weylAction_nonpos_of_forall_length_le hA hw₀ (γ := Pi.single k 1)
      (fun i => by simp only [Pi.single_apply]; split_ifs <;> norm_num)
    intro i
    simp only [hβ, Pi.neg_apply, Pi.zero_apply, neg_nonneg]
    exact this i
  by_cases hs : ∃ m, β = Pi.single m 1
  · obtain ⟨m, hm⟩ := hs
    refine ⟨m, ?_⟩
    rw [← hm, hβ, neg_neg]
  push Not at hs
  exfalso
  obtain ⟨l, hl, hl0⟩ := exists_sub_single_mem_roots hA hpd hβr hβ0 hs
  have e : Pi.single k 1 = -weylAction hA w₀⁻¹ (β - Pi.single l 1) +
      -weylAction hA w₀⁻¹ (Pi.single l 1) := by
    rw [← neg_add, ← map_add, sub_add_cancel, hβ, map_neg, weylAction_inv_apply_apply, neg_neg]
  have h1 : 0 ≤ -weylAction hA w₀⁻¹ (β - Pi.single l 1) := fun i => by
    have := weylAction_nonpos_of_forall_length_le hA hw₀' hl0 i
    simp only [Pi.neg_apply, Pi.zero_apply, neg_nonneg]
    exact this
  have h2 : 0 ≤ -weylAction hA w₀⁻¹ (Pi.single l 1) := fun i => by
    have := weylAction_nonpos_of_forall_length_le hA hw₀' (γ := Pi.single l 1)
      (fun i => by simp only [Pi.single_apply]; split_ifs <;> norm_num) i
    simp only [Pi.neg_apply, Pi.zero_apply, neg_nonneg]
    exact this
  have hne1 : -weylAction hA w₀⁻¹ (β - Pi.single l 1) ≠ 0 := by
    rw [neg_ne_zero]
    exact ne_zero_of_mem_roots hA ∅ (weylAction_mem_roots hA _ hl)
  have hne2 : -weylAction hA w₀⁻¹ (Pi.single l 1) ≠ 0 := by
    rw [neg_ne_zero]
    exact weylAction_single_ne_zero hA _ l
  have h3 := one_le_sum_of_nonneg h1 hne1
  have h4 := one_le_sum_of_nonneg h2 hne2
  have h5 : ∑ i, (Pi.single k 1 : I → ℤ) i = 1 := by simp
  rw [e] at h5
  simp only [Pi.add_apply, Finset.sum_add_distrib] at h5
  omega

end FiniteType

end CFSG.Timmesfeld.ARS
