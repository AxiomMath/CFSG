module

public import CFSG.RankThree.Classical.SteinbergBJOrthogonalHighWitt
public import CFSG.ClassicalGroups.Orthogonal.RootGroupStabilizerFour

public section

namespace CFSG.RankThree.GF2n.Smith81

open Module QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.UnbalancedCatalog (even_finrank_of_charTwo exists_hypPairs_normal
  polar_self_charTwo)
open scoped commutatorElement

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

private theorem exists_family_four_le [Finite K] [CharP K 2] [FiniteDimensional K V]
    (hQ : (polarBilin Q).Nondegenerate) (h4 : 4 ≤ finrank K V) :
    ∃ (P : ℕ → HypPair Q) (r : ℕ), 1 ≤ r ∧
      (∀ i j, i < r → j < r → i ≠ j → (P i).Orth (P j)) ∧
      (∀ x ∈ tailSpace P r, Q x = 0 → x = 0) ∧
      (finrank K (tailSpace P r) = 0 ∨ finrank K (tailSpace P r) = 2) := by
  classical
  obtain ⟨n₀, hn₀⟩ := even_finrank_of_charTwo Q hQ
  have hfin : finrank K (⊤ : Submodule K V) = 2 * n₀ := by rw [finrank_top]; omega
  have ext : ∀ (m : ℕ) (R : Fin m → HypPair Q), 1 ≤ m → (∀ i j, i ≠ j → (R i).Orth (R j)) →
      ∃ P : ℕ → HypPair Q, (∀ i j, i < m → j < m → i ≠ j → (P i).Orth (P j)) ∧
        ∀ i (hi : i < m), P i = R ⟨i, hi⟩ := by
    intro m R hm hRo
    refine ⟨fun i => if h : i < m then R ⟨i, h⟩ else R ⟨0, hm⟩, fun i j hi hj hij => ?_,
      fun i hi => by simp [hi]⟩
    simp only [hi, hj, dite_true]
    exact hRo _ _ fun h => hij (by simpa using congrArg Fin.val h)
  rcases exists_hypPairs_normal n₀ ⊤ (polarNondegOn_top hQ) hfin with
    ⟨R, -, hRo⟩ | ⟨m, hm, R, u, v, -, hRo, -, -, huv, hu, huv0, hroot⟩
  · obtain ⟨P, hPo, -⟩ := ext n₀ R (by omega) hRo
    have hdim := CFSG.RankThree.Classical.finrank_tailSpace_add hPo n₀ le_rfl
    have h0 : finrank K (tailSpace P n₀) = 0 := by omega
    refine ⟨P, n₀, by omega, hPo, fun x hx _ => ?_, Or.inl h0⟩
    have := Submodule.finrank_eq_zero.mp h0
    rw [this] at hx
    exact (Submodule.mem_bot K).mp hx
  · obtain ⟨P, hPo, hPR⟩ := ext m R (by omega) hRo
    have hdim := CFSG.RankThree.Classical.finrank_tailSpace_add hPo m le_rfl
    have h2 : finrank K (tailSpace P m) = 2 := by omega
    have hu' : u ∈ tailSpace P m := mem_tailSpace.mpr fun i hi => by
      rw [hPR i hi]; exact HypPair.mem_perp.mp (huv ⟨i, hi⟩).1
    have hv' : v ∈ tailSpace P m := mem_tailSpace.mpr fun i hi => by
      rw [hPR i hi]; exact HypPair.mem_perp.mp (huv ⟨i, hi⟩).2
    have hli : LinearIndependent K ![u, v] := by
      rw [LinearIndependent.pair_iff]
      intro s t hst
      have h1 := congrArg (polar Q u) hst
      rw [polar_add_right, polar_smul_right_eq, polar_smul_right_eq, polar_zero_right,
        polar_self_charTwo Q u, mul_zero, zero_add] at h1
      have ht : t = 0 := (mul_eq_zero.mp h1).resolve_right huv0
      subst ht
      rw [zero_smul, add_zero] at hst
      have hu0 : u ≠ 0 := by
        rintro rfl
        rw [map_zero] at hu
        exact zero_ne_one hu
      exact ⟨(smul_eq_zero.mp hst).resolve_right hu0, rfl⟩
    have hspan : Submodule.span K {u, v} = tailSpace P m := by
      refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
      · rw [Submodule.span_le]
        intro y hy
        rcases hy with rfl | hy
        · exact hu'
        · rw [Set.mem_singleton_iff] at hy
          rw [hy]
          exact hv'
      · rw [h2]
        have h := finrank_span_eq_card hli
        rwa [Matrix.range_cons_cons_empty, Fintype.card_fin] at h
    refine ⟨P, m, by omega, hPo, fun x hx hQx => ?_, Or.inr h2⟩
    rw [← hspan] at hx
    obtain ⟨s, t, rfl⟩ := Submodule.mem_span_pair.mp hx
    rw [QuadraticMap.map_add Q, map_smul_eq_sq, map_smul_eq_sq, hu, polar_smul_left_eq,
      polar_smul_right_eq, mul_one] at hQx
    by_cases ht : t = 0
    · subst ht
      have hs : s ^ 2 = 0 := by rw [← hQx]; ring
      rw [pow_eq_zero_iff two_ne_zero] at hs
      subst hs
      simp
    · exfalso
      apply hroot (s / t)
      have ht2 : t ^ 2 ≠ 0 := pow_ne_zero 2 ht
      field_simp
      linear_combination hQx

section Reflections

private theorem reflect_smul_of_ne_zero {c : K} (hc : c ≠ 0) (v : V) :
    reflect Q (c • v) = reflect Q v := by
  by_cases hv : Q v = 0
  · have : Q (c • v) = 0 := by rw [map_smul_eq_sq, hv, mul_zero]
    rw [reflect_of_map_eq_zero this, reflect_of_map_eq_zero hv]
  · have hcv : Q (c • v) ≠ 0 := by
      rw [map_smul_eq_sq]
      exact mul_ne_zero (pow_ne_zero 2 hc) hv
    refine LinearEquiv.ext fun x => ?_
    rw [reflect_apply hcv, reflect_apply hv, polar_smul_left_eq, map_smul_eq_sq, smul_smul]
    have e : c * polar Q v x / (c ^ 2 * Q v) * c = polar Q v x / Q v := by field_simp
    rw [e]

private theorem exists_smul_map_eq_one [Finite K] [CharP K 2] {a : V} (ha : Q a ≠ 0) :
    ∃ c : K, c ≠ 0 ∧ Q (c • a) = 1 := by
  obtain ⟨μ, hμ⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K 2) (Q a)⁻¹
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hμ
    exact inv_ne_zero ha hμ
  refine ⟨μ, hμ0, ?_⟩
  rw [map_smul_eq_sq, pow_two, ← hμ, inv_mul_cancel₀ ha]

private theorem reflect_mul_reflect_mem_elementaryGroup_of_polar_eq_zero (h2 : (2 : K) = 0)
    {a w : V} (ha : Q a = 1) (hw : Q w = 1) (haw : polar Q a w = 0) :
    reflect Q a * reflect Q w ∈ elementaryGroup Q := by
  have hwa : polar Q w a = 0 := by rw [polar_comm, haw]
  have h2v : ∀ x : V, x + x = 0 := fun x => by rw [← two_smul K x, h2, zero_smul]
  have hu : Q (a + w) = 0 := by
    rw [QuadraticMap.map_add Q, ha, hw, haw, add_zero]
    linear_combination h2
  have hua : polar Q (a + w) a = 0 := by
    rw [polar_add_left, polar_self_eq_two_mul, h2, zero_mul, hwa, add_zero]
  have key := eichler_eq_reflect_mul_reflect h2 hu hua ha
  rw [← add_assoc, h2v a, zero_add] at key
  rw [← key]
  exact eichler_mem_elementaryGroup Q _ _

variable [FiniteDimensional K V]

private theorem exists_map_ne_zero_polar_eq_zero (hQ : (polarBilin Q).Nondegenerate)
    (hd : 4 ≤ finrank K V) {a b : V} (hab : polar Q a b ≠ 0) :
    ∃ w, Q w ≠ 0 ∧ polar Q a w = 0 ∧ polar Q b w = 0 := by
  set f := (polarBilin Q a).prod (polarBilin Q b)
  have hmem : ∀ x, x ∈ LinearMap.ker f ↔ polar Q a x = 0 ∧ polar Q b x = 0 := fun x => by
    simp [f]
  by_contra! hne
  have hQ0 : ∀ x ∈ LinearMap.ker f, Q x = 0 := fun x hx => by
    obtain ⟨h1, h2⟩ := (hmem x).mp hx
    by_contra h0
    exact hne x h0 h1 h2
  have hle : LinearMap.ker f ≤
      LinearMap.BilinForm.orthogonal (polarBilin Q) (LinearMap.ker f) := by
    intro a' ha'
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro b' hb'
    have hs : b' + a' ∈ LinearMap.ker f := Submodule.add_mem _ hb' ha'
    rw [polarBilin_apply_apply, polar, hQ0 _ hs, hQ0 _ hb', hQ0 _ ha', sub_zero, sub_zero]
  have h1 := Submodule.finrank_mono hle
  rw [LinearMap.BilinForm.finrank_orthogonal hQ] at h1
  have h2 := LinearMap.finrank_range_add_finrank_ker f
  have h3 : finrank K (LinearMap.range f) ≤ 2 :=
    (Submodule.finrank_le _).trans (by simp)
  have heq : LinearMap.ker f =
      LinearMap.BilinForm.orthogonal (polarBilin Q) (LinearMap.ker f) := by
    refine Submodule.eq_of_le_of_finrank_le hle ?_
    rw [LinearMap.BilinForm.finrank_orthogonal hQ]
    omega
  have haorth : a ∈ LinearMap.BilinForm.orthogonal (polarBilin Q) (LinearMap.ker f) := by
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro y hy
    have := ((hmem y).mp hy).1
    simpa [polarBilin_apply_apply, polar_comm Q y a] using this
  rw [← heq, hmem] at haorth
  have h := haorth.2
  rw [polar_comm] at h
  exact hab h

private theorem reflect_mul_reflect_mem_elementaryGroup [Finite K] [CharP K 2]
    (hQ : (polarBilin Q).Nondegenerate) (hd : 4 ≤ finrank K V) {a b : V} (ha : Q a ≠ 0)
    (hb : Q b ≠ 0) : reflect Q a * reflect Q b ∈ elementaryGroup Q := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  obtain ⟨c, hc0, hc⟩ := exists_smul_map_eq_one ha
  obtain ⟨c', hc'0, hc'⟩ := exists_smul_map_eq_one hb
  rw [← reflect_smul_of_ne_zero hc0 a, ← reflect_smul_of_ne_zero hc'0 b]
  set a' := c • a
  set b' := c' • b
  by_cases hab : polar Q a' b' = 0
  · exact reflect_mul_reflect_mem_elementaryGroup_of_polar_eq_zero h2 hc hc' hab
  · obtain ⟨w, hw, haw, hbw⟩ := exists_map_ne_zero_polar_eq_zero hQ hd hab
    obtain ⟨c'', hc''0, hc''⟩ := exists_smul_map_eq_one hw
    have haw' : polar Q a' (c'' • w) = 0 := by rw [polar_smul_right_eq, haw, mul_zero]
    have hbw' : polar Q (c'' • w) b' = 0 := by
      rw [polar_comm, polar_smul_right_eq, hbw, mul_zero]
    have e : reflect Q a' * reflect Q b' =
        (reflect Q a' * reflect Q (c'' • w)) * (reflect Q (c'' • w) * reflect Q b') := by
      calc reflect Q a' * reflect Q b'
          = reflect Q a' * (reflect Q (c'' • w) * reflect Q (c'' • w)) * reflect Q b' := by
            rw [reflect_mul_self, mul_one]
        _ = _ := by group
    rw [e]
    exact mul_mem (reflect_mul_reflect_mem_elementaryGroup_of_polar_eq_zero h2 hc hc'' haw')
      (reflect_mul_reflect_mem_elementaryGroup_of_polar_eq_zero h2 hc'' hc' hbw')

end Reflections

section Main

open CFSG.RankThree.OrthogonalInvolutions (omegaGroup mem_omegaGroup)

variable [Finite K] [CharP K 2] [FiniteDimensional K V]

theorem omegaGroup_le_elementaryGroup_of_four_le (hQ : (polarBilin Q).Nondegenerate)
    (h4 : 4 ≤ finrank K V) : omegaGroup Q hQ ≤ elementaryGroup Q := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  obtain ⟨P, r, hr, hP, hA, hdim⟩ := exists_family_four_le hQ h4
  have hA' : ∀ x ∈ tailSpace P r, x ≠ 0 → ∀ y ∈ tailSpace P r, polar Q x y = 0 →
      ∃ c : K, y = c • x := by
    intro x hx hx0 y hy hxy
    rcases hdim with h0 | h2''
    · exact absurd ((Submodule.finrank_eq_zero.1 h0) ▸ hx : x ∈ (⊥ : Submodule K V))
        (by rw [Submodule.mem_bot]; exact hx0)
    · exact eq_smul_of_polar_eq_zero_of_finrank_two h2'' (polarNondegOn_tailSpace hP hQ le_rfl)
        hx hx0 (by rw [polar_self_eq_two_mul, h2, zero_mul]) hy hxy
  have hgen := orthogonalGroup_le_closure_of_two_eq_zero hP hQ h2 hA hA' hr
  set O := TauCeti.QuadraticMap.orthogonalGroup Q with hOdef
  set E := elementaryGroup Q with hEdef
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := K) (by omega)
  obtain ⟨v₀, hv₀⟩ := CFSG.RankThree.OrthogonalInvolutions.exists_map_ne_zero hQ
  set r₀ := reflect Q v₀ with hr₀
  have hr₀O : r₀ ∈ O := reflect_mem_orthogonalGroup Q v₀
  have hr₀2 : r₀ * r₀ = 1 := reflect_mul_self Q v₀
  have hr₀inv : r₀⁻¹ = r₀ := reflect_inv Q v₀
  have hEΩ : E ≤ omegaGroup Q hQ := elementaryGroup_le_omegaGroup hQ
  have hr₀Ω : r₀ ∉ omegaGroup Q hQ := by
    intro h
    let _ : Invertible (Q v₀) := invertibleOfNonzero hv₀
    have h1 := CFSG.RankThree.OrthogonalInvolutions.finrank_commSpace_reflection hQ v₀
    rw [← reflect_eq_reflection] at h1
    have h2' := (mem_omegaGroup.mp h).2
    rw [h1] at h2'
    exact Nat.not_even_one h2'
  have hc : ∀ n ∈ E, r₀⁻¹ * n * r₀ ∈ E := fun n hn => by
    have := conj_mem_elementaryGroup (inv_mem hr₀O) hn
    rwa [inv_inv] at this
  have hdich : ∀ g ∈ O, g ∈ E ∨ g * r₀ ∈ E := by
    intro g hg
    refine Subgroup.closure_induction (p := fun g _ => g ∈ O ∧ (g ∈ E ∨ g * r₀ ∈ E))
      (fun x hx => ?_) ⟨one_mem _, Or.inl (one_mem _)⟩ (fun x y _ _ hx hy => ?_)
      (fun x _ hx => ?_) (hgen hg) |>.2
    · rcases hx with ⟨v, rfl⟩ | hx
      · refine ⟨reflect_mem_orthogonalGroup Q v, ?_⟩
        by_cases hv : Q v = 0
        · left
          rw [reflect_of_map_eq_zero hv]
          exact one_mem _
        · right
          exact reflect_mul_reflect_mem_elementaryGroup hQ h4 hv hv₀
      · exact ⟨elementaryGroup_le_orthogonalGroup Q hx, Or.inl hx⟩
    · obtain ⟨hxO, hx⟩ := hx
      obtain ⟨hyO, hy⟩ := hy
      refine ⟨mul_mem hxO hyO, ?_⟩
      rcases hx with hx | hx <;> rcases hy with hy | hy
      · exact Or.inl (mul_mem hx hy)
      · right
        rw [mul_assoc]
        exact mul_mem hx hy
      · right
        have : x * y * r₀ = x * r₀ * (r₀⁻¹ * y * r₀) := by group
        rw [this]
        exact mul_mem hx (hc y hy)
      · left
        have h11 : r₀⁻¹ * r₀⁻¹ = 1 := by rw [← mul_inv_rev, hr₀2, inv_one]
        have : x * y = x * r₀ * (r₀⁻¹ * (y * r₀) * r₀) * (r₀⁻¹ * r₀⁻¹) := by group
        rw [this, h11, mul_one]
        exact mul_mem hx (hc _ hy)
    · obtain ⟨hxO, hx⟩ := hx
      refine ⟨inv_mem hxO, ?_⟩
      rcases hx with hx | hx
      · exact Or.inl (inv_mem hx)
      · right
        have hc' := conj_mem_elementaryGroup (inv_mem hr₀O) hx
        rw [inv_inv] at hc'
        have : x⁻¹ * r₀ = (r₀⁻¹ * (x * r₀) * r₀⁻¹)⁻¹ := by group
        rw [this, hr₀inv]
        exact inv_mem (by simpa [hr₀inv] using hc')
  intro g hg
  rcases hdich g (CFSG.RankThree.OrthogonalInvolutions.omegaGroup_le Q hQ hg) with h | h
  · exact h
  · exfalso
    apply hr₀Ω
    have : r₀ = g⁻¹ * (g * r₀) := by group
    rw [this]
    exact mul_mem (inv_mem hg) (hEΩ h)

end Main

end CFSG.RankThree.GF2n.Smith81
