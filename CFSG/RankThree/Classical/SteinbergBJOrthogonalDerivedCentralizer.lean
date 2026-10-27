module

public import CFSG.LocalAnalysis.ComponentInitial.QuadraticLowDimension
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogQuadraticNormalForms

public section

namespace CFSG.RankThree.Classical

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

variable {K W : Type*} [Field K] [AddCommGroup W] [Module K W] {Q : QuadraticForm K W}

theorem eichler_mem_commutator_orthogonalGroup {c : K} (hc0 : c ≠ 0) (hc1 : c ≠ 1)
    (P : HypPair Q) {w : W} (hw : w ∈ P.perp) :
    eichler Q P.e w ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup Q,
      TauCeti.QuadraticMap.orthogonalGroup Q⁆ := by
  have hc1' : c - 1 ≠ 0 := sub_ne_zero.mpr hc1
  rw [HypPair.mem_perp] at hw
  set d := reflect Q (P.e + c⁻¹ • P.f) * reflect Q (P.e + P.f) with hd
  have hdO : d ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    mul_mem (reflect_mem_orthogonalGroup Q _) (reflect_mem_orthogonalGroup Q _)
  have hQ1 : Q (P.e + P.f) = 1 := by
    rw [QuadraticMap.map_add Q P.e P.f, P.Q_e, P.Q_f, P.polar_ef, zero_add, zero_add]
  have hQc : Q (P.e + c⁻¹ • P.f) = c⁻¹ := by
    rw [QuadraticMap.map_add Q P.e (c⁻¹ • P.f), map_smul_eq_sq, P.Q_e, P.Q_f, polar_smul_right_eq,
      P.polar_ef]
    ring
  have hs1 : reflect Q (P.e + P.f) P.e = -P.f := by
    rw [reflect_apply (by rw [hQ1]; exact one_ne_zero), hQ1, div_one, polar_add_left, P.polar_ee,
      P.polar_fe, zero_add, one_smul, sub_add_cancel_left]
  have hs2 : reflect Q (P.e + c⁻¹ • P.f) (-P.f) = c • P.e := by
    rw [reflect_apply (by rw [hQc]; exact inv_ne_zero hc0), hQc, polar_neg_right, polar_add_left,
      polar_smul_left_eq, P.polar_ef, P.polar_ff, mul_zero, add_zero, neg_div, div_inv_eq_mul,
      one_mul, neg_smul, sub_neg_eq_add, smul_add, smul_smul, mul_inv_cancel₀ hc0, one_smul]
    abel
  have hde : d P.e = c • P.e := by rw [hd, LinearEquiv.mul_apply, hs1, hs2]
  have hdw : ∀ x : W, polar Q P.e x = 0 → polar Q P.f x = 0 → d x = x := by
    intro x hxe hxf
    have h1 : reflect Q (P.e + P.f) x = x :=
      reflect_apply_of_polar_eq_zero (by rw [polar_add_left, hxe, hxf, add_zero])
    have h2 : reflect Q (P.e + c⁻¹ • P.f) x = x := reflect_apply_of_polar_eq_zero
      (by rw [polar_add_left, polar_smul_left_eq, hxe, hxf, mul_zero, add_zero])
    rw [hd, LinearEquiv.mul_apply, h1, h2]
  set w' := (c - 1)⁻¹ • w with hw'
  have hw'e : polar Q P.e w' = 0 := by rw [hw', polar_smul_right_eq, hw.1, mul_zero]
  have hw'f : polar Q P.f w' = 0 := by rw [hw', polar_smul_right_eq, hw.2, mul_zero]
  have hcomm : ⁅d, eichler Q P.e w'⁆ = eichler Q P.e w := by
    have hconj : d * eichler Q P.e w' * d⁻¹ = eichler Q P.e (c • w') := by
      rw [eichler_conj hdO, hde, hdw w' hw'e hw'f, eichler_smul_left]
    have hcw : polar Q P.e (c • w') = 0 := by rw [polar_smul_right_eq, hw'e, mul_zero]
    have hnw : polar Q P.e (-w') = 0 := by rw [polar_neg_right, hw'e, neg_zero]
    have hsum : c • w' + -w' = w := by
      rw [hw', smul_smul, ← neg_smul, ← add_smul]
      have : c * (c - 1)⁻¹ + -(c - 1)⁻¹ = 1 := by
        field_simp
        ring
      rw [this, one_smul]
    rw [commutatorElement_def, hconj, eichler_inv hw'e, eichler_mul hcw hnw, hsum]
  rw [← hcomm]
  exact Subgroup.commutator_mem_commutator hdO (eichler_mem_orthogonalGroup Q P.e w')

theorem commute_orthElementaryMap_identity (Q : QuadraticForm K W) (M : W →ₗ[K] W) (u w : W)
    (a : K) (h : M ∘ₗ orthElementaryMap Q u (a • w) = orthElementaryMap Q u (a • w) ∘ₗ M)
    (x : W) :
    a • (polar Q x u • M w - polar Q x w • M u - polar Q (M x) u • w + polar Q (M x) w • u) +
      (a ^ 2 * Q w) • (polar Q (M x) u • u - polar Q x u • M u) = 0 := by
  have hx := LinearMap.congr_fun h x
  simp only [LinearMap.comp_apply, orthElementaryMap_apply, map_add, map_sub, map_smul,
    polar_smul_right_eq, map_smul_eq_sq] at hx
  linear_combination (norm := module) hx

theorem eq_smul_id_of_commute_orthElementaryMap {c : K} (hc0 : c ≠ 0) (hc1 : c ≠ 1)
    (P : HypPair Q) {w₀ : W} (hw₀ : w₀ ∈ P.perp) (hQw₀ : Q w₀ ≠ 0) (M : W →ₗ[K] W)
    (hM : ∀ w ∈ P.perp, ∀ a : K,
      M ∘ₗ orthElementaryMap Q P.e (a • w) = orthElementaryMap Q P.e (a • w) ∘ₗ M ∧
      M ∘ₗ orthElementaryMap Q P.f (a • w) = orthElementaryMap Q P.f (a • w) ∘ₗ M) :
    ∃ l : K, M = l • LinearMap.id := by
  have hc2 : c - c ^ 2 ≠ 0 := by
    rw [show c - c ^ 2 = c * (1 - c) by ring]
    exact mul_ne_zero hc0 (sub_ne_zero.mpr hc1.symm)
  have hcc : (c - c ^ 2) * Q w₀ ≠ 0 := mul_ne_zero hc2 hQw₀
  have key : ∀ u : W, (∀ w ∈ P.perp, ∀ a : K,
      M ∘ₗ orthElementaryMap Q u (a • w) = orthElementaryMap Q u (a • w) ∘ₗ M) →
      (∀ x, polar Q (M x) u • u = polar Q x u • M u) ∧
      ∀ w ∈ P.perp, ∀ x,
        polar Q x u • M w - polar Q x w • M u - polar Q (M x) u • w + polar Q (M x) w • u = 0 := by
    intro u hu
    have hY : ∀ x, polar Q (M x) u • u - polar Q x u • M u = 0 := by
      intro x
      have h1 := commute_orthElementaryMap_identity Q M u w₀ 1 (hu w₀ hw₀ 1) x
      have h2 := commute_orthElementaryMap_identity Q M u w₀ c (hu w₀ hw₀ c) x
      have h3 : ((c - c ^ 2) * Q w₀) • (polar Q (M x) u • u - polar Q x u • M u) = 0 := by
        linear_combination (norm := module) c • h1 - h2
      exact (smul_eq_zero.mp h3).resolve_left hcc
    refine ⟨fun x => sub_eq_zero.mp (hY x), fun w hw x => ?_⟩
    have h1 := commute_orthElementaryMap_identity Q M u w 1 (hu w hw 1) x
    rwa [hY x, smul_zero, add_zero, one_smul] at h1
  obtain ⟨hYe, hXe⟩ := key P.e fun w hw a => (hM w hw a).1
  obtain ⟨hYf, -⟩ := key P.f fun w hw a => (hM w hw a).2
  set l := polar Q (M P.f) P.e with hl
  have hMe : M P.e = l • P.e := by
    have := hYe P.f
    rw [P.polar_fe, one_smul] at this
    exact this.symm
  have hMf : M P.f = l • P.f := by
    have := hYf P.e
    rw [P.polar_ef, one_smul, hMe, polar_smul_left_eq, P.polar_ef, mul_one] at this
    exact this.symm
  have hMw : ∀ w ∈ P.perp, M w = l • w := by
    intro w hw
    have hwf := (HypPair.mem_perp.mp hw).2
    have := hXe w hw P.f
    rw [P.polar_fe, polar_comm Q P.f w, ← polar_comm Q P.f w, hwf, ← hl, hMf,
      polar_smul_left_eq, hwf, mul_zero, one_smul, zero_smul, sub_zero, zero_smul, add_zero,
      sub_eq_zero] at this
    exact this
  refine ⟨l, LinearMap.ext fun x => ?_⟩
  rw [LinearMap.smul_apply, LinearMap.id_apply, P.eq_add_proj x, map_add, map_add, map_smul,
    map_smul, hMe, hMf, hMw _ (P.proj_mem_perp x), smul_add, smul_add, smul_comm l _ P.e,
    smul_comm l _ P.f]

theorem exists_mem_perp_map_ne_zero [FiniteDimensional K W] (hQ : (polarBilin Q).Nondegenerate)
    (hW : 3 ≤ Module.finrank K W) (P : HypPair Q) : ∃ w ∈ P.perp, Q w ≠ 0 := by
  have hne : ∃ u ∈ P.perp, u ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hle : (⊤ : Submodule K W) ≤ Submodule.span K (Set.range ![P.e, P.f]) := by
      intro x _
      rw [P.eq_add_proj x, hcon _ (P.proj_mem_perp x), add_zero]
      exact add_mem (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
        (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩))
    have h1 := Submodule.finrank_mono hle
    rw [finrank_top] at h1
    have h2 := finrank_range_le_card (R := K) ![P.e, P.f]
    rw [Fintype.card_fin, Set.finrank] at h2
    omega
  obtain ⟨u, huU, hu0⟩ := hne
  obtain ⟨y, hyU, huy⟩ := (P.polarNondegOn_perp hQ).exists_polar_ne_zero huU hu0
  by_cases hQu : Q u = 0
  · by_cases hQy : Q y = 0
    · refine ⟨u + y, add_mem huU hyU, ?_⟩
      rw [QuadraticMap.map_add Q u y, hQu, hQy, zero_add, zero_add]
      exact huy
    · exact ⟨y, hyU, hQy⟩
  · exact ⟨u, huU, hQu⟩

theorem nonempty_hypPair_of_finite [Finite K] [FiniteDimensional K W]
    (hQ : (polarBilin Q).Nondegenerate) (hW : 3 ≤ Module.finrank K W) : Nonempty (HypPair Q) := by
  obtain ⟨v, hv0, hQv⟩ : ∃ v : W, v ≠ 0 ∧ Q v = 0 := by
    by_cases hodd : Odd (Nat.card K)
    · exact (finite_odd_quadratic_low_Witt_dimension_bound hodd Q hQ).1 hW
    · have : Fintype K := Fintype.ofFinite K
      have h2 : ringChar K = 2 := by
        rw [FiniteField.even_card_iff_char_two, ← Nat.card_eq_fintype_card]
        exact Nat.not_odd_iff.mp hodd
      have : CharP K 2 := ringChar.of_eq h2
      obtain ⟨x, -, hx0, hQx⟩ :=
        CFSG.ComponentClassification.UnbalancedCatalog.exists_singular_of_three_le (S := ⊤)
          (polarNondegOn_top hQ) (by rw [finrank_top]; exact hW)
      exact ⟨x, hx0, hQx⟩
  obtain ⟨P, -⟩ := exists_hypPair hQ hQv hv0
  exact ⟨P⟩

theorem finite_orthogonal_derived_natural_linear_centralizer_scalar [Finite K]
    (hK : 2 < Nat.card K) [FiniteDimensional K W] (Q : QuadraticForm K W)
    (hQ : (polarBilin Q).Nondegenerate) (hW : 3 ≤ Module.finrank K W) :
    (∀ M : W →ₗ[K] W, (∀ g ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup Q,
        TauCeti.QuadraticMap.orthogonalGroup Q⁆,
        M ∘ₗ (g : W →ₗ[K] W) = (g : W →ₗ[K] W) ∘ₗ M) ↔ ∃ c : K, M = c • LinearMap.id) ∧
    Nonempty (HypPair Q) ∧
    ∀ P : HypPair Q,
      (∀ w ∈ P.perp, ∀ a : K,
        (∃ g ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆,
          (g : W →ₗ[K] W) = orthElementaryMap Q P.e (a • w)) ∧
        (∃ g ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆,
          (g : W →ₗ[K] W) = orthElementaryMap Q P.f (a • w))) ∧
      ∀ M : W →ₗ[K] W, (∀ w ∈ P.perp, ∀ a : K,
          M ∘ₗ orthElementaryMap Q P.e (a • w) = orthElementaryMap Q P.e (a • w) ∘ₗ M ∧
          M ∘ₗ orthElementaryMap Q P.f (a • w) = orthElementaryMap Q P.f (a • w) ∘ₗ M) →
        ∃ c : K, M = c • LinearMap.id := by
  obtain ⟨c, hc0, hc1⟩ : ∃ c : K, c ≠ 0 ∧ c ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hsurj : Function.Surjective (fun t : Bool => if t then (1 : K) else 0) := by
      intro x
      by_cases hx : x = 0
      · exact ⟨false, by simp [hx]⟩
      · exact ⟨true, by simp [hcon x hx]⟩
    have := Nat.card_le_card_of_surjective _ hsurj
    rw [Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool] at this
    omega
  have hmem : ∀ P : HypPair Q, ∀ w ∈ P.perp, ∀ a : K,
      ∃ g ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆,
        (g : W →ₗ[K] W) = orthElementaryMap Q P.e (a • w) := by
    intro P w hw a
    have haw : a • w ∈ P.perp := P.perp.smul_mem a hw
    have hv : polar Q P.e (a • w) = 0 := (HypPair.mem_perp.mp haw).1
    exact ⟨eichler Q P.e (a • w), eichler_mem_commutator_orthogonalGroup hc0 hc1 P haw,
      LinearMap.ext fun x => eichler_apply P.Q_e hv x⟩
  let swapPair : HypPair Q → HypPair Q := fun P => ⟨P.f, P.e, P.Q_f, P.Q_e, P.polar_fe⟩
  have hswap : ∀ P : HypPair Q, ∀ w, w ∈ P.perp → w ∈ (swapPair P).perp := fun P w hw => by
    rw [HypPair.mem_perp] at hw ⊢
    exact ⟨hw.2, hw.1⟩
  have hexplicit : ∀ P : HypPair Q,
      (∀ w ∈ P.perp, ∀ a : K,
        (∃ g ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆,
          (g : W →ₗ[K] W) = orthElementaryMap Q P.e (a • w)) ∧
        (∃ g ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆,
          (g : W →ₗ[K] W) = orthElementaryMap Q P.f (a • w))) ∧
      ∀ M : W →ₗ[K] W, (∀ w ∈ P.perp, ∀ a : K,
          M ∘ₗ orthElementaryMap Q P.e (a • w) = orthElementaryMap Q P.e (a • w) ∘ₗ M ∧
          M ∘ₗ orthElementaryMap Q P.f (a • w) = orthElementaryMap Q P.f (a • w) ∘ₗ M) →
        ∃ c : K, M = c • LinearMap.id := by
    intro P
    refine ⟨fun w hw a => ⟨hmem P w hw a, hmem (swapPair P) w (hswap P w hw) a⟩, fun M hM => ?_⟩
    obtain ⟨w₀, hw₀, hQw₀⟩ := exists_mem_perp_map_ne_zero hQ hW P
    exact eq_smul_id_of_commute_orthElementaryMap hc0 hc1 P hw₀ hQw₀ M hM
  obtain ⟨P₀⟩ := nonempty_hypPair_of_finite hQ hW
  refine ⟨fun M => ⟨fun hM => (hexplicit P₀).2 M fun w hw a => ?_, ?_⟩, ⟨P₀⟩, hexplicit⟩
  · obtain ⟨⟨g, hg, hge⟩, ⟨g', hg', hge'⟩⟩ := (hexplicit P₀).1 w hw a
    rw [← hge, ← hge']
    exact ⟨hM g hg, hM g' hg'⟩
  · rintro ⟨l, rfl⟩ g _
    rw [LinearMap.smul_comp, LinearMap.comp_smul, LinearMap.id_comp, LinearMap.comp_id]

end CFSG.RankThree.Classical
