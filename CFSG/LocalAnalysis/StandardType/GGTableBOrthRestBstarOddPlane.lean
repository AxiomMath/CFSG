module

public import CFSG.LocalAnalysis.StandardType.GGTableBOrthRestOddLayer

public section

namespace CFSG.StandardType

namespace OrthBstarOdd

open Module CFSG.RankThree.PartOne.LIT

section Eigen

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]

theorem apply_eq_of_eigen {p : ℕ} {s : V ≃ₗ[K] V} (hsp : s ^ p = 1)
    (hK1 : ∀ c : K, c ^ p = 1 → c = 1) {v : V} (hv : v ≠ 0) {c : K} (hc : s v = c • v) :
    s v = v := by
  have hpow : ∀ k : ℕ, (s ^ k) v = c ^ k • v := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, LinearEquiv.mul_apply, hc, map_smul, ih, smul_smul, pow_succ']
  have h1 := hpow p
  rw [hsp] at h1
  change v = c ^ p • v at h1
  have h2 : (c ^ p - 1) • v = 0 := by rw [sub_smul, ← h1, one_smul, sub_self]
  have h3 : c ^ p = 1 := sub_eq_zero.mp ((smul_eq_zero.mp h2).resolve_right hv)
  rw [hc, hK1 c h3, one_smul]

theorem indep_of_ne {p : ℕ} {s : V ≃ₗ[K] V} (hsp : s ^ p = 1)
    (hK1 : ∀ c : K, c ^ p = 1 → c = 1) {w : V} (hw : s w ≠ w) :
    ∀ a b : K, a • w + b • s w = 0 → a = 0 ∧ b = 0 := by
  have hw0 : w ≠ 0 := by
    rintro rfl
    exact hw (map_zero s)
  intro a b hab
  by_cases hb : b = 0
  · subst hb
    rw [zero_smul, add_zero] at hab
    exact ⟨(smul_eq_zero.mp hab).resolve_right hw0, rfl⟩
  · exfalso
    apply hw
    refine apply_eq_of_eigen hsp hK1 hw0 (c := -(b⁻¹ * a)) ?_
    have h1 : b • s w = -(a • w) := eq_neg_of_add_eq_zero_right hab
    calc s w = b⁻¹ • (b • s w) := by rw [smul_smul, inv_mul_cancel₀ hb, one_smul]
      _ = -(b⁻¹ * a) • w := by rw [h1, smul_neg, smul_smul, neg_smul]

variable [FiniteDimensional K V]

theorem mem_span_of_finrank_two {W : Submodule K V} (hW : finrank K W = 2) {x y : V}
    (hx : x ∈ W) (hy : y ∈ W) (hind : ∀ a b : K, a • x + b • y = 0 → a = 0 ∧ b = 0) :
    ∀ v ∈ W, ∃ a b : K, v = a • x + b • y := by
  have hli : LinearIndependent K ![x, y] := LinearIndependent.pair_iff.mpr hind
  have hle : Submodule.span K (Set.range ![x, y]) ≤ W := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact hx
    · exact hy
  have hfin : finrank K (Submodule.span K (Set.range ![x, y])) = 2 := by
    rw [finrank_span_eq_card hli, Fintype.card_fin]
  have heq : Submodule.span K (Set.range ![x, y]) = W :=
    Submodule.eq_of_le_of_finrank_eq hle (by rw [hfin, hW])
  intro v hv
  rw [← heq, Submodule.mem_span_range_iff_exists_fun] at hv
  obtain ⟨c, hc⟩ := hv
  refine ⟨c 0, c 1, ?_⟩
  rw [← hc, Fin.sum_univ_two]
  rfl

end Eigen

section Plane

variable {K : Type} [Field K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V}

omit [CharP K 2] in
theorem polar_map {s : V ≃ₗ[K] V} (hsQ : ∀ v, Q (s v) = Q v) (u v : V) :
    QuadraticMap.polar Q (s u) (s v) = QuadraticMap.polar Q u v := by
  simp only [QuadraticMap.polar, ← map_add, hsQ]

theorem polar_eq_of_sq {s : V ≃ₗ[K] V} (hsQ : ∀ v, Q (s v) = Q v) {τ : K} (hτ : τ ≠ 0) {z : V}
    (hz : s (s z) = τ • s z + z) : QuadraticMap.polar Q z (s z) = τ * Q z := by
  have h2K : (2 : K) = 0 := CharTwo.two_eq_zero
  have e : Q (τ • s z + z) = Q z := by rw [← hz, hsQ, hsQ]
  rw [QuadraticMap.map_add (⇑Q) (τ • s z) z, QuadraticMap.map_smul, QuadraticMap.polar_smul_left,
    hsQ, smul_eq_mul, smul_eq_mul, QuadraticMap.polar_comm] at e
  have h : τ * (QuadraticMap.polar Q z (s z) - τ * Q z) = 0 := by
    linear_combination e - τ ^ 2 * Q z * h2K
  exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left hτ)

theorem map_add_smul_of_sq {s : V ≃ₗ[K] V} (hsQ : ∀ v, Q (s v) = Q v) {τ : K} (hτ : τ ≠ 0)
    {z : V} (hz : s (s z) = τ • s z + z) (a b : K) :
    Q (a • z + b • s z) = (a ^ 2 + τ * a * b + b ^ 2) * Q z := by
  rw [QuadraticMap.map_add (⇑Q) (a • z) (b • s z), QuadraticMap.map_smul, QuadraticMap.map_smul,
    QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_right, polar_eq_of_sq hsQ hτ hz, hsQ,
    smul_eq_mul, smul_eq_mul, smul_eq_mul, smul_eq_mul]
  ring

variable [FiniteDimensional K V]

theorem plane_facts {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hK1 : ∀ c : K, c ^ p = 1 → c = 1)
    {s : V ≃ₗ[K] V} (hsQ : ∀ v, Q (s v) = Q v) (hsp : s ^ p = 1) {W : Submodule K V}
    (hW : finrank K W = 2) (hnd : ∀ w ∈ W, (∀ w' ∈ W, QuadraticMap.polar Q w w' = 0) → w = 0)
    (hsW : ∀ v ∈ W, s v ∈ W) (hfpf : ∀ v ∈ W, v ≠ 0 → s v ≠ v) :
    ∃ τ : K, τ ≠ 0 ∧ (∀ v ∈ W, s (s v) = τ • s v + v) ∧ ∀ v ∈ W, v ≠ 0 → Q v ≠ 0 := by
  have hWne : W ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hW
    exact absurd hW (by norm_num)
  obtain ⟨w, hwW, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hWne
  have hself : ∀ u, QuadraticMap.polar Q u u = 0 := fun u => OrthRestOdd.polar_self_eq_zero Q u
  have hB : ∀ v ∈ W, v ≠ 0 → QuadraticMap.polar Q v (s v) ≠ 0 := by
    intro v hvW hv0 h0
    have hspan := mem_span_of_finrank_two hW hvW (hsW v hvW) (indep_of_ne hsp hK1 (hfpf v hvW hv0))
    apply hv0
    refine hnd v hvW fun w' hw' => ?_
    obtain ⟨a, b, rfl⟩ := hspan w' hw'
    rw [QuadraticMap.polar_add_right, QuadraticMap.polar_smul_right,
      QuadraticMap.polar_smul_right, hself, h0, smul_zero, smul_zero, add_zero]
  have hspan := mem_span_of_finrank_two hW hwW (hsW w hwW) (indep_of_ne hsp hK1 (hfpf w hwW hw0))
  obtain ⟨α, τ, hατ⟩ := hspan (s (s w)) (hsW _ (hsW w hwW))
  have hα : α = 1 := by
    have e1 := polar_map hsQ w (s w)
    rw [hατ, QuadraticMap.polar_add_right, QuadraticMap.polar_smul_right,
      QuadraticMap.polar_smul_right, hself, smul_zero, add_zero, QuadraticMap.polar_comm,
      smul_eq_mul] at e1
    have h1 : (α - 1) * QuadraticMap.polar Q w (s w) = 0 := by rw [sub_mul, e1, one_mul, sub_self]
    exact sub_eq_zero.mp ((mul_eq_zero.mp h1).resolve_right (hB w hwW hw0))
  subst hα
  rw [one_smul] at hατ
  have hsq : ∀ v ∈ W, s (s v) = τ • s v + v := by
    intro v hv
    obtain ⟨a, b, rfl⟩ := hspan v hv
    have h3 := congrArg s hατ
    rw [map_add, map_smul] at h3
    simp only [map_add, map_smul]
    rw [h3, hατ]
    module
  have hτ : τ ≠ 0 := by
    intro hτ0
    have hs2 : ∀ v ∈ W, s (s v) = v := fun v hv => by rw [hsq v hv, hτ0, zero_smul, zero_add]
    obtain ⟨k, hk⟩ : Odd p := hp.odd_of_ne_two hp2
    have hpow : ∀ j : ℕ, ∀ v ∈ W, (s ^ (2 * j)) v = v := by
      intro j
      induction j with
      | zero => intro v _; simp
      | succ j ih =>
        intro v hv
        rw [show 2 * (j + 1) = 2 * j + 2 by ring, pow_add, LinearEquiv.mul_apply, sq,
          LinearEquiv.mul_apply, hs2 v hv, ih v hv]
    have h1 : (s ^ p) w = s w := by
      rw [hk, pow_succ, LinearEquiv.mul_apply, hpow k (s w) (hsW w hwW)]
    rw [hsp] at h1
    exact hfpf w hwW hw0 h1.symm
  refine ⟨τ, hτ, hsq, fun v hv hv0 hQv => ?_⟩
  have h1 := polar_eq_of_sq hsQ hτ (hsq v hv)
  rw [hQv, mul_zero] at h1
  exact hB v hv hv0 h1

end Plane

section Split

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V}

theorem polar_fixed_comm {t : V ≃ₗ[K] V} (htQ : ∀ v, Q (t v) = Q v) :
    ∀ u ∈ fixedSpace t, ∀ w ∈ commSpace t, QuadraticMap.polar Q u w = 0 := by
  intro u hu w hw
  obtain ⟨y, rfl⟩ := mem_commSpace.mp hw
  have h1 := polar_map htQ u y
  rw [mem_fixedSpace.mp hu] at h1
  rw [QuadraticMap.polar_sub_right, h1, sub_self]

variable [FiniteDimensional K V]

theorem commSpace_nondeg (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {p : ℕ}
    (hpK : (p : K) ≠ 0) {t : V ≃ₗ[K] V} (htQ : ∀ v, Q (t v) = Q v) (htp : t ^ p = 1) :
    ∀ w ∈ commSpace t, (∀ w' ∈ commSpace t, QuadraticMap.polar Q w w' = 0) → w = 0 := by
  intro w hw hw'
  have hc := isCompl_fixedSpace_commSpace hpK htp
  refine hQ.1 w fun v => ?_
  have hv : v ∈ fixedSpace t ⊔ commSpace t := by rw [hc.sup_eq_top]; trivial
  obtain ⟨u, hu, w₁, hw₁, rfl⟩ := Submodule.mem_sup.mp hv
  rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_add_right, hw' w₁ hw₁,
    QuadraticMap.polar_comm, polar_fixed_comm htQ u hu w hw, zero_add]

theorem fixedSpace_nondeg (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {p : ℕ}
    (hpK : (p : K) ≠ 0) {t : V ≃ₗ[K] V} (htQ : ∀ v, Q (t v) = Q v) (htp : t ^ p = 1) :
    ∀ u ∈ fixedSpace t, (∀ u' ∈ fixedSpace t, QuadraticMap.polar Q u u' = 0) → u = 0 := by
  intro u hu hu'
  have hc := isCompl_fixedSpace_commSpace hpK htp
  refine hQ.1 u fun v => ?_
  have hv : v ∈ fixedSpace t ⊔ commSpace t := by rw [hc.sup_eq_top]; trivial
  obtain ⟨u₁, hu₁, w₁, hw₁, rfl⟩ := Submodule.mem_sup.mp hv
  rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_add_right, hu' u₁ hu₁,
    polar_fixed_comm htQ u hu w₁ hw₁, zero_add]

theorem fpf_commSpace {p : ℕ} (hpK : (p : K) ≠ 0) {t : V ≃ₗ[K] V} (htp : t ^ p = 1) :
    ∀ v ∈ commSpace t, v ≠ 0 → t v ≠ v := by
  intro v hv hv0 htv
  have hc := isCompl_fixedSpace_commSpace hpK htp
  have hmem : v ∈ fixedSpace t ⊓ commSpace t := ⟨mem_fixedSpace.mpr htv, hv⟩
  rw [hc.inf_eq_bot, Submodule.mem_bot] at hmem
  exact hv0 hmem

end Split

end OrthBstarOdd

end CFSG.StandardType
