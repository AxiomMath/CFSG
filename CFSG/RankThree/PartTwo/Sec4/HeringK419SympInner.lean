module

public import CFSG.RankThree.PartTwo.Sec4.HeringK419SympBasic

public section

namespace CFSG.RankThree.PartTwo.Sec4.HeringK419

open CFSG.LieType.BorelTits

theorem add_self_eq_zero' (K : Type*) {V : Type*} [Field K] [CharP K 2] [AddCommGroup V]
    [Module K V] (a : V) : a + a = 0 := by
  rw [← two_smul K a, CharTwo.two_eq_zero, zero_smul]

theorem neg_eq' (K : Type*) {V : Type*} [Field K] [CharP K 2] [AddCommGroup V] [Module K V]
    (a : V) : -a = a :=
  neg_eq_of_add_eq_zero_right (add_self_eq_zero' K a)

namespace SympData

variable {K V H : Type*} [Field K] [AddCommGroup V] [Module K V] [Group H] [CharP K 2]
  (D : SympData K V H)

@[expose] def lineFlag (v : V) : ℕ → Submodule K V :=
  flag3 (K ∙ v) (D.F.perp (K ∙ v))

theorem β_span_singleton {v : V} (hv : D.F.β v v = 0) {w : V} (hw : w ∈ K ∙ v) :
    D.F.β v w = 0 := by
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hw
  rw [D.F.smul_right, hv, mul_zero]

theorem β_perp_span {v : V} {w : V} (hw : w ∈ D.F.perp (K ∙ v)) : D.F.β v w = 0 :=
  hw v (Submodule.mem_span_singleton_self v)

theorem trans_mem_lineFlagKernel {v : V} {t : H}
    (ht : ∀ w, D.ρ t w = w + D.F.β v w • v) : t ∈ flagKernel D.ρ (D.lineFlag v) := by
  have hvv := D.alt v
  have hinv := D.trans_inv ht
  refine mem_flagKernel_flag3 D.ρ (mem_flagStab_flag3 D.ρ ?_ ?_) ?_ ?_ ?_
  · intro w hw
    rw [hinv, ht, D.β_span_singleton hvv hw, zero_smul, add_zero]
    exact ⟨hw, hw⟩
  · intro w hw
    rw [hinv, ht, D.β_perp_span hw, zero_smul, add_zero]
    exact ⟨hw, hw⟩
  · intro w hw
    rw [ht, D.β_span_singleton hvv hw, zero_smul, add_zero]
  · intro w hw
    rw [ht, D.β_perp_span hw, zero_smul, add_sub_cancel_left]
    exact zero_mem _
  · intro w
    rw [ht, add_sub_cancel_left]
    exact Submodule.smul_mem _ _ (D.F.mem_perp_span_singleton.mpr hvv)

theorem siegel_mem_lineFlagKernel {v y : V} (hvy : D.F.β v y = 0) {s : H}
    (hs : ∀ w, D.ρ s w = w + D.F.β v w • y + D.F.β y w • v) :
    s ∈ flagKernel D.ρ (D.lineFlag v) := by
  have hvv := D.alt v
  have hyv : D.F.β y v = 0 := D.F.refl _ _ hvy
  have hinv := D.siegel_inv hvy hs
  have hyA : ∀ w ∈ K ∙ v, D.F.β y w = 0 := by
    intro w hw
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hw
    rw [D.F.smul_right, hyv, mul_zero]
  have hvmem : v ∈ D.F.perp (K ∙ v) := D.F.mem_perp_span_singleton.mpr hvv
  have hymem : y ∈ D.F.perp (K ∙ v) := D.F.mem_perp_span_singleton.mpr hvy
  refine mem_flagKernel_flag3 D.ρ (mem_flagStab_flag3 D.ρ ?_ ?_) ?_ ?_ ?_
  · intro w hw
    rw [hinv, hs, D.β_span_singleton hvv hw, hyA w hw, zero_smul, zero_smul, add_zero, add_zero]
    exact ⟨hw, hw⟩
  · intro w hw
    rw [hinv, hs, D.β_perp_span hw, zero_smul, add_zero]
    exact ⟨add_mem hw (Submodule.smul_mem _ _ hvmem), add_mem hw (Submodule.smul_mem _ _ hvmem)⟩
  · intro w hw
    rw [hs, D.β_span_singleton hvv hw, hyA w hw, zero_smul, zero_smul, add_zero, add_zero]
  · intro w hw
    rw [hs, D.β_perp_span hw, zero_smul, add_zero, add_sub_cancel_left]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)
  · intro w
    rw [hs, add_assoc, add_sub_cancel_left]
    refine add_mem (Submodule.smul_mem _ _ hymem) (Submodule.smul_mem _ _ hvmem)

theorem eq_one_of_mul_self_eq_one {c : K} (h : c * c = 1) : c = 1 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have : (c - 1) ^ 2 = 0 := by linear_combination h + (1 - c) * h2
  have := pow_eq_zero_iff (two_ne_zero) |>.mp this
  exact sub_eq_zero.mp this

theorem rep_cube {k : H} (hk3 : k ^ 3 = 1) (x : V) :
    D.ρ k (D.ρ k (D.ρ k x)) = x := by
  have : k * k * k = 1 := by rw [← pow_three']; exact hk3
  have h := congrArg (fun g => D.ρ g x) this
  simpa [map_mul, Module.End.mul_apply] using h

theorem rep_inv_eq {k : H} (hk3 : k ^ 3 = 1) (x : V) : D.ρ k⁻¹ x = D.ρ k (D.ρ k x) := by
  have h := D.rep_inv_apply k (D.ρ k (D.ρ k x))
  rw [D.rep_cube hk3] at h
  exact h

theorem exists_move_of_eigen_ne_one {k : H} {v : V} (hv0 : v ≠ 0) {c : K}
    (hc : D.ρ k v = c • v) (hc1 : c ≠ 1) :
    ∃ t ∈ flagKernel D.ρ (D.lineFlag v), k * t * k⁻¹ ≠ t := by
  obtain ⟨t, ht⟩ := D.trans v
  refine ⟨t, D.trans_mem_lineFlagKernel ht, fun heq => ?_⟩
  obtain ⟨x, hx⟩ := D.exists_β_ne_zero hv0
  have h1 := congrArg (fun g => D.ρ g x) heq
  simp only [map_mul, Module.End.mul_apply] at h1
  rw [ht, ht, map_add, map_smul, D.rep_apply_inv, hc, ← D.β_rep_left, hc, D.β_smul_left] at h1
  have h2 : (c * c * D.F.β v x - D.F.β v x) • v = 0 := by
    rw [sub_smul, mul_assoc, mul_smul, smul_smul]
    have h1' := add_left_cancel h1
    rw [smul_smul] at h1'
    rw [sub_eq_zero]
    rw [← h1']
    simp [mul_comm, mul_assoc, mul_left_comm, smul_smul]
  rcases smul_eq_zero.mp h2 with h3 | h3
  · have : c * c = 1 := by
      have h4 : (c * c - 1) * D.F.β v x = 0 := by linear_combination h3
      rcases mul_eq_zero.mp h4 with h5 | h5
      · exact sub_eq_zero.mp h5
      · exact absurd h5 hx
    exact hc1 (eq_one_of_mul_self_eq_one this)
  · exact hv0 h3

theorem exists_move_of_fixed {k : H} (hk3 : k ^ 3 = 1) (hk1 : k ≠ 1) {v : V} (hv0 : v ≠ 0)
    (hc : D.ρ k v = v) :
    ∃ t ∈ flagKernel D.ρ (D.lineFlag v), k * t * k⁻¹ ≠ t := by
  have hkinv : D.ρ k⁻¹ v = v := by
    have := D.rep_inv_apply k v
    rwa [hc] at this
  have hy : ∃ y ∈ D.F.perp (K ∙ v), D.ρ k y - y ∉ K ∙ v := by
    by_contra hcon
    push Not at hcon
    apply hk1
    apply D.inj
    refine LinearMap.ext fun x => ?_
    rw [map_one, Module.End.one_apply]
    have h1 : D.ρ k x - x ∈ D.F.perp (K ∙ v) :=
      D.F.mem_perp_span_singleton.mpr (by
        rw [D.F.β_sub_right, D.β_rep_right, hkinv, sub_self])
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp (hcon _ h1)
    have h3 : D.ρ k (a • v) - a • v = 0 := by rw [map_smul, hc, sub_self]
    rw [ha] at h3
    simp only [map_sub, D.rep_cube hk3] at h3
    have h4 : (3 : K) • (D.ρ k x - D.ρ k (D.ρ k x)) = 0 := by
      rw [← h3]
      module
    have h5 : (3 : K) = 1 := by
      have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
      linear_combination h2
    rw [h5, one_smul, sub_eq_zero] at h4
    have h6 := D.rep_inv_apply k (D.ρ k x)
    rw [← h4, D.rep_inv_apply] at h6
    exact h6.symm
  obtain ⟨y, hyp, hyn⟩ := hy
  have hvy : D.F.β v y = 0 := D.β_perp_span hyp
  obtain ⟨s, hs⟩ := D.siegel v y hvy
  refine ⟨s, D.siegel_mem_lineFlagKernel hvy hs, fun heq => hyn ?_⟩
  obtain ⟨x, hx⟩ := D.exists_β_ne_zero hv0
  have h1 := congrArg (fun g => D.ρ g x) heq
  simp only [map_mul, Module.End.mul_apply] at h1
  rw [hs (D.ρ k⁻¹ x), hs x] at h1
  simp only [map_add, map_smul, D.rep_apply_inv] at h1
  have e1 : D.F.β v (D.ρ k⁻¹ x) = D.F.β v x := by rw [← D.β_rep_left, hc]
  have e2 : D.F.β y (D.ρ k⁻¹ x) = D.F.β (D.ρ k y) x := (D.β_rep_left k y x).symm
  rw [e1, e2, hc] at h1
  have key : D.F.β v x • (D.ρ k y - y) =
      (D.F.β y x - D.F.β (D.ρ k y) x) • v := by
    linear_combination (norm := module) h1
  refine Submodule.mem_span_singleton.mpr ⟨(D.F.β v x)⁻¹ * (D.F.β y x - D.F.β (D.ρ k y) x), ?_⟩
  rw [← smul_smul, ← key, smul_smul, inv_mul_cancel₀ hx, one_smul]

theorem exists_move_of_no_eigen [Finite K] [FiniteDimensional K V] {k : H} (hk3 : k ^ 3 = 1)
    (hnev : ∀ v : V, v ≠ 0 → ∀ c : K, D.ρ k v ≠ c • v) (hdim : 3 ≤ Module.finrank K V) :
    ∃ I : Submodule K V, (∀ w ∈ I, D.ρ k w ∈ I ∧ D.ρ k⁻¹ w ∈ I) ∧
      ∃ t ∈ flagKernel D.ρ (flag2 I), k * t * k⁻¹ ≠ t := by
  classical
  have hker : ∀ w, D.ρ k (D.ρ k w) = D.ρ k w + w := by
    intro w
    by_cases hu : D.ρ k (D.ρ k w) + D.ρ k w + w = 0
    · have h1 : D.ρ k (D.ρ k w) + (D.ρ k w + w) = 0 := by rw [← add_assoc]; exact hu
      have h2 := add_self_eq_zero' K (D.ρ k w + w)
      linear_combination (norm := module) h1 - h2
    · exfalso
      refine hnev _ hu 1 ?_
      rw [one_smul, map_add, map_add, D.rep_cube hk3]
      abel
  have hexists : ∃ x : V, x ≠ 0 ∧ D.F.β x (D.ρ k x) = 0 := by
    by_contra hcon
    push Not at hcon
    haveI : Nontrivial V := Module.nontrivial_of_finrank_pos (R := K) (M := V) (by omega)
    obtain ⟨x₁, hx₁⟩ := exists_ne (0 : V)
    let ψ : V →ₗ[K] K × K := LinearMap.prod (D.F.toDual x₁) (D.F.toDual (D.ρ k x₁))
    have hψ : LinearMap.ker ψ ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt (by
      rw [Module.finrank_prod, Module.finrank_self]
      omega)
    obtain ⟨y, hyker, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hψ
    have hy1 : D.F.β x₁ y = 0 := by
      have := congrArg Prod.fst (LinearMap.mem_ker.mp hyker)
      simpa [ψ] using this
    have hy2 : D.F.β (D.ρ k x₁) y = 0 := by
      have := congrArg Prod.snd (LinearMap.mem_ker.mp hyker)
      simpa [ψ] using this
    have hQy : D.F.β y (D.ρ k y) ≠ 0 := hcon y hy0
    have hQx : D.F.β x₁ (D.ρ k x₁) ≠ 0 := hcon x₁ hx₁
    have hcross1 : D.F.β x₁ (D.ρ k y) = 0 := by
      rw [D.β_rep_right, D.rep_inv_eq hk3, hker, D.F.add_left, hy2, hy1, add_zero]
    have hcross2 : D.F.β y (D.ρ k x₁) = 0 := by rw [D.β_swap, hy2]
    haveI : Fintype K := Fintype.ofFinite K
    obtain ⟨c, hc⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K 2)
      (D.F.β x₁ (D.ρ k x₁) / D.F.β y (D.ρ k y))
    have hzQ : D.F.β (x₁ + c • y) (D.ρ k (x₁ + c • y)) = 0 := by
      simp only [map_add, map_smul, D.F.add_left, D.F.add_right, D.β_smul_left, D.F.smul_right,
        hcross1, hcross2, mul_zero, add_zero, zero_add]
      rw [← mul_assoc, ← hc, div_mul_cancel₀ _ hQy]
      exact CharTwo.add_self_eq_zero _
    have hz0 : x₁ + c • y ≠ 0 := by
      intro hz0
      have hx₁c : x₁ = c • y := by
        have : x₁ = -(c • y) := eq_neg_of_add_eq_zero_left hz0
        rwa [neg_eq' K] at this
      have h := hy2
      rw [hx₁c, map_smul, D.β_smul_left, D.β_swap] at h
      have hc0 : c = 0 := by
        rcases mul_eq_zero.mp h with h' | h'
        · exact h'
        · exact absurd h' hQy
      rw [hc0, zero_smul] at hx₁c
      exact hx₁ hx₁c
    exact hcon _ hz0 hzQ
  obtain ⟨x, hx0, hxQ⟩ := hexists
  set I : Submodule K V := K ∙ x ⊔ K ∙ D.ρ k x with hI
  have hxI : x ∈ I := Submodule.mem_sup_left (Submodule.mem_span_singleton_self x)
  have hpxI : D.ρ k x ∈ I := Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
  have hstab : ∀ w ∈ I, D.ρ k w ∈ I ∧ D.ρ k⁻¹ w ∈ I := by
    intro w hw
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hw
    obtain ⟨a', rfl⟩ := Submodule.mem_span_singleton.mp ha
    obtain ⟨b', rfl⟩ := Submodule.mem_span_singleton.mp hb
    refine ⟨?_, ?_⟩
    · rw [map_add, map_smul, map_smul, hker x]
      exact add_mem (Submodule.smul_mem _ _ hpxI)
        (Submodule.smul_mem _ _ (add_mem hpxI hxI))
    · rw [map_add, map_smul, map_smul, D.rep_inv_eq hk3 x, D.rep_inv_apply, hker x]
      exact add_mem (Submodule.smul_mem _ _ (add_mem hpxI hxI)) (Submodule.smul_mem _ _ hxI)
  have hIiso : ∀ w ∈ I, D.F.β x w = 0 := by
    intro w hw
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hw
    obtain ⟨a', rfl⟩ := Submodule.mem_span_singleton.mp ha
    obtain ⟨b', rfl⟩ := Submodule.mem_span_singleton.mp hb
    rw [D.F.add_right, D.F.smul_right, D.F.smul_right, D.alt x, hxQ, mul_zero, mul_zero,
      add_zero]
  refine ⟨I, hstab, ?_⟩
  obtain ⟨t, ht⟩ := D.trans x
  have htinv := D.trans_inv ht
  have htmem : t ∈ flagKernel D.ρ (flag2 I) := by
    refine mem_flagKernel_flag2 D.ρ (mem_flagStab_flag2 D.ρ ?_) ?_ ?_
    · intro w hw
      rw [htinv, ht, hIiso w hw, zero_smul, add_zero]
      exact ⟨hw, hw⟩
    · intro w hw
      rw [ht, hIiso w hw, zero_smul, add_zero]
    · intro w
      rw [ht, add_sub_cancel_left]
      exact Submodule.smul_mem _ _ hxI
  refine ⟨t, htmem, fun heq => ?_⟩
  obtain ⟨w, hw⟩ := D.exists_β_ne_zero hx0
  have h1 := congrArg (fun g => D.ρ g w) heq
  simp only [map_mul, Module.End.mul_apply] at h1
  rw [ht (D.ρ k⁻¹ w), ht w, map_add, map_smul, D.rep_apply_inv, ← D.β_rep_left] at h1
  have h2 : D.F.β (D.ρ k x) w • D.ρ k x = D.F.β x w • x := add_left_cancel h1
  set a' : K := (D.F.β x w)⁻¹ * D.F.β (D.ρ k x) w with ha'
  have hxa : x = a' • D.ρ k x := by
    rw [ha', ← smul_smul, h2, smul_smul, inv_mul_cancel₀ hw, one_smul]
  have ha'0 : a' ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hxa
    exact hx0 hxa
  refine hnev x hx0 a'⁻¹ ?_
  calc D.ρ k x = a'⁻¹ • (a' • D.ρ k x) := by rw [smul_smul, inv_mul_cancel₀ ha'0, one_smul]
    _ = a'⁻¹ • x := by rw [← hxa]

theorem lineFlag_stab {k : H} {v : V} (hv0 : v ≠ 0) {c : K} (hc : D.ρ k v = c • v) :
    k ∈ flagStab D.ρ (D.lineFlag v) := by
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hc
    have := D.rep_inv_apply k v
    rw [hc, map_zero] at this
    exact hv0 this.symm
  have hcinv : D.ρ k⁻¹ v = c⁻¹ • v := by
    have h := D.rep_inv_apply k v
    rw [hc, map_smul] at h
    calc D.ρ k⁻¹ v = c⁻¹ • (c • D.ρ k⁻¹ v) := by rw [smul_smul, inv_mul_cancel₀ hc0, one_smul]
      _ = c⁻¹ • v := by rw [h]
  refine mem_flagStab_flag3 D.ρ ?_ ?_
  · intro w hw
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hw
    rw [map_smul, map_smul, hc, hcinv]
    exact ⟨Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)),
      Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v))⟩
  · intro w hw
    have hw' : D.F.β v w = 0 := D.β_perp_span hw
    constructor
    · refine D.F.mem_perp_span_singleton.mpr ?_
      rw [D.β_rep_right, hcinv, D.β_smul_left, hw', mul_zero]
    · refine D.F.mem_perp_span_singleton.mpr ?_
      rw [D.β_rep_right, inv_inv, hc, D.β_smul_left, hw', mul_zero]

include D in
theorem exists_two_subgroup_of_order_three [Finite K] [FiniteDimensional K V]
    (hdim : 3 ≤ Module.finrank K V) {k : H} (hk3 : k ^ 3 = 1) (hk1 : k ≠ 1) :
    ∃ T : Subgroup H, IsPGroup 2 T ∧ (∀ t ∈ T, k * t * k⁻¹ ∈ T) ∧
      ∃ t ∈ T, k * t * k⁻¹ ≠ t := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases hev : ∃ v : V, v ≠ 0 ∧ ∃ c : K, D.ρ k v = c • v
  · obtain ⟨v, hv0, c, hc⟩ := hev
    refine ⟨flagKernel D.ρ (D.lineFlag v),
      isPGroup_flagKernel D.ρ 2 D.inj (flag3_zero _ _) (flag3_three _ _),
      fun t ht => conj_mem_flagKernel D.ρ (D.lineFlag_stab hv0 hc) ht, ?_⟩
    by_cases hc1 : c = 1
    · subst hc1
      rw [one_smul] at hc
      exact D.exists_move_of_fixed hk3 hk1 hv0 hc
    · exact D.exists_move_of_eigen_ne_one hv0 hc hc1
  · push Not at hev
    obtain ⟨I, hI, hmove⟩ := D.exists_move_of_no_eigen hk3 (fun v hv c => hev v hv c) hdim
    exact ⟨flagKernel D.ρ (flag2 I),
      isPGroup_flagKernel D.ρ 2 D.inj (flag2_zero _) (flag2_two _),
      fun t ht => conj_mem_flagKernel D.ρ (mem_flagStab_flag2 D.ρ hI) ht, hmove⟩

end SympData

end CFSG.RankThree.PartTwo.Sec4.HeringK419
