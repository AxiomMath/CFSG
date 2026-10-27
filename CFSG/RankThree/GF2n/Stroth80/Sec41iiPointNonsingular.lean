module

public import CFSG.RankThree.GF2n.Stroth80.Sec41iiTensorNat
public import CFSG.ClassicalGroups.Orthogonal.RootGroupStabilizerFour
public import CFSG.ClassicalGroups.Orthogonal.StatedOmegaElementary

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG.Open CFSG.ClassicalGroups.Orthogonal CFSG.ClassicalGroups.PCoreSection
open QuadraticMap
open scoped Matrix

section Nonsingular

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

private theorem polarBilin_isRefl' : (polarBilin Q).IsRefl := fun x y h => by
  rw [polarBilin_apply_apply] at h ⊢
  rwa [polar_comm Q]

private theorem polar_self_char_two [CharP K 2] (x : V) : polar Q x x = 0 := by
  rw [polar_self_eq_two_mul, CharTwo.two_eq_zero, zero_mul]

private theorem exists_singular_add_smul [Finite K] [CharP K 2] {u y : V} (hQu : Q u ≠ 0)
    (hyu : polar Q y u = 0) : ∃ t : K, Q (y + t • u) = 0 := by
  obtain ⟨r, hr⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K 2) (Q y / Q u)
  refine ⟨r, ?_⟩
  have h1 : r * r * Q u = Q y := by rw [← hr, div_mul_cancel₀ _ hQu]
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  rw [QuadraticMap.map_add (⇑Q), map_smul_eq_sq, polar_smul_right_eq, hyu, mul_zero, add_zero]
  linear_combination h1 + Q y * h2

private theorem irreducible_perp [Finite K] [CharP K 2] [FiniteDimensional K V]
    (hQ : (polarBilin Q).Nondegenerate) (h4 : 4 ≤ Module.finrank K V) {u : V} (hu : u ≠ 0)
    (hQu : Q u ≠ 0) (X : Submodule K V) (hLX : Submodule.span K {u} ≤ X)
    (hXP : X ≤ LinearMap.BilinForm.orthogonal (polarBilin Q) (Submodule.span K {u}))
    (hXinv : ∀ s ∈ pointStabilizer Q u, ∀ x ∈ X, s.app x ∈ X) :
    X = Submodule.span K {u} ∨
      X = LinearMap.BilinForm.orthogonal (polarBilin Q) (Submodule.span K {u}) := by
  by_cases hXL : X = Submodule.span K {u}
  · exact Or.inl hXL
  refine Or.inr (le_antisymm hXP ?_)
  obtain ⟨y, hyX, hyL⟩ : ∃ y ∈ X, y ∉ Submodule.span K {u} := by
    by_contra hcon
    push Not at hcon
    exact hXL (le_antisymm hcon hLX)
  have hu_mem : u ∈ X := hLX (Submodule.mem_span_singleton_self u)
  have hyu' : polar Q u y = 0 := mem_orth_span_single_iff.mp (hXP hyX)
  have hyu : polar Q y u = 0 := by rw [polar_comm Q]; exact hyu'
  obtain ⟨σ, hσX, hσs, hσu, hσL⟩ : ∃ σ ∈ X, Q σ = 0 ∧ polar Q u σ = 0 ∧
      σ ∉ Submodule.span K {u} := by
    obtain ⟨t, ht⟩ := exists_singular_add_smul hQu hyu
    refine ⟨y + t • u, X.add_mem hyX (X.smul_mem t hu_mem), ht, ?_, ?_⟩
    · rw [polar_add_right, polar_smul_right_eq, polar_self_char_two, mul_zero, add_zero, hyu']
    · intro hmem
      apply hyL
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
      have hy : y = (c - t) • u := by rw [sub_smul, hc, add_sub_cancel_right]
      rw [hy]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self u)
  by_cases h5 : 5 ≤ Module.finrank K V
  · exact orth_le_of_singular_mem hQ h5 hXinv hσX hσs hσu hσL
  have h4' : Module.finrank K V = 4 := by omega
  have hσu'' : polar Q σ u = 0 := by rw [polar_comm Q]; exact hσu
  have hσσ : polar Q σ σ = 0 := polar_self_eq_zero hσs
  obtain ⟨z, hzu, hσz⟩ := exists_polar_ne_zero_of_not_mem hQ hσL
  have hzu' : polar Q u z = 0 := mem_orth_span_single_iff.mp hzu
  have hzu'' : polar Q z u = 0 := by rw [polar_comm Q]; exact hzu'
  obtain ⟨a, haQ, hau, hσa⟩ : ∃ a : V, Q a = 0 ∧ polar Q a u = 0 ∧ polar Q σ a ≠ 0 := by
    obtain ⟨t', ht'⟩ := exists_singular_add_smul hQu hzu''
    refine ⟨z + t' • u, ht', ?_, ?_⟩
    · rw [polar_add_left, polar_smul_left_eq, polar_self_char_two, mul_zero, add_zero, hzu'']
    · rw [polar_add_right, polar_smul_right_eq, hσu'', mul_zero, add_zero]
      exact hσz
  have hua : polar Q u a = 0 := by rw [polar_comm Q]; exact hau
  have hEmem : Eom Q a u ∈ pointStabilizer Q u := by
    refine mem_pointStabilizer.mpr ⟨1, ?_⟩
    simp only [Eom_app haQ hau, hua, polar_self_char_two, zero_smul, mul_zero, zero_add,
      add_zero, sub_zero, one_smul]
  have hwX := hXinv _ hEmem σ hσX
  rw [Eom_app haQ hau, hσu''] at hwX
  have h1 : polar Q σ a • (u - Q u • a) ∈ X := by
    have := X.sub_mem hwX hσX
    convert this using 1
    module
  have h2 : u - Q u • a ∈ X := by
    have := X.smul_mem (polar Q σ a)⁻¹ h1
    rwa [smul_smul, inv_mul_cancel₀ hσa, one_smul] at this
  have haX : a ∈ X := by
    have h3 : Q u • a ∈ X := by
      have := X.sub_mem hu_mem h2
      rwa [sub_sub_cancel] at this
    have := X.smul_mem (Q u)⁻¹ h3
    rwa [smul_smul, inv_mul_cancel₀ hQu, one_smul] at this
  have haa : polar Q a a = 0 := polar_self_eq_zero haQ
  have hsa : polar Q a σ = polar Q σ a := polar_comm Q a σ
  have hli : LinearIndependent K ![u, σ, a] := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons] at hg
    have hp1 := congrArg (polar Q σ) hg
    have hp2 := congrArg (polar Q a) hg
    simp only [polar_add_right, polar_smul_right_eq, polar_zero_right] at hp1 hp2
    have e2 : g 2 * polar Q σ a = 0 := by
      linear_combination hp1 - g 0 * hσu'' - g 1 * hσσ
    have e1 : g 1 * polar Q σ a = 0 := by
      linear_combination hp2 - g 0 * hau - g 2 * haa - g 1 * hsa
    have hg2 : g 2 = 0 := (mul_eq_zero.mp e2).resolve_right hσa
    have hg1 : g 1 = 0 := (mul_eq_zero.mp e1).resolve_right hσa
    have hg0 : g 0 = 0 := by
      simp only [hg1, hg2, zero_smul, add_zero] at hg
      exact (smul_eq_zero.mp hg).resolve_right hu
    intro i
    fin_cases i <;> simp [hg0, hg1, hg2]
  have hspan : Submodule.span K {u, σ, a} ≤
      LinearMap.BilinForm.orthogonal (polarBilin Q) (Submodule.span K {u}) := by
    rw [Submodule.span_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with h | h | h
    · rw [h]; exact mem_orth_span_single_iff.mpr (polar_self_char_two u)
    · rw [h]; exact mem_orth_span_single_iff.mpr hσu
    · rw [h]; exact mem_orth_span_single_iff.mpr hua
  have hfin : Module.finrank K (Submodule.span K {u, σ, a}) = 3 := by
    have hrange : Set.range ![u, σ, a] = {u, σ, a} := by
      simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
    have h := finrank_span_eq_card hli
    rw [hrange, Fintype.card_fin] at h
    exact h
  have hfin' : Module.finrank K
      (LinearMap.BilinForm.orthogonal (polarBilin Q) (Submodule.span K {u})) = 3 := by
    rw [LinearMap.BilinForm.finrank_orthogonal hQ, finrank_span_singleton hu, h4']
  have heq := Submodule.eq_of_le_of_finrank_eq hspan (hfin.trans hfin'.symm)
  rw [← heq, Submodule.span_le]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with h | h | h
  · rw [h]; exact hu_mem
  · rw [h]; exact hσX
  · rw [h]; exact haX

private theorem trivial_of_normal_two_group [Finite K] [CharP K 2] [FiniteDimensional K V]
    (hQ : (polarBilin Q).Nondegenerate) (h4 : 4 ≤ Module.finrank K V) {u : V} (hu : u ≠ 0)
    (hQu : Q u ≠ 0) (T : Subgroup (Gom Q)) (hTS : T ≤ pointStabilizer Q u)
    (hT2 : ∀ t ∈ T, t * t = 1) (hTn : ∀ s ∈ pointStabilizer Q u, ∀ t ∈ T, s * t * s⁻¹ ∈ T) :
    ∀ t ∈ T, t = 1 := by
  haveI : Finite V := Module.finite_of_finite K
  intro t ht
  have hT : IsPGroup 2 T := by
    intro g
    have hg : g * g = 1 := Subtype.ext (hT2 g.1 g.2)
    exact ⟨1, by rw [pow_one, pow_two, hg]⟩
  have hLP : Submodule.span K {u} ≤
      LinearMap.BilinForm.orthogonal (polarBilin Q) (Submodule.span K {u}) := by
    rw [Submodule.span_le]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    rw [hx]
    exact mem_orth_span_single_iff.mpr (polar_self_char_two u)
  have hP : ∀ s ∈ pointStabilizer Q u,
      ∀ x ∈ LinearMap.BilinForm.orthogonal (polarBilin Q) (Submodule.span K {u}),
        s.app x ∈ LinearMap.BilinForm.orthogonal (polarBilin Q) (Submodule.span K {u}) := by
    intro s hs x hx
    have hxu : polar Q x u = 0 := by
      rw [polar_comm Q]
      exact mem_orth_span_single_iff.mp hx
    rw [mem_orth_span_single_iff, polar_comm Q]
    exact polar_app_eq_zero_of_mem_pointStabilizer hu hs hxu
  have hL : ∀ s ∈ pointStabilizer Q u, ∀ x ∈ Submodule.span K {u},
      s.app x ∈ Submodule.span K {u} := by
    intro s hs x hx
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
    obtain ⟨d, hd⟩ := mem_pointStabilizer.mp hs
    rw [Gom.map_smul, hd, smul_smul]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self u)
  have hperp : ∀ x ∈ LinearMap.BilinForm.orthogonal (polarBilin Q) (Submodule.span K {u}),
      t.app x - x ∈ Submodule.span K {u} :=
    (apply_sub_mem_of_isPGroup (isLinearAction_Gom Q) hTS hT hTn hLP hP hL
      (irreducible_perp hQ h4 hu hQu)) t ht
  have hfix : ∀ x ∈ LinearMap.BilinForm.orthogonal (polarBilin Q) (Submodule.span K {u}),
      t.app x = x := by
    intro x hx
    have hxu : polar Q x u = 0 := by
      rw [polar_comm Q]
      exact mem_orth_span_single_iff.mp hx
    obtain ⟨γ, hγ⟩ := Submodule.mem_span_singleton.mp (hperp x hx)
    have hγ' : γ • u = t.app x - x := hγ
    have hγx : t.app x = x + γ • u := by rw [hγ']; abel
    have hQx := Gom.map_of_mem t x
    rw [hγx, QuadraticMap.map_add (⇑Q), map_smul_eq_sq, polar_smul_right_eq, hxu, mul_zero,
      add_zero] at hQx
    have hγ2 : γ * γ * Q u = 0 := by linear_combination hQx
    have hγ0 : γ = 0 := by
      rcases mul_eq_zero.mp hγ2 with h | h
      · exact mul_self_eq_zero.mp h
      · exact absurd h hQu
    rw [hγx, hγ0, zero_smul, add_zero]
  obtain ⟨w, hw⟩ := exists_polar_ne_zero hQ hu
  obtain ⟨x₀, hx₀⟩ : ∃ x₀ : V, polar Q u x₀ = 1 :=
    ⟨(polar Q u w)⁻¹ • w, by rw [polar_smul_right_eq, inv_mul_cancel₀ hw]⟩
  have hx₀' : polar Q x₀ u = 1 := by rw [polar_comm Q]; exact hx₀
  have hz : t.app x₀ - x₀ ∈ Submodule.span K {u} := by
    have hmem : t.app x₀ - x₀ ∈ LinearMap.BilinForm.orthogonal (polarBilin Q)
        (LinearMap.BilinForm.orthogonal (polarBilin Q) (Submodule.span K {u})) := by
      rw [mem_orth_iff]
      intro x hx
      have h1 : polar Q (t.app x) (t.app x₀) = polar Q x x₀ := Gom.polar_app t x x₀
      rw [hfix x hx] at h1
      rw [polar_sub_right, h1, sub_self]
    rwa [LinearMap.BilinForm.orthogonal_orthogonal hQ polarBilin_isRefl'] at hmem
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hz
  have hc' : c • u = t.app x₀ - x₀ := hc
  have hTx₀ : t.app x₀ = x₀ + c • u := by rw [hc']; abel
  have hcQ : c * c * Q u + c = 0 := by
    have h1 := Gom.map_of_mem t x₀
    rw [hTx₀, QuadraticMap.map_add (⇑Q), map_smul_eq_sq, polar_smul_right_eq, hx₀'] at h1
    linear_combination h1
  have hformula : ∀ v : V, t.app v = v + (polar Q u v * c) • u := by
    intro v
    have hw' : polar Q u (v - polar Q u v • x₀) = 0 := by
      rw [polar_sub_right, polar_smul_right_eq, hx₀, mul_one, sub_self]
    have hwfix := hfix _ (mem_orth_span_single_iff.mpr hw')
    calc t.app v = t.app ((v - polar Q u v • x₀) + polar Q u v • x₀) := by rw [sub_add_cancel]
      _ = (v - polar Q u v • x₀) + polar Q u v • (x₀ + c • u) := by
          rw [Gom.map_add, Gom.map_smul, hwfix, hTx₀]
      _ = v + (polar Q u v * c) • u := by module
  have hc2 : c * (c * Q u + 1) = 0 := by linear_combination hcQ
  rcases mul_eq_zero.mp hc2 with hc0 | hc1
  · refine Gom.ext' fun v => ?_
    rw [hformula v, hc0, mul_zero, zero_smul, add_zero, Gom.app_one]
  ·
    exfalso
    have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
    have hcinv : c = (Q u)⁻¹ := by
      have : c * Q u = 1 := by linear_combination hc1 - h2
      exact eq_inv_of_mul_eq_one_left this
    haveI : Invertible (Q u) := invertibleOfNonzero hQu
    have heq : (t : V ≃ₗ[K] V) = reflect Q u := by
      refine LinearEquiv.ext fun v => ?_
      show t.app v = reflect Q u v
      rw [hformula v, reflect_apply hQu v, hcinv, div_eq_mul_inv, sub_eq_add_neg, ← neg_smul,
        CharTwo.neg_eq]
    have hmem : reflect Q u ∈ CFSG.RankThree.OrthogonalInvolutions.omegaGroup Q hQ := by
      rw [← heq]
      exact elementaryGroup_le_omegaGroup hQ t.2
    have hev := (CFSG.RankThree.OrthogonalInvolutions.mem_omegaGroup.mp hmem).2
    have hrank := CFSG.RankThree.OrthogonalInvolutions.finrank_commSpace_reflection hQ u
    rw [reflect_eq_reflection, hrank] at hev
    exact Nat.not_even_one hev

private theorem pointTrivial_of_equiv {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type}
    [Field K] [Finite K] [CharP K 2] {Q : QuadraticForm K (ι → K)} {X : Subgroup (GL ι K)}
    (e : ↥X ≃* Gom Q)
    (he : ∀ (A : ↥X) (v : ι → K), (e A).app v = ((A : GL ι K) : Matrix ι ι K) *ᵥ v)
    (hQ : (polarBilin Q).Nondegenerate) (h4 : 4 ≤ Module.finrank K (ι → K)) {u : ι → K}
    (hu : u ≠ 0) (hQu : Q u ≠ 0) : PointTrivial K X u := by
  unfold PointTrivial
  intro P hPX hP2 hPfix hPnorm
  have hTS : (P.subgroupOf X).map e.toMonoidHom ≤ pointStabilizer Q u := by
    intro t ht
    obtain ⟨A, hA, rfl⟩ := Subgroup.mem_map.mp ht
    rw [mem_pointStabilizer]
    refine ⟨1, ?_⟩
    change (e A).app u = 1 • u
    rw [he, hPfix _ (Subgroup.mem_subgroupOf.mp hA), one_smul]
  have hT2 : ∀ t ∈ (P.subgroupOf X).map e.toMonoidHom, t * t = 1 := by
    intro t ht
    obtain ⟨A, hA, rfl⟩ := Subgroup.mem_map.mp ht
    change e A * e A = 1
    rw [← map_mul]
    have hAA : A * A = 1 := Subtype.ext (hP2 _ (Subgroup.mem_subgroupOf.mp hA))
    rw [hAA, map_one]
  have hTn : ∀ s ∈ pointStabilizer Q u, ∀ t ∈ (P.subgroupOf X).map e.toMonoidHom,
      s * t * s⁻¹ ∈ (P.subgroupOf X).map e.toMonoidHom := by
    intro s hs t ht
    obtain ⟨A, hA, rfl⟩ := Subgroup.mem_map.mp ht
    obtain ⟨g, rfl⟩ := e.surjective s
    obtain ⟨c, hc⟩ := mem_pointStabilizer.mp hs
    rw [he] at hc
    have hconj := hPnorm (g : GL ι K) g.2 ⟨c, hc⟩ (A : GL ι K) (Subgroup.mem_subgroupOf.mp hA)
    refine Subgroup.mem_map.mpr ⟨g * A * g⁻¹, Subgroup.mem_subgroupOf.mpr hconj, ?_⟩
    change e (g * A * g⁻¹) = e g * e A * (e g)⁻¹
    rw [map_mul, map_mul, map_inv]
  have key := trivial_of_normal_two_group hQ h4 hu hQu _ hTS hT2 hTn
  refine eq_bot_iff.mpr fun p hp => ?_
  have hpX : p ∈ X := hPX hp
  have hmem : e ⟨p, hpX⟩ ∈ (P.subgroupOf X).map e.toMonoidHom :=
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hp)
  have h1 : e ⟨p, hpX⟩ = 1 := key _ hmem
  have h2 : (⟨p, hpX⟩ : ↥X) = 1 := e.injective (by rw [h1, map_one])
  rw [Subgroup.mem_bot]
  exact congrArg Subtype.val h2

end Nonsingular

theorem classicalPointNonsingularStatement_holds : ClassicalPointNonsingularStatement := by
  intro K _ _ _ _
  refine ⟨fun m hm u hu0 hQu => ?_, fun m b c hm hirr u hu0 hQu => ?_⟩
  · have h4 : 4 ≤ Module.finrank K (Fin m ⊕ Fin m → K) := by
      simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
      omega
    have hQ' : (CFSG.LieType.Universal.Spin.quadPlus m K) u ≠ 0 := by
      rw [congrFun (CFSG.LieType.Universal.Spin.coe_quadPlus m K) u]
      exact hQu
    exact pointTrivial_of_equiv (statedOmegaPlusEquiv hm) (statedOmegaPlusEquiv_app hm)
      (CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadPlus m K) h4 hu0 hQ'
  · have h4 : 4 ≤ Module.finrank K (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K) := by
      simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
      omega
    have hQ' : (CFSG.LieType.Universal.Spin.quadMinus m K b c) u ≠ 0 := by
      rw [congrFun (CFSG.LieType.Universal.Spin.coe_quadMinus m K b c) u]
      exact hQu
    exact pointTrivial_of_equiv (statedOmegaMinusEquiv hm hirr)
      (statedOmegaMinusEquiv_app hm hirr)
      (CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadMinus_of_finite m K hirr) h4 hu0
      hQ'

end CFSG.RankThree.GF2n.Stroth80
