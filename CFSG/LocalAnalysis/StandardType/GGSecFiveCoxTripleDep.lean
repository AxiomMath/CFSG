module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveCoxTriplePair

public section

namespace CFSG.StandardType.CoxTriple

open CFSG.LieType.RootSystem

private lemma ct_dep_arith {ε r m n u v : ℚ}
    (hε : ε = 1 ∨ ε = -1) (hr : 0 < r)
    (hm : 3 * r = m ^ 2 - ε * m * n + n ^ 2)
    (hu : u = m * (m / r)) (hv : v = n * (n / r))
    (hu012 : u = 0 ∨ u = 1 ∨ u = 2) (hv012 : v = 0 ∨ v = 1 ∨ v = 2)
    (hmi : ∃ z : ℤ, (z : ℚ) = m) (hmr : ∃ z : ℤ, (z : ℚ) = m / r) :
    r = 1 ∧ n = -ε * m := by
  have hr0 : r ≠ 0 := ne_of_gt hr
  have hm0 : m ≠ 0 := by
    intro h
    subst h
    have hv3 : v = 3 := by rw [hv]; field_simp; linarith [hm]
    rcases hv012 with h | h | h <;> linarith
  have hn0 : n ≠ 0 := by
    intro h
    subst h
    have hu3 : u = 3 := by rw [hu]; field_simp; linarith [hm]
    rcases hu012 with h | h | h <;> linarith
  have hu' : u * r = m ^ 2 := by rw [hu]; field_simp
  have hv' : v * r = n ^ 2 := by rw [hv]; field_simp
  have hu12 : u = 1 ∨ u = 2 := by
    rcases hu012 with h | h | h
    · rw [h, zero_mul] at hu'; exact absurd (sq_eq_zero_iff.mp hu'.symm) hm0
    · exact Or.inl h
    · exact Or.inr h
  have hv12 : v = 1 ∨ v = 2 := by
    rcases hv012 with h | h | h
    · rw [h, zero_mul] at hv'; exact absurd (sq_eq_zero_iff.mp hv'.symm) hn0
    · exact Or.inl h
    · exact Or.inr h
  have key : m ^ 2 = r → u = 1 → r = 1 := by
    intro hsq hu1
    obtain ⟨mi, hmi'⟩ := hmi
    obtain ⟨zi, hzr⟩ := hmr
    have hprodq : (mi : ℚ) * (zi : ℚ) = 1 := by
      rw [hmi', hzr, ← hu]; exact hu1
    have hpi : mi * zi = 1 := by exact_mod_cast hprodq
    have hr1 : r = 1 := by
      rw [← hsq, ← hmi']
      rcases Int.eq_one_or_neg_one_of_mul_eq_one hpi with h | h <;> rw [h] <;> norm_num
    exact hr1
  rcases hε with rfl | hε
  ·
    rcases hu12 with hu1 | hu2 <;> rcases hv12 with hv1 | hv2
    · rw [hu1, one_mul] at hu'
      rw [hv1, one_mul] at hv'
      have hmn : m * n = -m ^ 2 := by nlinarith [hm, hu', hv']
      have hn_eq : n = -m := by
        have h2 : m * (n + m) = 0 := by nlinarith [hmn]
        rcases mul_eq_zero.mp h2 with h | h
        · exact absurd h hm0
        · linarith
      refine ⟨key hu'.symm hu1, ?_⟩
      rw [hn_eq]; ring
    · rw [hu1, one_mul] at hu'
      rw [hv2] at hv'
      have hmn : m * n = 0 := by nlinarith [hm, hu', hv']
      exact absurd hmn (mul_ne_zero hm0 hn0)
    · rw [hu2] at hu'
      rw [hv1, one_mul] at hv'
      have hmn : m * n = 0 := by nlinarith [hm, hu', hv']
      exact absurd hmn (mul_ne_zero hm0 hn0)
    · rw [hu2] at hu'
      rw [hv2] at hv'
      have hfac : (m - n) * (m + n) = 0 := by nlinarith [hu', hv']
      have hmn : m * n = r := by nlinarith [hm, hu', hv']
      rcases mul_eq_zero.mp hfac with h | h
      · have hm : m = n := by linarith
        rw [hm] at hmn
        nlinarith [hr, hv', hmn]
      · have hm : m = -n := by linarith
        rw [hm] at hmn
        nlinarith [hr, hv', hmn]
  ·
    rw [hε] at hm
    rcases hu12 with hu1 | hu2 <;> rcases hv12 with hv1 | hv2
    · rw [hu1, one_mul] at hu'
      rw [hv1, one_mul] at hv'
      have hmn : m * n = r := by nlinarith [hm, hu', hv']
      have hn_eq : n = m := by
        have hfac : (m - n) * (m + n) = 0 := by nlinarith [hu', hv']
        rcases mul_eq_zero.mp hfac with h | h
        · linarith
        · have : n = -m := by linarith
          rw [this] at hmn
          nlinarith [hv', hmn]
      refine ⟨key hu'.symm hu1, ?_⟩
      rw [hn_eq, hε]; ring
    · rw [hu1, one_mul] at hu'
      rw [hv2] at hv'
      have hmn : m * n = 0 := by nlinarith [hm, hu', hv']
      exact absurd hmn (mul_ne_zero hm0 hn0)
    · rw [hu2] at hu'
      rw [hv1, one_mul] at hv'
      have hmn : m * n = 0 := by nlinarith [hm, hu', hv']
      exact absurd hmn (mul_ne_zero hm0 hn0)
    · rw [hu2] at hu'
      rw [hv2] at hv'
      have hfac : (m - n) * (m + n) = 0 := by nlinarith [hu', hv']
      have hmn : m * n = -r := by nlinarith [hm, hu', hv']
      rcases mul_eq_zero.mp hfac with h | h
      · have hm : m = n := by linarith
        rw [hm] at hmn
        nlinarith [hr, hv', hmn]
      · have hm : m = -n := by linarith
        rw [hm] at hmn
        nlinarith [hr, hv', hmn]

theorem coxTriple_dep
    {I : Type} [Fintype I] [DecidableEq I] {C : Matrix I I ℤ} (hC : TauCeti.IsFiniteType C)
    (hord : ∀ (i j : I) (g h : (coxeterMatrix hC).Group),
      orderOf (g * (coxeterMatrix hC).simple i * g⁻¹ * (h * (coxeterMatrix hC).simple j * h⁻¹)) ≤ 4)
    (i₁ i₂ i₃ : I) (g₁ g₂ g₃ : (coxeterMatrix hC).Group)
    (h3 : orderOf (g₁ * (coxeterMatrix hC).simple i₁ * g₁⁻¹ * (g₂ * (coxeterMatrix hC).simple i₂ * g₂⁻¹)) = 3)
    (hdep : ∃ x y : ℚ, toRat (weylAction hC g₃ (Pi.single i₃ 1)) =
      x • toRat (weylAction hC g₁ (Pi.single i₁ 1)) + y • toRat (weylAction hC g₂ (Pi.single i₂ 1))) :
    g₃ * (coxeterMatrix hC).simple i₃ * g₃⁻¹ ∈
      Subgroup.closure ({g₁ * (coxeterMatrix hC).simple i₁ * g₁⁻¹,
        g₂ * (coxeterMatrix hC).simple i₂ * g₂⁻¹} : Set (coxeterMatrix hC).Group) := by
  change coxRefl hC g₃ i₃ ∈
    Subgroup.closure ({coxRefl hC g₁ i₁, coxRefl hC g₂ i₂} : Set (coxeterMatrix hC).Group)
  set t1 : (coxeterMatrix hC).Group := coxRefl hC g₁ i₁ with ht1
  set t2 : (coxeterMatrix hC).Group := coxRefl hC g₂ i₂ with ht2
  set t3 : (coxeterMatrix hC).Group := coxRefl hC g₃ i₃ with ht3
  set r1 : I → ℤ := coxRoot hC g₁ i₁ with hr1
  set r2 : I → ℤ := coxRoot hC g₂ i₂ with hr2
  set r3 : I → ℤ := coxRoot hC g₃ i₃ with hr3
  have hr1ne : toRat r1 ≠ 0 := by
    intro h
    have h0 : r1 = 0 := toRat_injective (show toRat r1 = toRat 0 by rw [h, map_zero])
    exact weylAction_single_ne_zero hC g₁ i₁ h0
  have hr2ne : toRat r2 ≠ 0 := by
    intro h
    have h0 : r2 = 0 := toRat_injective (show toRat r2 = toRat 0 by rw [h, map_zero])
    exact weylAction_single_ne_zero hC g₂ i₂ h0
  have hr3ne : toRat r3 ≠ 0 := by
    intro h
    have h0 : r3 = 0 := toRat_injective (show toRat r3 = toRat 0 by rw [h, map_zero])
    exact weylAction_single_ne_zero hC g₃ i₃ h0
  have hnp12 : ¬ ∃ q : ℚ, toRat r2 = q • toRat r1 := by
    rintro ⟨q, hq⟩
    have ht : t2 = t1 := by
      rw [ht2, ht1]
      exact coxRefl_eq_of_proportional hC g₁ g₂ i₁ i₂ q hq
    have ht1sq : t1 * t1 = 1 := by
      have hs : (coxeterMatrix hC).simple i₁ * (coxeterMatrix hC).simple i₁ = 1 :=
        CoxeterSystem.simple_mul_simple_self (coxeterMatrix hC).toCoxeterSystem i₁
      simp only [ht1, coxRefl]
      rw [show (g₁ * (coxeterMatrix hC).simple i₁ * g₁⁻¹) *
          (g₁ * (coxeterMatrix hC).simple i₁ * g₁⁻¹) =
          g₁ * ((coxeterMatrix hC).simple i₁ * (coxeterMatrix hC).simple i₁) * g₁⁻¹ by group,
        hs]
      group
    have h3' : orderOf (t1 * t2) = 3 := h3
    have : orderOf (t1 * t2) = 1 := by rw [ht, ht1sq, orderOf_one]
    omega
  have hprod12 : coxPairing hC r2 r1 * coxPairing hC r1 r2 = 1 := by
    have hA4 := orderOf_coxRefl_mul hC g₁ g₂ i₁ i₂ hnp12
    have h3' : orderOf (t1 * t2) = 3 := h3
    rcases coxPairing_mul_cases hC g₁ g₂ i₁ i₂ hnp12 with h0 | h1 | h2 | h3six
    · have h := hA4.1 h0
      rw [← ht1, ← ht2] at h
      omega
    · exact h1
    · have h := hA4.2.2.1 h2
      rw [← ht1, ← ht2] at h
      omega
    · have h := hA4.2.2.2 h3six
      rw [← ht1, ← ht2] at h
      omega
  obtain ⟨a, ha⟩ := exists_int_coxPairing hC g₁ i₁ r2
  obtain ⟨b, hb⟩ := exists_int_coxPairing hC g₂ i₂ r1
  have hab : a * b = 1 := by
    have h : (a : ℚ) * (b : ℚ) = 1 := by rw [ha, hb]; exact hprod12
    exact_mod_cast h
  let ε : ℚ := (a : ℚ)
  have hε : ε = 1 ∨ ε = -1 := by
    rcases Int.eq_one_or_neg_one_of_mul_eq_one hab with h | h
    · left; dsimp [ε]; rw [h]; norm_num
    · right; dsimp [ε]; rw [h]; norm_num
  have hε2 : ε ^ 2 = 1 := by rcases hε with h | h <;> rw [h] <;> norm_num
  have haε : ε = coxPairing hC r2 r1 := by dsimp [ε]; exact ha
  have hbε : ε = coxPairing hC r1 r2 := by
    dsimp [ε]
    rw [← hb]
    exact (by rw [Int.eq_of_mul_eq_one hab] : (b : ℚ) = (a : ℚ)).symm
  set L : ℚ := form hC (toRat r1) (toRat r1) with hL
  set c : ℚ := form hC (toRat r1) (toRat r2) with hcdef
  have hLpos : 0 < L := by rw [hL]; exact form_pos hC hr1ne
  have hc : c = ε * L / 2 := by
    have h : ε = 2 * c / L := by
      rw [haε, coxPairing, form_comm hC (toRat r2) (toRat r1), ← hcdef, ← hL]
    field_simp [hLpos.ne'] at h ⊢
    linarith
  have hL2 : form hC (toRat r2) (toRat r2) = L := by
    have h : ε = 2 * c / form hC (toRat r2) (toRat r2) := by
      rw [hbε, coxPairing, ← hcdef]
    rw [hc] at h
    have hne : form hC (toRat r2) (toRat r2) ≠ 0 := (form_pos hC hr2ne).ne'
    field_simp [hne] at h
    rcases hε with h1 | h1 <;> rw [h1] at h <;> linarith
  by_cases hp31 : ∃ q : ℚ, toRat r3 = q • toRat r1
  · obtain ⟨q, hq⟩ := hp31
    have ht : t3 = t1 := by
      rw [ht3, ht1]
      exact coxRefl_eq_of_proportional hC g₁ g₃ i₁ i₃ q hq
    rw [ht]
    exact Subgroup.subset_closure (by simp)
  by_cases hp32 : ∃ q : ℚ, toRat r3 = q • toRat r2
  · obtain ⟨q, hq⟩ := hp32
    have ht : t3 = t2 := by
      rw [ht3, ht2]
      exact coxRefl_eq_of_proportional hC g₂ g₃ i₂ i₃ q hq
    rw [ht]
    exact Subgroup.subset_closure (by simp)
  · have hnp31 : ¬ ∃ q : ℚ, toRat r1 = q • toRat r3 := by
      rintro ⟨q, hq⟩
      apply hp31
      rcases eq_or_ne q 0 with rfl | hq0
      · rw [zero_smul] at hq; exact absurd hq hr1ne
      · exact ⟨q⁻¹, by rw [hq, smul_smul, inv_mul_cancel₀ hq0, one_smul]⟩
    have hnp32 : ¬ ∃ q : ℚ, toRat r2 = q • toRat r3 := by
      rintro ⟨q, hq⟩
      apply hp32
      rcases eq_or_ne q 0 with rfl | hq0
      · rw [zero_smul] at hq; exact absurd hq hr2ne
      · exact ⟨q⁻¹, by rw [hq, smul_smul, inv_mul_cancel₀ hq0, one_smul]⟩
    obtain ⟨x, y, hxy0⟩ := hdep
    have hxy : toRat r3 = x • toRat r1 + y • toRat r2 := hxy0
    set B33 : ℚ := form hC (toRat r3) (toRat r3) with hB33def
    set rr : ℚ := B33 / L with hrrdef
    set m : ℚ := coxPairing hC r3 r1 with hmdef
    set n : ℚ := coxPairing hC r3 r2 with hndef
    have hB33 : B33 = L * (x ^ 2 + ε * x * y + y ^ 2) := by
      rw [hB33def, hxy]
      simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
      rw [← hL, form_comm hC (toRat r2) (toRat r1), ← hcdef, hc, hL2]
      ring
    have hrr : rr = x ^ 2 + ε * x * y + y ^ 2 := by
      rw [hrrdef, hB33]
      field_simp [hLpos.ne']
      try ring
    have hm : m = 2 * x + ε * y := by
      rw [hmdef, coxPairing, hxy]
      simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
      rw [← hL, form_comm hC (toRat r2) (toRat r1), ← hcdef, hc]
      field_simp [hLpos.ne']
      try ring
    have hn : n = ε * x + 2 * y := by
      rw [hndef, coxPairing, hxy]
      simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
      rw [← hcdef, hL2, hc]
      field_simp [hLpos.ne']
      try ring
    have hp13eq : coxPairing hC r1 r3 = m / rr := by
      have hB33ne : B33 ≠ 0 := by rw [hB33def]; exact (form_pos hC hr3ne).ne'
      rw [hmdef, hrrdef, coxPairing, coxPairing, form_comm hC (toRat r1) (toRat r3),
        ← hL, ← hB33def]
      field_simp [hLpos.ne', hB33ne]
      try ring
    have hp23eq : coxPairing hC r2 r3 = n / rr := by
      have hB33ne : B33 ≠ 0 := by rw [hB33def]; exact (form_pos hC hr3ne).ne'
      rw [hndef, hrrdef, coxPairing, coxPairing, form_comm hC (toRat r2) (toRat r3),
        hL2, ← hB33def]
      field_simp [hLpos.ne', hB33ne]
      try ring
    have hp13mem : m * (m / rr) = 0 ∨ m * (m / rr) = 1 ∨ m * (m / rr) = 2 := by
      have hA4 := orderOf_coxRefl_mul hC g₃ g₁ i₃ i₁ hnp31
      rcases coxPairing_mul_cases hC g₃ g₁ i₃ i₁ hnp31 with h0 | h1 | h2 | h3six
      · left; rw [hp13eq, ← hmdef, mul_comm] at h0; exact h0
      · right; left; rw [hp13eq, ← hmdef, mul_comm] at h1; exact h1
      · right; right; rw [hp13eq, ← hmdef, mul_comm] at h2; exact h2
      · exfalso
        have h6 : orderOf (g₃ * (coxeterMatrix hC).simple i₃ * g₃⁻¹ *
            (g₁ * (coxeterMatrix hC).simple i₁ * g₁⁻¹)) = 6 := hA4.2.2.2 h3six
        have h4 := hord i₃ i₁ g₃ g₁
        omega
    have hp23mem : n * (n / rr) = 0 ∨ n * (n / rr) = 1 ∨ n * (n / rr) = 2 := by
      have hA4 := orderOf_coxRefl_mul hC g₃ g₂ i₃ i₂ hnp32
      rcases coxPairing_mul_cases hC g₃ g₂ i₃ i₂ hnp32 with h0 | h1 | h2 | h3six
      · left; rw [hp23eq, ← hndef, mul_comm] at h0; exact h0
      · right; left; rw [hp23eq, ← hndef, mul_comm] at h1; exact h1
      · right; right; rw [hp23eq, ← hndef, mul_comm] at h2; exact h2
      · exfalso
        have h6 : orderOf (g₃ * (coxeterMatrix hC).simple i₃ * g₃⁻¹ *
            (g₂ * (coxeterMatrix hC).simple i₂ * g₂⁻¹)) = 6 := hA4.2.2.2 h3six
        have h4 := hord i₃ i₂ g₃ g₂
        omega
    have hrrpos : 0 < rr := by
      rw [hrrdef]
      exact div_pos (by rw [hB33def]; exact form_pos hC hr3ne) hLpos
    have h3r : 3 * rr = m ^ 2 - ε * m * n + n ^ 2 := by
      rw [hm, hn, hrr]; nlinarith [hε2]
    have hint_m : ∃ z : ℤ, (z : ℚ) = m := by
      obtain ⟨z, hz⟩ := exists_int_coxPairing hC g₁ i₁ r3
      exact ⟨z, by rw [hmdef]; exact hz⟩
    have hint_mr : ∃ z : ℤ, (z : ℚ) = m / rr := by
      obtain ⟨z, hz⟩ := exists_int_coxPairing hC g₃ i₃ r1
      exact ⟨z, by rw [← hp13eq]; exact hz⟩
    obtain ⟨hrr1, hn_eq⟩ :=
      ct_dep_arith hε hrrpos h3r rfl rfl hp13mem hp23mem hint_m hint_mr
    have hyx : y = -ε * x := by
      have h1 : ε * x + 2 * y = -ε * (2 * x + ε * y) := by rw [← hn, hn_eq, hm]
      have h2 : ε * (2 * x + ε * y) = 2 * (ε * x) + ε ^ 2 * y := by ring
      rw [neg_mul] at h1
      rw [h2, hε2] at h1
      linarith
    have hρ : toRat (coxRoot hC (t2 * g₁) i₁) = toRat r1 - ε • toRat r2 := by
      have h1 : coxRoot hC (t2 * g₁) i₁ = weylAction hC t2 r1 := by
        simp only [coxRoot, weylAction_mul_apply, hr1]
      rw [h1]
      have h2 : toRat (weylAction hC t2 r1) = toRat r1 - coxPairing hC r1 r2 • toRat r2 := by
        rw [ht2]
        exact toRat_weylAction_coxRefl hC g₂ i₂ r1
      rw [h2, hbε]
    have hq : toRat r3 = x • toRat (coxRoot hC (t2 * g₁) i₁) := by
      rw [hxy, hρ, hyx]
      module
    have ht3eq : t3 = coxRefl hC (t2 * g₁) i₁ :=
      coxRefl_eq_of_proportional hC (t2 * g₁) g₃ i₁ i₃ x hq
    have hconj : coxRefl hC (t2 * g₁) i₁ = t2 * t1 * t2⁻¹ := by
      rw [ht1, ht2]
      simp only [coxRefl]
      group
    rw [ht3eq, hconj]
    refine Subgroup.mul_mem _ (Subgroup.mul_mem _ ?_ ?_) (Subgroup.inv_mem _ ?_)
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)

end CFSG.StandardType.CoxTriple

end
