module

public import CFSG.LocalAnalysis.StandardType.GGSixTrialityL613KGTorus

public section

namespace CFSG.StandardType

namespace L613KG

open Module CFSG.StandardType.Triality CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData CFSG.LieType.Universal.Spin
  CFSG.RankThree.PartOne.AUTSL CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.StandardType.D4Rank QuadraticMap
open scoped Matrix

variable {K : Type} [Field K]

section Diag

theorem eq_smul_single_of_diag {μ : Fin (2 * 4) → K} {j₀ : Fin (2 * 4)}
    (huniq : ∀ j, j ≠ j₀ → μ j ≠ μ j₀) {v : Fin (2 * 4) → K}
    (hv : (fun j => μ j * v j) = μ j₀ • v) : v = v j₀ • Pi.single j₀ 1 := by
  funext j
  by_cases hj : j = j₀
  · subst hj
    simp
  · have h := congrFun hv j
    simp only [Pi.smul_apply, smul_eq_mul] at h
    have h0 : (μ j - μ j₀) * v j = 0 := by rw [sub_mul, h, sub_self]
    rcases mul_eq_zero.mp h0 with h1 | h1
    · exact absurd (sub_eq_zero.mp h1) (huniq j hj)
    · simp [h1, hj]

theorem single_smul_of_diag (μ : Fin (2 * 4) → K) (j : Fin (2 * 4)) :
    (fun i => μ i * (Pi.single j (1 : K) : Fin (2 * 4) → K) i) = μ j • Pi.single j 1 := by
  funext i
  by_cases hi : i = j
  · subst hi
    simp
  · simp [hi]

theorem act_eq_of_single {z : Om8 K} {cz : Fin (2 * 4) → K}
    (h : ∀ j, act z (Pi.single j 1) = cz j • Pi.single j 1) (v : Fin (2 * 4) → K) :
    act z v = fun j => cz j * v j := by
  have e : act z v = ∑ i, v i • act z (Pi.single i 1) := by
    conv_lhs => rw [pi_eq_sum_univ' v]
    rw [act, Matrix.mulVec_sum]
    simp only [Matrix.mulVec_smul]
  rw [e]
  funext j
  simp only [h, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
  simp [mul_comm]

theorem omFixDim_eq_card_of_diag {z : Om8 K} {cz : Fin (2 * 4) → K}
    (hz : ∀ v, act z v = fun j => cz j * v j) :
    omFixDim z = Nat.card {j // cz j = 1} := by
  classical
  set f : {j // cz j = 1} → Fin (2 * 4) → K := fun j => Pi.single j.1 1 with hf
  have hli : LinearIndependent K f := by
    have h := (Pi.basisFun K (Fin (2 * 4))).linearIndependent.comp
      (Subtype.val : {j // cz j = 1} → Fin (2 * 4)) Subtype.val_injective
    convert h using 1
    funext j
    simp [hf]
  have hker : LinearMap.ker (omRep z - 1) = Submodule.span K (Set.range f) := by
    apply le_antisymm
    · intro v hv
      have hv' : act z v = v := mem_ker_iff_act.mp hv
      rw [hz] at hv'
      have hvj : ∀ j, cz j ≠ 1 → v j = 0 := by
        intro j hj
        have h1 := congrFun hv' j
        have h2 : (cz j - 1) * v j = 0 := by rw [sub_mul, h1, one_mul, sub_self]
        rcases mul_eq_zero.mp h2 with h3 | h3
        · exact absurd (sub_eq_zero.mp h3) hj
        · exact h3
      rw [pi_eq_sum_univ' v]
      refine Submodule.sum_mem _ fun j _ => ?_
      by_cases hj : cz j = 1
      · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨j, hj⟩, rfl⟩)
      · rw [hvj j hj, zero_smul]
        exact Submodule.zero_mem _
    · rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      refine mem_ker_iff_act.mpr ?_
      rw [hz, hf]
      simp only
      rw [single_smul_of_diag cz j.1, j.2, one_smul]
  rw [omFixDim, fixDim, hker, finrank_span_eq_card hli, Nat.card_eq_fintype_card]

theorem card_fix_ne_four {cz : Fin (2 * 4) → K} (hpair : ∀ k, cz (ie k) * cz (jf k) = 1)
    (h01 : cz (ie 1) = cz (ie 0)) (h02 : cz (ie 2) = cz (ie 0)) :
    Nat.card {j // cz j = 1} ≠ 4 := by
  classical
  have hjf : ∀ k, (cz (jf k) = 1 ↔ cz (ie k) = 1) := by
    intro k
    constructor
    · intro h
      have := hpair k
      rwa [h, mul_one] at this
    · intro h
      have := hpair k
      rwa [h, one_mul] at this
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter,
    ← Equiv.sum_comp (plusIndexEquiv 4), Fintype.sum_sum_type, Fin.sum_univ_four, Fin.sum_univ_four]
  change (if cz (ie 0) = 1 then 1 else 0) + (if cz (ie 1) = 1 then 1 else 0) +
      (if cz (ie 2) = 1 then 1 else 0) + (if cz (ie 3) = 1 then 1 else 0) +
      ((if cz (jf 0) = 1 then 1 else 0) + (if cz (jf 1) = 1 then 1 else 0) +
      (if cz (jf 2) = 1 then 1 else 0) + (if cz (jf 3) = 1 then 1 else 0)) ≠ 4
  simp only [hjf, h01, h02]
  by_cases ha : cz (ie 0) = 1 <;> by_cases hb : cz (ie 3) = 1 <;> simp [ha, hb]

end Diag

section Commute

variable [Finite K] [CharP K 2]

theorem act_dg_single (c : Fin 4 → Kˣ) (j : Fin (2 * 4)) :
    act (dg c) (Pi.single j 1) = ((twHom c j : Kˣ) : K) • Pi.single j 1 := by
  rw [act_dg]
  exact single_smul_of_diag _ j

omit [Finite K] [CharP K 2] in
theorem units_facts {ω : Kˣ} (hω : orderOf ω = 3) : ω ≠ 1 ∧ ω⁻¹ ≠ 1 ∧ ω⁻¹ ≠ ω := by
  have h1 : ω ≠ 1 := fun h => by rw [h, orderOf_one] at hω; exact absurd hω (by norm_num)
  refine ⟨h1, fun h => h1 (inv_eq_one.mp h), fun h => ?_⟩
  have h2 : ω ^ 2 = 1 := by rw [pow_two]; nth_rw 1 [← h]; exact inv_mul_cancel ω
  have := orderOf_dvd_of_pow_eq_one h2
  rw [hω] at this
  exact absurd this (by norm_num)

omit [Finite K] [CharP K 2] in
theorem twHom_mulSingle_ne_ie {ω : Kˣ} (hω : orderOf ω = 3) (k : Fin 4) (j : Fin (2 * 4))
    (hj : j ≠ ie k) :
    ((twHom (Pi.mulSingle k ω) j : Kˣ) : K) ≠ ((twHom (Pi.mulSingle k ω) (ie k) : Kˣ) : K) := by
  obtain ⟨h1, h2, h3⟩ := units_facts hω
  intro h
  have h' := Units.ext h
  rw [twHom_ie, Pi.mulSingle_eq_same] at h'
  rcases ie_or_jf j with ⟨l, rfl⟩ | ⟨l, rfl⟩
  · have hl : l ≠ k := fun hl => hj (by rw [hl])
    rw [twHom_ie, Pi.mulSingle_eq_of_ne hl] at h'
    exact h1 h'.symm
  · rw [twHom_jf] at h'
    by_cases hl : l = k
    · subst hl
      rw [Pi.mulSingle_eq_same] at h'
      exact h3 h'
    · rw [Pi.mulSingle_eq_of_ne hl, inv_one] at h'
      exact h1 h'.symm

omit [Finite K] [CharP K 2] in
theorem twHom_mulSingle_ne_jf {ω : Kˣ} (hω : orderOf ω = 3) (k : Fin 4) (j : Fin (2 * 4))
    (hj : j ≠ jf k) :
    ((twHom (Pi.mulSingle k ω) j : Kˣ) : K) ≠ ((twHom (Pi.mulSingle k ω) (jf k) : Kˣ) : K) := by
  obtain ⟨h1, h2, h3⟩ := units_facts hω
  intro h
  have h' := Units.ext h
  rw [twHom_jf, Pi.mulSingle_eq_same] at h'
  rcases ie_or_jf j with ⟨l, rfl⟩ | ⟨l, rfl⟩
  · rw [twHom_ie] at h'
    by_cases hl : l = k
    · subst hl
      rw [Pi.mulSingle_eq_same] at h'
      exact h3 h'.symm
    · rw [Pi.mulSingle_eq_of_ne hl] at h'
      exact h2 h'.symm
  · have hl : l ≠ k := fun hl => hj (by rw [hl])
    rw [twHom_jf, Pi.mulSingle_eq_of_ne hl, inv_one] at h'
    exact h2 h'.symm

theorem act_single_eq_of_commute {ω : Kˣ} (hω : orderOf ω = 3) {z : Om8 K}
    (hz : ∀ k, z * dg (Pi.mulSingle k ω) = dg (Pi.mulSingle k ω) * z) (j : Fin (2 * 4)) :
    act z (Pi.single j 1) = act z (Pi.single j 1) j • Pi.single j 1 := by
  have key : ∀ k, act (dg (Pi.mulSingle k ω)) (act z (Pi.single j 1)) =
      ((twHom (Pi.mulSingle k ω) j : Kˣ) : K) • act z (Pi.single j 1) := fun k => by
    rw [← act_mul, ← hz k, act_mul, act_dg_single, act_smul]
  rcases ie_or_jf j with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · have h1 := key k
    rw [act_dg] at h1
    exact eq_smul_single_of_diag (μ := fun i => ((twHom (Pi.mulSingle k ω) i : Kˣ) : K))
      (twHom_mulSingle_ne_ie hω k) h1
  · have h1 := key k
    rw [act_dg] at h1
    exact eq_smul_single_of_diag (μ := fun i => ((twHom (Pi.mulSingle k ω) i : Kˣ) : K))
      (twHom_mulSingle_ne_jf hω k) h1

theorem act_eq_of_commute {ω : Kˣ} (hω : orderOf ω = 3) {z : Om8 K}
    (hz : ∀ k, z * dg (Pi.mulSingle k ω) = dg (Pi.mulSingle k ω) * z) (v : Fin (2 * 4) → K) :
    act z v = fun j => act z (Pi.single j 1) j * v j :=
  act_eq_of_single (fun j => act_single_eq_of_commute hω hz j) v

end Commute

section Triality

variable [Finite K] [CharP K 2]

theorem omFixDim_two_or_four {α : MulAut (Om8 K)} (hα3 : α ^ 3 = 1)
    (hns : ∀ g : similarityPairs (coordinateQuadPlus 4 K), conjAct _ g ≠ α) {e : Om8 K}
    (he3 : e ^ 3 = 1) (he1 : e ≠ 1) (hfix : α e = e) : omFixDim e = 2 ∨ omFixDim e = 4 := by
  have hcls := ggD4TrialityClassInput_holds
  obtain ⟨γ, k, σ, hk, rfl⟩ := exists_conj_theta_pow_fieldAutP α hα3 hns
  set φ := AutOm.fieldAutP 4 σ with hφ
  have hθφ : ∀ j : ℕ, ∀ y : Om8 K, (theta ^ j) (φ y) = φ ((theta ^ j) y) := by
    intro j y
    rw [← MulAut.mul_apply, ← MulAut.mul_apply,
      (Commute.pow_left (theta_fieldAutP σ : Commute theta φ) j).eq]
  have hpair : ((theta : MulAut (Om8 K)) ^ k = theta ∧ (theta : MulAut (Om8 K)) ^ (k + k) =
      theta⁻¹) ∨ ((theta : MulAut (Om8 K)) ^ k = theta⁻¹ ∧
        (theta : MulAut (Om8 K)) ^ (k + k) = theta) := by
    rcases hk with rfl | rfl
    · exact Or.inl ⟨pow_one _, theta_sq⟩
    · refine Or.inr ⟨theta_sq, ?_⟩
      rw [show 2 + 2 = 3 + 1 from rfl, pow_succ, theta_cube, one_mul]
  have hd1 : omFixDim ((theta ^ k) (φ e)) = omFixDim e := by
    have h := hfix
    rw [MulAut.mul_apply, MulAut.mul_apply] at h
    rw [← omFixDim_conj γ, h]
  have hd2 : omFixDim ((theta ^ (k + k)) (φ (φ e))) = omFixDim e := by
    have h2 : (MulAut.conj γ * (theta ^ k * φ)) ^ 2 =
        MulAut.conj (γ * (theta ^ k * φ : MulAut (Om8 K)) γ) * (theta ^ (k + k) * (φ * φ)) := by
      rw [conj_mul_sq, _root_.sq (theta ^ k * φ), mul_assoc, ← mul_assoc φ,
        ← (Commute.pow_left (theta_fieldAutP σ : Commute theta φ) k).eq, mul_assoc,
        ← mul_assoc (theta ^ k), ← pow_add]
    have hα2 : ((MulAut.conj γ * (theta ^ k * φ) : MulAut (Om8 K)) ^ 2) e = e := by
      rw [_root_.sq, MulAut.mul_apply, hfix, hfix]
    rw [h2, MulAut.mul_apply] at hα2
    have h := omFixDim_conj (γ * (theta ^ k * φ : MulAut (Om8 K)) γ)
      ((theta ^ (k + k) * (φ * φ) : MulAut (Om8 K)) e)
    rw [hα2] at h
    exact h.symm
  have hy3 : φ e ^ 3 = 1 := by rw [← map_pow, he3, map_one]
  have hdy : omFixDim (φ e) = omFixDim e := omFixDim_fieldAutP σ e
  have hle : omFixDim e ≤ 8 := by
    have := Submodule.finrank_le (LinearMap.ker (omRep e - 1))
    rwa [Module.finrank_fin_fun] at this
  have h8 : omFixDim e ≠ 8 := fun h => he1 (eq_one_of_omFixDim h)
  obtain ⟨j, hj⟩ := omFixDim_even e he3
  have h6 : omFixDim e ≠ 6 := by
    intro h6
    obtain ⟨ha, hb⟩ := (hcls K (φ e) hy3).1 (hdy.trans h6)
    rcases hpair with ⟨hk1, -⟩ | ⟨hk1, -⟩ <;> rw [hk1] at hd1 <;> omega
  have h0 : omFixDim e ≠ 0 := by
    intro h0
    have h := (hcls K (φ e) hy3).2 (hdy.trans h0)
    rw [hθφ, omFixDim_fieldAutP] at hd2
    rcases hpair with ⟨hk1, hk2⟩ | ⟨hk1, hk2⟩ <;> rw [hk1] at hd1 <;> rw [hk2] at hd2 <;>
      rcases h with h | h <;> omega
  omega

end Triality

theorem omFixDim_ne_four_of_not_dvd [Finite K] [CharP K 2] (hK3 : 3 ∣ Nat.card K - 1)
    {z : Om8 K} (hidx : ¬ 3 ∣ (Subgroup.centralizer {z}).index) : omFixDim z ≠ 4 := by
  intro h
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨ω, hω⟩ : ∃ ω : Kˣ, orderOf ω = 3 :=
    exists_prime_orderOf_dvd_card' 3 (by rw [Nat.card_units]; exact hK3)
  have hω3 : ω ^ 3 = 1 := by rw [← hω]; exact pow_orderOf_eq_one ω
  obtain ⟨S, hS⟩ := exists_sylow_le_of_not_dvd (p := 3) hidx
  obtain ⟨S', hS'⟩ := (isPGroup_pZero (K := K)).exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Om8 K) S S'
  have hcomm : ∀ x ∈ pZero (K := K), (g * z * g⁻¹) * x = x * (g * z * g⁻¹) := by
    intro x hx
    have hx' : x ∈ (S' : Subgroup (Om8 K)) := hS' hx
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hx'
    obtain ⟨s, hs, rfl⟩ := hx'
    have hsz : s * z = z * s := Subgroup.mem_centralizer_singleton_iff.mp (hS hs)
    simp only [MulAut.smul_def, MulAut.conj_apply]
    calc g * z * g⁻¹ * (g * s * g⁻¹) = g * (z * s) * g⁻¹ := by group
      _ = g * (s * z) * g⁻¹ := by rw [hsz]
      _ = g * s * g⁻¹ * (g * z * g⁻¹) := by group
  have hdz : omFixDim (g * z * g⁻¹) = omFixDim z := by
    rw [← MulAut.conj_apply]
    exact omFixDim_conj g z
  have hE : ∀ k, (g * z * g⁻¹) * dg (Pi.mulSingle k ω) = dg (Pi.mulSingle k ω) * (g * z * g⁻¹) :=
    fun k => hcomm _ (dg_mem_pZero (by
      funext l
      simp only [Pi.pow_apply, Pi.one_apply]
      by_cases hl : l = k
      · subst hl
        rw [Pi.mulSingle_eq_same, hω3]
      · rw [Pi.mulSingle_eq_of_ne hl, one_pow]))
  have hW : (g * z * g⁻¹) * wg = wg * (g * z * g⁻¹) := hcomm _ wg_mem_pZero
  set z' := g * z * g⁻¹ with hz'
  set cz : Fin (2 * 4) → K := fun j => act z' (Pi.single j 1) j with hcz
  have hact : ∀ v, act z' v = fun j => cz j * v j := act_eq_of_commute hω hE
  have hsingle : ∀ j, act z' (Pi.single j 1) = cz j • Pi.single j 1 := fun j => by
    rw [hact]
    exact single_smul_of_diag cz j
  have hpair : ∀ k, cz (ie k) * cz (jf k) = 1 := by
    intro k
    have h1 := polar_act z' (Pi.single (ie k) 1) (Pi.single (jf k) 1)
    rw [hsingle, hsingle, polar_smul_left, polar_smul_right, polar_single_ie_jf] at h1
    simpa using h1
  have hperm : ∀ j, cz j = cz (pi3 j) := by
    intro j
    have h1 : act (z' * wg) (Pi.single (pi3 j) 1) j = act (wg * z') (Pi.single (pi3 j) 1) j := by
      rw [hW]
    simp only [act_mul, act_wg, hact, Function.comp_apply] at h1
    simpa using h1
  have h01 : cz (ie 1) = cz (ie 0) := by rw [hperm (ie 0), pi3_ie, sig3_zero]
  have h02 : cz (ie 2) = cz (ie 0) := by rw [hperm (ie 2), pi3_ie, sig3_two]
  exact card_fix_ne_four hpair h01 h02 ((omFixDim_eq_card_of_diag hact).symm.trans (hdz.trans h))

theorem _root_.CFSG.StandardType.ggD4CentralClassThreeInput_holds : GGD4CentralClassThreeInput := by
  intro K _ _ _ hK3 z hz3 hz1 hidx α hα3 hns hαz
  rcases omFixDim_two_or_four hα3 hns hz3 hz1 hαz with h | h
  · exact h
  · exact absurd h (omFixDim_ne_four_of_not_dvd hK3 hidx)

end L613KG

end CFSG.StandardType
