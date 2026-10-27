module

public import CFSG.HardMathSupport.Solomon.Coordinator.BGLLNorm
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.GH74.GLS.IVK.L2.Fixed
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherSemilinearData

public section

namespace CFSG.RankThree.PartTwo.Sec19.Item19Res6Proof

open CFSG.LocalAnalysis.ComponentInitial
open CFSG.GH74.GLS.IVK (fixedField mem_fixedField_iff fixedField_apply)

theorem ringEquiv_fix_of_cube {F : Type*} [Field F] {σ : F ≃+* F} (hσ : σ ^ 3 = 1) {ω : F}
    (hω3 : ω ^ 3 = 1) : σ ω = ω := by
  by_cases hω1 : ω = 1
  · rw [hω1, map_one]
  have hω : ω ^ 2 + ω + 1 = 0 := by
    have h1 : (ω - 1) * (ω ^ 2 + ω + 1) = 0 := by linear_combination hω3
    exact (mul_eq_zero.1 h1).resolve_left (sub_ne_zero.2 hω1)
  have hy3 : (σ ω) ^ 3 = 1 := by rw [← map_pow, hω3, map_one]
  have hfac : (σ ω - 1) * ((σ ω - ω) * (σ ω - ω ^ 2)) = 0 := by
    linear_combination hy3 - (σ ω) ^ 2 * hω + (σ ω) * (hω + hω3) - hω3
  have hσ3 : ∀ x, σ (σ (σ x)) = x := fun x => by
    have := congrArg (fun τ : F ≃+* F => τ x) hσ
    simpa [pow_succ] using this
  rcases mul_eq_zero.1 hfac with h | h
  · exact absurd (σ.injective ((sub_eq_zero.1 h).trans (map_one σ).symm)) hω1
  rcases mul_eq_zero.1 h with h | h
  · exact sub_eq_zero.1 h
  · exfalso
    have h1 : σ ω = ω ^ 2 := sub_eq_zero.1 h
    have h2 : σ (σ ω) = ω ^ 4 := by rw [h1, map_pow, h1]; ring
    have h3 : σ (σ (σ ω)) = ω ^ 8 := by rw [h2, map_pow, h1]; ring
    rw [hσ3] at h3
    apply hω1
    have h4 : ω ^ 8 = ω ^ 2 := by
      calc ω ^ 8 = (ω ^ 3) ^ 2 * ω ^ 2 := by ring
        _ = ω ^ 2 := by rw [hω3]; ring
    have h5 : ω = ω ^ 2 := h3.trans h4
    have hω0 : ω ≠ 0 := by rintro rfl; norm_num at hω3
    have : ω * (ω - 1) = 0 := by linear_combination h5.symm
    exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left hω0)

variable {p f : ℕ} {K : Type} [Field K]

theorem eq_one_of_bar_eq_of_cube (h : UnitaryFieldData p f K) (hQ : p ^ f % 3 = 2) {n : K}
    (hbar : h.bar n = n) (hn3 : n ^ 3 = 1) : n = 1 := by
  have hn0 : n ≠ 0 := by rintro rfl; norm_num at hn3
  rw [UnitaryFieldData.bar_apply] at hbar
  obtain ⟨m, hm⟩ : ∃ m, p ^ f = 3 * m + 2 := ⟨p ^ f / 3, by omega⟩
  rw [hm, pow_add, pow_mul, hn3, one_pow, one_mul] at hbar
  have : n * (n - 1) = 0 := by linear_combination hbar
  exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left hn0)

theorem bar_eq_of_cube (h : UnitaryFieldData p f K) (hQ : p ^ f % 3 = 2) {c : K}
    (hc : c ^ 3 = 1) : h.bar c = c ^ 2 := by
  rw [UnitaryFieldData.bar_apply]
  obtain ⟨m, hm⟩ : ∃ m, p ^ f = 3 * m + 2 := ⟨p ^ f / 3, by omega⟩
  rw [hm, pow_add, pow_mul, hc, one_pow, one_mul]

theorem bar_norm_eq (h : UnitaryFieldData p f K) (d : K) : h.bar (h.norm d) = h.norm d := by
  rw [UnitaryFieldData.norm, map_mul, h.bar_bar, mul_comm]

theorem norm_pow_three (h : UnitaryFieldData p f K) (d : K) :
    h.norm (d ^ 3) = h.norm d ^ 3 := by
  rw [UnitaryFieldData.norm, UnitaryFieldData.norm, map_pow, mul_pow]

theorem norm_eq_one_of_pow_three (h : UnitaryFieldData p f K) (hQ : p ^ f % 3 = 2) {d α : K}
    (hα : h.norm α = 1) (hd : d ^ 3 = α) : h.norm d = 1 := by
  refine eq_one_of_bar_eq_of_cube h hQ (bar_norm_eq h d) ?_
  rw [← norm_pow_three, hd, hα]

theorem exists_norm_one_twist (h : UnitaryFieldData p f K) (hQ : p ^ f % 3 = 2) {σ : K ≃+* K}
    (hσ : orderOf σ = 3) {c : K} (hc : c ^ 3 = 1) :
    ∃ μ : K, μ ≠ 0 ∧ h.norm μ = 1 ∧ σ μ = c * μ := by
  have hσ3 : σ ^ 3 = 1 := by rw [← hσ]; exact pow_orderOf_eq_one σ
  have hσc : σ c = c := ringEquiv_fix_of_cube hσ3 hc
  have hc0 : c ≠ 0 := by rintro rfl; norm_num at hc
  obtain ⟨y, hy0, hy⟩ := CFSG.HardMathSupport.Solomon.Coordinator.bgll_hilbert90 hσ (l := c)
    (by rw [hσc, hσc]; linear_combination hc)
  have hby0 : h.bar y ≠ 0 := (map_ne_zero h.bar).2 hy0
  have hσy : σ y = c⁻¹ * y := by
    field_simp
    linear_combination hy
  have hbc : h.bar c = c ^ 2 := bar_eq_of_cube h hQ hc
  refine ⟨y / h.bar y, div_ne_zero hy0 hby0, ?_, ?_⟩
  · rw [UnitaryFieldData.norm, map_div₀, h.bar_bar]
    field_simp
  · rw [map_div₀, CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.map_bar_comm h σ y, hσy,
      map_mul, map_inv₀, hbc]
    field_simp

theorem card_rootsOfUnity_eq (h : UnitaryFieldData p f K) :
    Nat.card (rootsOfUnity (p ^ f + 1) K) = p ^ f + 1 := by
  rw [← h.ker_normUnits]
  exact h.card_ker_normUnits_and_surjective.1

theorem pow_succ_eq_one_of_mem {k : Subfield K} [Finite k] {e : ℕ} (hfe : f = 3 * e)
    (hk : Nat.card k = p ^ (2 * e)) {w : K} (hwk : w ∈ k) (hw : w ^ (p ^ f + 1) = 1) :
    w ^ (p ^ e + 1) = 1 := by
  have := Fintype.ofFinite k
  have h1 : (⟨w, hwk⟩ : k) ^ Fintype.card k = ⟨w, hwk⟩ := FiniteField.pow_card _
  rw [← Nat.card_eq_fintype_card, hk] at h1
  have h2 : w ^ p ^ (2 * e) = w := congrArg Subtype.val h1
  have h3 : p ^ f = p ^ (2 * e) * p ^ e := by rw [hfe, ← pow_add]; ring_nf
  rw [h3, pow_succ, pow_mul, h2] at hw
  rw [pow_succ]
  exact hw

@[expose] noncomputable def normOneTwist (σ : K ≃+* K) (n : ℕ) :
    rootsOfUnity n K →* rootsOfUnity n K where
  toFun w := ⟨Units.map (σ : K →* K) (w : Kˣ) * (w : Kˣ)⁻¹, by
    rw [mem_rootsOfUnity, mul_pow, ← map_pow, (mem_rootsOfUnity _ _).1 w.2, map_one, inv_pow,
      (mem_rootsOfUnity _ _).1 w.2, inv_one, one_mul]⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' a b := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, map_mul, mul_inv]
    rw [mul_mul_mul_comm]

theorem coe_normOneTwist (σ : K ≃+* K) (n : ℕ) (w : rootsOfUnity n K) :
    ((normOneTwist σ n w : rootsOfUnity n K) : Kˣ) =
      Units.map (σ : K →* K) (w : Kˣ) * (w : Kˣ)⁻¹ :=
  rfl

theorem exists_norm_one_twisted (h : UnitaryFieldData p f K) {σ : K ≃+* K} (hσ : orderOf σ = 3)
    {e : ℕ} (hfe : f = 3 * e) (hk : Nat.card (fixedField σ) = p ^ (2 * e)) (hq : 2 < p ^ e) :
    ∃ u : K, u ≠ 0 ∧ h.norm u = 1 ∧ u * σ u * σ (σ u) = 1 ∧ u * (σ u)⁻¹ ∉ fixedField σ := by
  classical
  have := h.finite
  have hkfin : Finite (fixedField σ) := Subtype.finite
  have hσ3 : σ ^ 3 = 1 := by rw [← hσ]; exact pow_orderOf_eq_one σ
  have hσσσ : ∀ x, σ (σ (σ x)) = x := fun x => by
    have := congrArg (fun τ : K ≃+* K => τ x) hσ3
    simpa [pow_succ] using this
  set U := rootsOfUnity (p ^ f + 1) K with hU
  set τ := normOneTwist σ (p ^ f + 1) with hτ
  have hUcard : Nat.card U = p ^ f + 1 := card_rootsOfUnity_eq h
  have hker : Nat.card τ.ker ≤ p ^ e + 1 := by
    have hinj : Function.Injective (fun w : τ.ker =>
        (⟨((w : U) : Kˣ), by
          have hw := w.2
          rw [MonoidHom.mem_ker] at hw
          have hfix : σ (((w : U) : Kˣ) : K) = (((w : U) : Kˣ) : K) := by
            have h1 := congrArg (fun v : U => ((v : Kˣ) : K)) hw
            simp only [hτ, coe_normOneTwist, Units.val_mul, Units.coe_map, MonoidHom.coe_ofClass,
              OneMemClass.coe_one, Units.val_one, Units.val_inv_eq_inv_val] at h1
            have h0 : (((w : U) : Kˣ) : K) ≠ 0 := Units.ne_zero _
            field_simp at h1
            exact h1
          have hmem : (((w : U) : Kˣ) : K) ∈ fixedField σ := (mem_fixedField_iff σ _).2 hfix
          have hpow : (((w : U) : Kˣ) : K) ^ (p ^ f + 1) = 1 := by
            have := (mem_rootsOfUnity _ _).1 (w : U).2
            rw [← Units.val_pow_eq_pow_val, this, Units.val_one]
          rw [mem_rootsOfUnity]
          apply Units.ext
          rw [Units.val_pow_eq_pow_val, Units.val_one]
          exact pow_succ_eq_one_of_mem hfe hk hmem hpow⟩ :
          rootsOfUnity (p ^ e + 1) K)) := by
      intro a b hab
      apply Subtype.ext
      apply Subtype.ext
      have := congrArg (fun v : rootsOfUnity (p ^ e + 1) K => (v : Kˣ)) hab
      exact this
    have h1 := Nat.card_le_card_of_injective _ hinj
    have h2 : Nat.card (rootsOfUnity (p ^ e + 1) K) ≤ p ^ e + 1 := card_rootsOfUnity K _
    omega
  have hmul : Nat.card τ.ker * Nat.card τ.range = p ^ f + 1 := by
    have h1 := Subgroup.card_mul_index τ.ker
    rw [Subgroup.index_ker] at h1
    rw [h1]
    exact hUcard
  obtain ⟨v, hvR, hv3⟩ : ∃ v ∈ τ.range, ((v : Kˣ) : K) ^ 3 ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hle : Nat.card τ.range ≤ 3 := by
      have hinj : Function.Injective (fun v : τ.range =>
          (⟨((v : U) : Kˣ), by
            rw [mem_rootsOfUnity]
            apply Units.ext
            rw [Units.val_pow_eq_pow_val, Units.val_one]
            exact hcon _ v.2⟩ : rootsOfUnity 3 K)) := by
        intro a b hab
        apply Subtype.ext
        apply Subtype.ext
        have := congrArg (fun w : rootsOfUnity 3 K => (w : Kˣ)) hab
        exact this
      have h1 := Nat.card_le_card_of_injective _ hinj
      have h2 : Nat.card (rootsOfUnity 3 K) ≤ 3 := card_rootsOfUnity K _
      omega
    have hpf : p ^ f = (p ^ e) ^ 3 := by rw [hfe, ← pow_mul, mul_comm]
    have h3 : p ^ f + 1 ≤ (p ^ e + 1) * 3 := by
      calc p ^ f + 1 = Nat.card τ.ker * Nat.card τ.range := hmul.symm
        _ ≤ (p ^ e + 1) * 3 := Nat.mul_le_mul hker hle
    rw [hpf] at h3
    set q := p ^ e
    have hq3 : 3 ≤ q := hq
    have h9 : 9 * q ≤ q ^ 3 := by
      calc 9 * q = 3 * 3 * q := by ring
        _ ≤ q * q * q := Nat.mul_le_mul (Nat.mul_le_mul hq3 hq3) le_rfl
        _ = q ^ 3 := by ring
    omega
  obtain ⟨w, rfl⟩ := hvR
  set u : K := (((τ w : U) : Kˣ) : K) with hu
  have hw0 : (((w : U) : Kˣ) : K) ≠ 0 := Units.ne_zero _
  have huw : u = σ (((w : U) : Kˣ) : K) * (((w : U) : Kˣ) : K)⁻¹ := by
    rw [hu, hτ, coe_normOneTwist, Units.val_mul, Units.val_inv_eq_inv_val]
    rfl
  have hu0 : u ≠ 0 := Units.ne_zero _
  have huN : h.norm u = 1 := by
    rw [h.norm_eq_pow]
    have := (mem_rootsOfUnity _ _).1 (τ w : U).2
    rw [hu, ← Units.val_pow_eq_pow_val, this, Units.val_one]
  have hσw0 : σ (((w : U) : Kˣ) : K) ≠ 0 := by rw [map_ne_zero]; exact hw0
  have hσσw0 : σ (σ (((w : U) : Kˣ) : K)) ≠ 0 := by rw [map_ne_zero, map_ne_zero]; exact hw0
  have hN : u * σ u * σ (σ u) = 1 := by
    rw [huw]
    simp only [map_mul, map_inv₀, hσσσ]
    field_simp
  refine ⟨u, hu0, huN, hN, fun hmem => hv3 ?_⟩
  have hσu0 : σ u ≠ 0 := by rw [map_ne_zero]; exact hu0
  have hσσu0 : σ (σ u) ≠ 0 := by rw [map_ne_zero, map_ne_zero]; exact hu0
  have hfix := (mem_fixedField_iff σ _).1 hmem
  rw [map_mul, map_inv₀] at hfix
  have h1 : σ u * σ u = u * σ (σ u) := by
    field_simp at hfix
    linear_combination hfix
  have h2 : (σ u) ^ 3 = 1 := by
    rw [← hN]
    linear_combination σ u * h1
  have h3 : u ^ 3 = 1 := by
    apply σ.injective
    rw [map_pow, h2, map_one]
  exact h3

theorem not_mem_of_mul_inv_not_mem {σ : K ≃+* K} {u : K} (hu0 : u ≠ 0)
    (hu : u * (σ u)⁻¹ ∉ fixedField σ) : u ∉ fixedField σ := by
  intro hmem
  apply hu
  rw [(mem_fixedField_iff σ u).1 hmem, mul_inv_cancel₀ hu0]
  exact (fixedField σ).one_mem

end CFSG.RankThree.PartTwo.Sec19.Item19Res6Proof
