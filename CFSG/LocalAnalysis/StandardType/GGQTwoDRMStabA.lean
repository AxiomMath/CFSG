module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDRMStabDefs
import CFSG.LocalAnalysis.StandardType.ZS.MonomialBasic
import CFSG.LocalAnalysis.StandardType.GGQTwoDRMStabAPerm

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {m : ℕ}

private noncomputable def p9uRMA_epsUnit (ε : DVec m) : Fin m → (ZMod 3)ˣ :=
  fun i => if ε i = 1 then 1 else -1

private lemma p9uRMA_epsUnit_val (ε : DVec m) (hε : ∀ i, ε i = 1 ∨ ε i = -1) (i : Fin m) :
    (p9uRMA_epsUnit ε i : ZMod 3) = ε i := by
  unfold p9uRMA_epsUnit
  by_cases h : ε i = 1
  · rw [if_pos h, h]; simp
  · have h1 : ε i = -1 := by
      rcases hε i with h' | h' <;> [exact absurd h' h; exact h']
    rw [if_neg h, h1]; simp

private lemma p9uRMA_epsUnit_inv_val (ε : DVec m)
    (hε : ∀ i, ε i = 1 ∨ ε i = -1) (i : Fin m) :
    ((p9uRMA_epsUnit ε i)⁻¹ : ZMod 3) = ε i := by
  unfold p9uRMA_epsUnit
  by_cases h : ε i = 1
  · rw [if_pos h, h]; simp
  · have h1 : ε i = -1 := by
      rcases hε i with h' | h' <;> [exact absurd h' h; exact h']
    rw [if_neg h, h1]; simp

private noncomputable def p9uRMA_D (ε : DVec m) : DVec m ≃ₗ[ZMod 3] DVec m :=
  ZS.diagMap 3 (dBasis m) (p9uRMA_epsUnit ε)

private lemma p9uRMA_D_basis (ε : DVec m) (hε : ∀ i, ε i = 1 ∨ ε i = -1) (i : Fin m) :
    p9uRMA_D ε (dBasis m i) = ε i • dBasis m i := by
  rw [p9uRMA_D, ZS.diagMap_apply_basis, p9uRMA_epsUnit_val ε hε]

private lemma p9uRMA_D_inv_basis (ε : DVec m) (hε : ∀ i, ε i = 1 ∨ ε i = -1) (i : Fin m) :
    (p9uRMA_D ε)⁻¹ (dBasis m i) = ε i • dBasis m i := by
  have hmul : p9uRMA_D ε * ZS.diagMap 3 (dBasis m) ((p9uRMA_epsUnit ε)⁻¹) = 1 := by
    rw [p9uRMA_D, ZS.diagMap_mul, mul_inv_cancel, ZS.diagMap_one]
  rw [inv_eq_of_mul_eq_one_right hmul, ZS.diagMap_apply_basis]
  simp only [Pi.inv_apply]
  rw [Units.val_inv_eq_inv_val, p9uRMA_epsUnit_inv_val ε hε]

private lemma p9uRMA_sum_basis (v : DVec m) : (∑ i : Fin m, v i • dBasis m i) = v := by
  conv_rhs => rw [← Module.Basis.sum_repr (dBasis m) v]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Pi.basisFun_repr]

private lemma p9uRMA_one_eq_sum : (1 : DVec m) = ∑ i, dBasis m i := by
  funext k
  rw [Finset.sum_apply, Finset.sum_eq_single k]
  · simp [dBasis, Pi.basisFun_apply]
  · intro i _ hi
    simp [dBasis, Pi.basisFun_apply, Pi.single_apply, hi]
  · intro hk; exact absurd (Finset.mem_univ k) hk

private lemma p9uRMA_D_one (ε : DVec m) (hε : ∀ i, ε i = 1 ∨ ε i = -1) :
    p9uRMA_D ε (1 : DVec m) = ε := by
  have h : p9uRMA_D ε (1 : DVec m) = ∑ i, ε i • dBasis m i := by
    rw [p9uRMA_one_eq_sum, map_sum]
    exact Finset.sum_congr rfl fun i _ => p9uRMA_D_basis ε hε i
  rw [h]; exact p9uRMA_sum_basis ε

private lemma p9uRMA_D_inv_eps (ε : DVec m) (hε : ∀ i, ε i = 1 ∨ ε i = -1) :
    (p9uRMA_D ε)⁻¹ ε = 1 := by
  have h : (p9uRMA_D ε)⁻¹ ε = (p9uRMA_D ε)⁻¹ (∑ i, ε i • dBasis m i) := by
    congr 1
    exact (p9uRMA_sum_basis ε).symm
  rw [h, map_sum]
  simp only [map_smul, p9uRMA_D_inv_basis ε hε, smul_smul]
  have h2 : ∀ i, ε i * ε i = 1 := by
    intro i; rcases hε i with h | h <;> rw [h] <;> decide
  trans ∑ i, dBasis m i
  · apply Finset.sum_congr rfl; intro i _
    rw [h2 i, one_smul]
  · exact p9uRMA_one_eq_sum.symm

private lemma p9uRMA_prod_eps_sq (ε : DVec m) (hε : ∀ i, ε i = 1 ∨ ε i = -1) :
    (∏ i, ε i) * (∏ i, ε i) = 1 := by
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_eq_one
  intro i _
  rcases hε i with h | h <;> rw [h] <;> decide

private lemma p9uRMA_mul_unit (ε : DVec m) (hε : ∀ i, ε i = 1 ∨ ε i = -1) (i j : Fin m) :
    ε i * ε j = 1 ∨ ε i * ε j = -1 := by
  rcases hε i with h | h <;> rcases hε j with h' | h' <;> rw [h, h'] <;> decide

private lemma p9uRMA_mem_dEvenStab_iff (ε : DVec m) (hε : ∀ i, ε i = 1 ∨ ε i = -1)
    (g : DVec m ≃ₗ[ZMod 3] DVec m) :
    g ∈ dEvenStab m ε ↔ ∃ σ : Equiv.Perm (Fin m),
      g = p9uRMA_D ε * dPerm m σ * (p9uRMA_D ε)⁻¹ := by
  constructor
  · intro hg
    have hLmem : (p9uRMA_D ε)⁻¹ * g * p9uRMA_D ε ∈ dEven m := by
      obtain ⟨σ, c, hc, hprod, hact⟩ := hg.1
      refine ⟨σ, fun i => ε i * c i * ε (σ i), ?_, ?_, ?_⟩
      · intro i
        show ε i * c i * ε (σ i) = 1 ∨ ε i * c i * ε (σ i) = -1
        rcases hε i with h | h <;> rcases hc i with h' | h' <;>
          rcases hε (σ i) with h'' | h'' <;> rw [h, h', h''] <;> decide
      · show (∏ i, ε i * c i * ε (σ i)) = 1
        rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, hprod, mul_one,
          Equiv.prod_comp σ (fun i => ε i), p9uRMA_prod_eps_sq ε hε]
      · intro i
        show ((p9uRMA_D ε)⁻¹ * g * p9uRMA_D ε) (dBasis m i) =
          (ε i * c i * ε (σ i)) • dBasis m (σ i)
        rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, p9uRMA_D_basis ε hε, map_smul,
          hact i]
        simp only [map_smul, p9uRMA_D_inv_basis ε hε, smul_smul]
    have hL1 : ((p9uRMA_D ε)⁻¹ * g * p9uRMA_D ε) (1 : DVec m) = 1 := by
      rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, p9uRMA_D_one ε hε, hg.2,
        p9uRMA_D_inv_eps ε hε]
    obtain ⟨σ, hσ⟩ := qtwoDRMStab_eq_dPerm_of_fix hLmem hL1
    exact ⟨σ, by rw [← hσ]; group⟩
  · rintro ⟨σ, rfl⟩
    refine ⟨?_, ?_⟩
    · refine ⟨σ, fun i => ε i * ε (σ i), fun i => p9uRMA_mul_unit ε hε i (σ i), ?_, ?_⟩
      · show (∏ i, ε i * ε (σ i)) = 1
        rw [Finset.prod_mul_distrib, Equiv.prod_comp σ (fun i => ε i),
          p9uRMA_prod_eps_sq ε hε]
      · intro i
        show (p9uRMA_D ε * dPerm m σ * (p9uRMA_D ε)⁻¹) (dBasis m i) =
          (ε i * ε (σ i)) • dBasis m (σ i)
        rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, p9uRMA_D_inv_basis ε hε, map_smul,
          dPerm_apply]
        simp only [map_smul, p9uRMA_D_basis ε hε, smul_smul]
    · show (p9uRMA_D ε * dPerm m σ * (p9uRMA_D ε)⁻¹) ε = ε
      rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, p9uRMA_D_inv_eps ε hε]
      change p9uRMA_D ε (dPerm m σ (fun _ => 1)) = ε
      rw [qtwoDRMStab_dPerm_const σ 1]
      exact p9uRMA_D_one ε hε

private lemma p9uRMA_inv_apply (a : DVec m ≃ₗ[ZMod 3] DVec m) (v : DVec m) :
    a⁻¹ v = a.symm v := rfl

private lemma p9uRMA_isRefl_conj {a r : DVec m ≃ₗ[ZMod 3] DVec m} (hr : dIsRefl r) :
    dIsRefl (a * r * a⁻¹) := by
  obtain ⟨c, f, hfc, hact⟩ := hr
  refine ⟨a c, f.comp a.symm.toLinearMap, ?_, fun v => ?_⟩
  · simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, LinearEquiv.symm_apply_apply]
    exact hfc
  · rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, p9uRMA_inv_apply, hact, map_sub, map_smul,
      LinearEquiv.apply_symm_apply]
    rfl

private lemma p9uRMA_three_m_le (hm : 5 ≤ m) : 3 * m ≤ 2 ^ (m - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 5 := ⟨m - 5, by omega⟩
  clear hm
  rw [show k + 5 - 1 = k + 4 by omega]
  induction k with
  | zero => norm_num
  | succ k ih =>
      calc 3 * (k + 1 + 5) = 3 * (k + 6) := by ring
        _ ≤ 2 * (3 * (k + 5)) := by omega
        _ ≤ 2 * 2 ^ (k + 4) := Nat.mul_le_mul_left 2 ih
        _ = 2 ^ (k + 1 + 4) := by rw [show k + 1 + 4 = k + 4 + 1 by omega, pow_succ]; ring

private lemma p9uRMA_three_mul_factorial_le (hm : 5 ≤ m) :
    3 * m.factorial ≤ 2 ^ (m - 1) * (m - 1).factorial := by
  have hfac : m.factorial = m * (m - 1).factorial := by
    conv_lhs => rw [show m = (m - 1) + 1 by omega]
    rw [Nat.factorial_succ, Nat.sub_add_cancel (by omega : 1 ≤ m)]
  rw [hfac]
  calc 3 * (m * (m - 1).factorial) = (3 * m) * (m - 1).factorial := by ring
    _ ≤ 2 ^ (m - 1) * (m - 1).factorial := Nat.mul_le_mul_right _ (p9uRMA_three_m_le hm)

private lemma p9uRMA_conj_mem_iff (ε : DVec m) (hε : ∀ i, ε i = 1 ∨ ε i = -1)
    (h : DVec m ≃ₗ[ZMod 3] DVec m) :
    p9uRMA_D ε * h * (p9uRMA_D ε)⁻¹ ∈ dEvenStab m ε ↔ h ∈ dEvenStab m (1 : DVec m) := by
  rw [p9uRMA_mem_dEvenStab_iff ε hε, qtwoDRMStab_mem_dEvenStab_one_iff]
  constructor
  · rintro ⟨σ, hσ⟩
    refine ⟨σ, ?_⟩
    have hh : h = dPerm m σ := by
      have h1 : p9uRMA_D ε * h = p9uRMA_D ε * dPerm m σ := by
        have := congrArg (fun g => g * p9uRMA_D ε) hσ
        simpa [mul_assoc] using this
      exact mul_left_cancel h1
    exact hh.symm
  · rintro ⟨σ, hσ⟩
    have hσ' : dPerm m σ = h := hσ
    exact ⟨σ, by rw [← hσ']⟩

private lemma p9uRMA_normalizer_transfer (ε : DVec m) (hε : ∀ i, ε i = 1 ∨ ε i = -1)
    {a : DVec m ≃ₗ[ZMod 3] DVec m}
    (hnorm : ∀ w ∈ dEvenStab m ε, a * w * a⁻¹ ∈ dEvenStab m ε) :
    ∀ σ : Equiv.Perm (Fin m), ∃ τ : Equiv.Perm (Fin m),
      dPerm m τ = ((p9uRMA_D ε)⁻¹ * a * p9uRMA_D ε) * dPerm m σ *
        ((p9uRMA_D ε)⁻¹ * a * p9uRMA_D ε)⁻¹ := by
  intro σ
  have hD : p9uRMA_D ε * dPerm m σ * (p9uRMA_D ε)⁻¹ ∈ dEvenStab m ε :=
    (p9uRMA_conj_mem_iff ε hε (dPerm m σ)).mpr
      ((qtwoDRMStab_mem_dEvenStab_one_iff _).mpr ⟨σ, rfl⟩)
  have ha : a * (p9uRMA_D ε * dPerm m σ * (p9uRMA_D ε)⁻¹) * a⁻¹ ∈ dEvenStab m ε :=
    hnorm _ hD
  have heq : ((p9uRMA_D ε)⁻¹ * a * p9uRMA_D ε) * dPerm m σ *
        ((p9uRMA_D ε)⁻¹ * a * p9uRMA_D ε)⁻¹ =
      (p9uRMA_D ε)⁻¹ * (a * (p9uRMA_D ε * dPerm m σ * (p9uRMA_D ε)⁻¹) * a⁻¹) *
        p9uRMA_D ε := by group
  rw [heq]
  exact (qtwoDRMStab_mem_dEvenStab_one_iff _).mp ((p9uRMA_conj_mem_iff ε hε _).mp (by
    show p9uRMA_D ε * ((p9uRMA_D ε)⁻¹ *
        (a * (p9uRMA_D ε * dPerm m σ * (p9uRMA_D ε)⁻¹) * a⁻¹) *
        p9uRMA_D ε) * (p9uRMA_D ε)⁻¹ ∈ dEvenStab m ε
    simpa [mul_assoc] using ha))

private lemma p9uRMA_exists_data (hm2 : 2 ≤ m) (ε : DVec m)
    (hε : ∀ i, ε i = 1 ∨ ε i = -1)
    (a : {a : DVec m ≃ₗ[ZMod 3] DVec m //
      a ε = ε ∧ ∀ w ∈ dEvenStab m ε, a * w * a⁻¹ ∈ dEvenStab m ε}) :
    ∃ d : Equiv.Perm (Fin m) × {pq : ZMod 3 × ZMod 3 // pq.1 + m * pq.2 = 1},
      ∀ v : DVec m,
        ((p9uRMA_D ε)⁻¹ * a.1 * p9uRMA_D ε) v =
          dPerm m d.1 (d.2.1.1 • v + d.2.1.2 • (∑ i, v i) • (1 : DVec m)) := by
  have hb1 : ((p9uRMA_D ε)⁻¹ * a.1 * p9uRMA_D ε) (1 : DVec m) = 1 := by
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, p9uRMA_D_one ε hε, a.2.1,
      p9uRMA_D_inv_eps ε hε]
  obtain ⟨β, p, q, hform⟩ :=
    qtwoDRMStab_normalizer_dPerm hm2 (p9uRMA_normalizer_transfer ε hε a.2.2)
  have hpq : p + m * q = 1 := by
    have h := hform (1 : DVec m)
    rw [hb1] at h
    have hsum : (∑ i : Fin m, (1 : ZMod 3)) = (m : ZMod 3) := by
      simp [Finset.sum_const, nsmul_eq_mul]
    have hconst : p • (1 : DVec m) + q • (∑ i, (1 : DVec m) i) • (1 : DVec m) =
        (fun _ => p + q * (m : ZMod 3)) := by
      funext k
      simp only [Pi.add_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul]
      rw [hsum]
      ring
    rw [hconst, qtwoDRMStab_dPerm_const] at h
    have h0 : (1 : ZMod 3) = p + q * (m : ZMod 3) := by
      simpa using congrFun h (⟨0, by omega⟩ : Fin m)
    have hpq' : p + q * (m : ZMod 3) = 1 := h0.symm
    rwa [mul_comm q (m : ZMod 3)] at hpq'
  exact ⟨⟨β, (p, q), hpq⟩, hform⟩

private noncomputable def p9uRMA_data (hm2 : 2 ≤ m) (ε : DVec m)
    (hε : ∀ i, ε i = 1 ∨ ε i = -1)
    (a : {a : DVec m ≃ₗ[ZMod 3] DVec m //
      a ε = ε ∧ ∀ w ∈ dEvenStab m ε, a * w * a⁻¹ ∈ dEvenStab m ε}) :
    Equiv.Perm (Fin m) × {pq : ZMod 3 × ZMod 3 // pq.1 + m * pq.2 = 1} :=
  Classical.choose (p9uRMA_exists_data hm2 ε hε a)

private lemma p9uRMA_data_spec (hm2 : 2 ≤ m) (ε : DVec m)
    (hε : ∀ i, ε i = 1 ∨ ε i = -1)
    (a : {a : DVec m ≃ₗ[ZMod 3] DVec m //
      a ε = ε ∧ ∀ w ∈ dEvenStab m ε, a * w * a⁻¹ ∈ dEvenStab m ε}) (v : DVec m) :
    ((p9uRMA_D ε)⁻¹ * a.1 * p9uRMA_D ε) v =
      dPerm m (p9uRMA_data hm2 ε hε a).1
        ((p9uRMA_data hm2 ε hε a).2.1.1 • v +
          (p9uRMA_data hm2 ε hε a).2.1.2 • (∑ i, v i) • (1 : DVec m)) :=
  Classical.choose_spec (p9uRMA_exists_data hm2 ε hε a) v

private lemma p9uRMA_data_injective (hm2 : 2 ≤ m) (ε : DVec m)
    (hε : ∀ i, ε i = 1 ∨ ε i = -1) :
    Function.Injective (p9uRMA_data hm2 ε hε) := by
  intro a a' h
  apply Subtype.ext
  have h1 := p9uRMA_data_spec hm2 ε hε a
  have h2 := p9uRMA_data_spec hm2 ε hε a'
  rw [h] at h1
  have heq : ((p9uRMA_D ε)⁻¹ * a.1 * p9uRMA_D ε) =
      ((p9uRMA_D ε)⁻¹ * a'.1 * p9uRMA_D ε) := by
    refine LinearEquiv.ext fun v => ?_
    rw [h1 v, h2 v]
  have hb : p9uRMA_D ε * ((p9uRMA_D ε)⁻¹ * a.1 * p9uRMA_D ε) * (p9uRMA_D ε)⁻¹ =
      p9uRMA_D ε * ((p9uRMA_D ε)⁻¹ * a'.1 * p9uRMA_D ε) * (p9uRMA_D ε)⁻¹ := by rw [heq]
  have h3 : a.1 = a'.1 := by
    have h1 : p9uRMA_D ε * ((p9uRMA_D ε)⁻¹ * a.1 * p9uRMA_D ε) =
        p9uRMA_D ε * ((p9uRMA_D ε)⁻¹ * a'.1 * p9uRMA_D ε) := mul_right_cancel hb
    have h2 : (p9uRMA_D ε)⁻¹ * a.1 * p9uRMA_D ε =
        (p9uRMA_D ε)⁻¹ * a'.1 * p9uRMA_D ε := mul_left_cancel h1
    have h4 : (p9uRMA_D ε)⁻¹ * a.1 = (p9uRMA_D ε)⁻¹ * a'.1 := mul_right_cancel h2
    exact mul_left_cancel h4
  exact h3

private lemma p9uRMA_sum_basis_single (m : ℕ) (i : Fin m) :
    (∑ j : Fin m, (dBasis m i : DVec m) j) = 1 := by
  rw [Finset.sum_eq_single i]
  · simp [dBasis, Pi.basisFun_apply]
  · intro j _ hj; simp [dBasis, Pi.basisFun_apply, Pi.single_eq_of_ne hj]
  · intro hi; exact absurd (Finset.mem_univ i) hi

private lemma p9uRMA_exists_notMem {m : ℕ} (hm : 5 ≤ m) (s : Finset (Fin m))
    (hs : s.card ≤ 4) : ∃ x : Fin m, x ∉ s := by
  obtain ⟨x, _, hx⟩ := Finset.exists_mem_notMem_of_card_lt_card (s := s) (t := Finset.univ)
    (by rw [Finset.card_univ, Fintype.card_fin]; omega)
  exact ⟨x, hx⟩

private lemma p9uRMA_vi (m : ℕ) (β : Equiv.Perm (Fin m)) (p q : ZMod 3) {i k : Fin m}
    (hki : k ≠ i) (hkb : k ≠ β i) :
    (dBasis m i - p • dBasis m (β i) - q • (1 : DVec m) : DVec m) k = -q := by
  simp only [Pi.sub_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, dBasis, Pi.basisFun_apply,
    Pi.single_apply, if_neg hki, if_neg hkb]
  ring

theorem qtwoDRMStab_A_reflection {m : ℕ} (hm : 5 ≤ m) {ε : DVec m}
    (hε : ∀ i, ε i = 1 ∨ ε i = -1) :
    ∀ a : DVec m ≃ₗ[ZMod 3] DVec m, a ε = ε →
      (∀ w ∈ dEvenStab m ε, a * w * a⁻¹ ∈ dEvenStab m ε) → dIsRefl a → a ∈ dEvenStab m ε := by
  intro a haε hnorm hrefl
  have hm2 : 2 ≤ m := by omega
  obtain ⟨d, hd⟩ := p9uRMA_exists_data hm2 ε hε ⟨a, haε, hnorm⟩
  set b : DVec m ≃ₗ[ZMod 3] DVec m := (p9uRMA_D ε)⁻¹ * a * p9uRMA_D ε with hb
  obtain ⟨β, p, q, hpq, hform⟩ : ∃ (β : Equiv.Perm (Fin m)) (p q : ZMod 3),
      p + m * q = 1 ∧ ∀ v, b v = dPerm m β (p • v + q • (∑ i, v i) • (1 : DVec m)) :=
    ⟨d.1, d.2.1.1, d.2.1.2, d.2.2, hd⟩
  have hrefl_b : dIsRefl b := by
    rw [hb]
    simpa using p9uRMA_isRefl_conj (a := (p9uRMA_D ε)⁻¹) hrefl
  have hb_eq_a : p9uRMA_D ε * b * (p9uRMA_D ε)⁻¹ = a := by rw [hb]; group
  by_cases hq0 : q = 0
  · have hp1 : p = 1 := by
      have h := hpq
      rw [hq0, mul_zero, add_zero] at h
      exact h
    have hb_eq : b = dPerm m β := by
      refine LinearEquiv.ext fun v => ?_
      rw [hform v, hp1, hq0, zero_smul, add_zero, one_smul]
    rw [← hb_eq_a, p9uRMA_conj_mem_iff ε hε b, qtwoDRMStab_mem_dEvenStab_one_iff]
    exact ⟨β, hb_eq.symm⟩
  · exfalso
    obtain ⟨c, f, hfc, hact⟩ := hrefl_b
    have hc0 : c ≠ 0 := by
      rintro rfl
      exact (by decide : (0 : ZMod 3) ≠ 2) (by simpa using hfc)
    have hsum1 : (∑ i : Fin m, (1 : DVec m) i) = (m : ZMod 3) := by
      simp [Finset.sum_const, nsmul_eq_mul]
    have hb1 : b (1 : DVec m) = 1 := by
      rw [hform (1 : DVec m), hsum1, smul_smul, ← add_smul,
        show p + q * (m : ZMod 3) = 1 by rw [mul_comm q]; exact hpq, one_smul]
      exact qtwoDRMStab_dPerm_const β 1
    have hb_e : ∀ i : Fin m, b (dBasis m i) = p • dBasis m (β i) + q • (1 : DVec m) := by
      intro i
      rw [hform (dBasis m i), p9uRMA_sum_basis_single m i, one_smul, map_add, map_smul,
        map_smul, dPerm_apply,
        show (dPerm m β) (1 : DVec m) = 1 from qtwoDRMStab_dPerm_const β 1]
    have hci : ∀ i : Fin m, f (dBasis m i) • c =
        dBasis m i - p • dBasis m (β i) - q • (1 : DVec m) := by
      intro i
      have h := hact (dBasis m i)
      rw [hb_e i] at h
      rw [sub_sub, h]; abel
    have hex : ∀ i : Fin m, ∃ j k : Fin m,
        j ∉ ({i, β⁻¹ i} : Finset (Fin m)) ∧
        k ∉ ({i, β i, j, β j} : Finset (Fin m)) := by
      intro i
      obtain ⟨j, hj⟩ := p9uRMA_exists_notMem hm ({i, β⁻¹ i} : Finset (Fin m))
        (le_trans Finset.card_le_two (by norm_num : 2 ≤ 4))
      obtain ⟨k, hk⟩ := p9uRMA_exists_notMem hm ({i, β i, j, β j} : Finset (Fin m))
        (Finset.card_le_four (a := i) (b := β i) (c := j) (d := β j))
      exact ⟨j, k, hj, hk⟩
    have hkey : ∀ i : Fin m, β i = i ∧ p = 1 := by
      intro i
      obtain ⟨j, k, hj, hk⟩ := hex i
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hj hk
      obtain ⟨hji, hjb'⟩ := hj
      obtain ⟨hki, hkb, hkj, hkbb⟩ := hk
      have hjb : β j ≠ i := fun h => hjb' (by rw [← h]; simp)
      have hμ' : f (dBasis m j) * (-q) = f (dBasis m i) * (-q) := by
        have hrel : f (dBasis m j) • (f (dBasis m i) • c) =
            f (dBasis m i) • (f (dBasis m j) • c) := by rw [smul_smul, smul_smul, mul_comm]
        rw [hci i, hci j] at hrel
        have h := congrFun hrel k
        simp only [Pi.smul_apply, smul_eq_mul] at h
        rwa [p9uRMA_vi m β p q hki hkb, p9uRMA_vi m β p q hkj hkbb] at h
      have hμ : f (dBasis m i) = f (dBasis m j) :=
        (mul_right_cancel₀ (neg_ne_zero.mpr hq0) hμ').symm
      have hvi_eq : (dBasis m i - p • dBasis m (β i) - q • (1 : DVec m) : DVec m) =
          (dBasis m j - p • dBasis m (β j) - q • (1 : DVec m) : DVec m) := by
        rw [← hci i, ← hci j, hμ]
      have hii := congrFun hvi_eq i
      simp only [Pi.sub_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one, mul_zero,
        sub_zero, zero_sub, dBasis, Pi.basisFun_apply, Pi.single_apply, if_neg (Ne.symm hji),
        if_neg (Ne.symm hjb), ↓reduceIte] at hii
      by_cases hfix : i = β i
      · exact ⟨hfix.symm, by rw [if_pos hfix] at hii; linear_combination -hii⟩
      · exfalso
        exact absurd (by rw [if_neg hfix] at hii; linear_combination hii) one_ne_zero
    have hβ1 : β = 1 := Equiv.ext fun i => (hkey i).1
    have hp1 : p = 1 := (hkey ⟨0, by omega⟩).2
    have hform1 : ∀ v : DVec m, b v = v + q • (∑ i, v i) • (1 : DVec m) := by
      intro v
      rw [hform v, hβ1, hp1, one_smul, dPerm_one]
      rfl
    have hf1 : f (1 : DVec m) = 0 := by
      have h := hact (1 : DVec m)
      rw [hb1] at h
      exact (smul_eq_zero.mp (sub_eq_self.mp h.symm)).resolve_right hc0
    let i0 : Fin m := ⟨0, by omega⟩
    have hrel_e : f (dBasis m i0) • c = (-q) • (1 : DVec m) := by
      have h := hact (dBasis m i0)
      rw [hform1 (dBasis m i0), p9uRMA_sum_basis_single m i0, one_smul] at h
      calc f (dBasis m i0) • c
          = dBasis m i0 - (dBasis m i0 + q • (1 : DVec m)) := by rw [h]; abel
        _ = (-q) • (1 : DVec m) := by rw [neg_smul]; abel
    have hfe_ne : f (dBasis m i0) ≠ 0 := by
      intro h0
      have h := congrFun hrel_e i0
      simp only [Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one] at h
      rw [h0, zero_mul] at h
      exact hq0 (neg_eq_zero.mp h.symm)
    have happ := congrArg f hrel_e
    rw [map_smul, map_smul, hf1, smul_zero] at happ
    exact (by decide : (2 : ZMod 3) ≠ 0)
      (hfc.symm.trans ((smul_eq_zero.mp happ).resolve_left hfe_ne))

theorem qtwoDRMStab_A {m : ℕ} (hm : 5 ≤ m) {ε : DVec m}
    (hε : ∀ i, ε i = 1 ∨ ε i = -1) :
    Nat.card {a : DVec m ≃ₗ[ZMod 3] DVec m //
        a ε = ε ∧ ∀ w ∈ dEvenStab m ε, a * w * a⁻¹ ∈ dEvenStab m ε} ≤
      2 ^ (m - 1) * (m - 1).factorial ∧
    ∀ a : DVec m ≃ₗ[ZMod 3] DVec m, a ε = ε →
      (∀ w ∈ dEvenStab m ε, a * w * a⁻¹ ∈ dEvenStab m ε) → dIsRefl a → a ∈ dEvenStab m ε := by
  have hm2 : 2 ≤ m := by omega
  have hcard : Nat.card {a : DVec m ≃ₗ[ZMod 3] DVec m //
        a ε = ε ∧ ∀ w ∈ dEvenStab m ε, a * w * a⁻¹ ∈ dEvenStab m ε} ≤
      2 ^ (m - 1) * (m - 1).factorial := by
    have hcard' := Nat.card_le_card_of_injective
      (p9uRMA_data hm2 ε hε) (p9uRMA_data_injective hm2 ε hε)
    rw [Nat.card_prod] at hcard'
    have hperm : Nat.card (Equiv.Perm (Fin m)) = m.factorial := by
      rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    have hfib : Nat.card {pq : ZMod 3 × ZMod 3 // pq.1 + m * pq.2 = 1} ≤ 3 := by
      have hinj : Function.Injective
          (fun x : {pq : ZMod 3 × ZMod 3 // pq.1 + m * pq.2 = 1} => x.1.2) := by
        intro x y hxy
        change x.1.2 = y.1.2 at hxy
        apply Subtype.ext
        have h1 : x.1.1 = y.1.1 := by
          have hthis : x.1.1 + m * x.1.2 = y.1.1 + m * y.1.2 := by rw [x.2, y.2]
          rw [hxy] at hthis
          exact add_right_cancel hthis
        exact Prod.ext h1 hxy
      have := Nat.card_le_card_of_injective
        (fun x : {pq : ZMod 3 × ZMod 3 // pq.1 + m * pq.2 = 1} => x.1.2) hinj
      simpa [Nat.card_eq_fintype_card, ZMod.card] using this
    calc Nat.card {a : DVec m ≃ₗ[ZMod 3] DVec m //
            a ε = ε ∧ ∀ w ∈ dEvenStab m ε, a * w * a⁻¹ ∈ dEvenStab m ε}
        ≤ Nat.card (Equiv.Perm (Fin m)) *
            Nat.card {pq : ZMod 3 × ZMod 3 // pq.1 + m * pq.2 = 1} := hcard'
      _ ≤ m.factorial * 3 := by rw [hperm]; exact Nat.mul_le_mul_left _ hfib
      _ = 3 * m.factorial := Nat.mul_comm _ _
      _ ≤ 2 ^ (m - 1) * (m - 1).factorial := p9uRMA_three_mul_factorial_le hm
  exact ⟨hcard, fun a ha hn hr => qtwoDRMStab_A_reflection hm hε a ha hn hr⟩

private lemma p9uRMA_D_inv_apply (ε : DVec m) (hε : ∀ i, ε i = 1 ∨ ε i = -1) (v : DVec m)
    (i : Fin m) : (p9uRMA_D ε)⁻¹ v i = ε i * v i := by
  conv_lhs => rw [← p9uRMA_sum_basis v]
  rw [map_sum, Finset.sum_apply, Finset.sum_eq_single i]
  · rw [map_smul, p9uRMA_D_inv_basis ε hε, smul_smul, Pi.smul_apply, dBasis, Pi.basisFun_apply,
      Pi.single_eq_same, smul_eq_mul, mul_one, mul_comm]
  · intro k _ hki
    rw [map_smul, p9uRMA_D_inv_basis ε hε, smul_smul, Pi.smul_apply, dBasis, Pi.basisFun_apply,
      Pi.single_eq_of_ne (Ne.symm hki), smul_zero]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

theorem qtwoDRMStab_six_form {ε : DVec 6} (hε : ∀ i, ε i = 1 ∨ ε i = -1)
    {a : DVec 6 ≃ₗ[ZMod 3] DVec 6} (haε : a ε = ε)
    (hnorm : ∀ w ∈ dEvenStab 6 ε, a * w * a⁻¹ ∈ dEvenStab 6 ε) :
    ∃ w ∈ dEvenStab 6 ε, ∃ q : ZMod 3, ∀ v, a v = w (v + (q * (ε ⬝ᵥ v)) • ε) := by
  obtain ⟨⟨β, ⟨⟨p, q⟩, hpq⟩⟩, hd⟩ := p9uRMA_exists_data (m := 6) (by norm_num) ε hε ⟨a, haε, hnorm⟩
  have hp : p = 1 := by
    have h6 : ((6 : ℕ) : ZMod 3) = 0 := by decide
    have hpq' : p + ((6 : ℕ) : ZMod 3) * q = 1 := hpq
    rwa [h6, zero_mul, add_zero] at hpq'
  subst hp
  set D := p9uRMA_D ε with hD
  refine ⟨D * dPerm 6 β * D⁻¹, (p9uRMA_mem_dEvenStab_iff ε hε _).mpr ⟨β, rfl⟩, q, fun v => ?_⟩
  have ha : a v = D ((D⁻¹ * a * D) (D⁻¹ v)) := by
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, ← LinearEquiv.mul_apply D D⁻¹,
      mul_inv_cancel, ← LinearEquiv.mul_apply D D⁻¹, mul_inv_cancel]
    rfl
  have hsum : (∑ i, D⁻¹ v i) = ε ⬝ᵥ v := by
    unfold dotProduct
    exact Finset.sum_congr rfl fun i _ => p9uRMA_D_inv_apply ε hε v i
  have hinv : D⁻¹ (v + (q * (ε ⬝ᵥ v)) • ε) = D⁻¹ v + (q * (ε ⬝ᵥ v)) • (1 : DVec 6) := by
    rw [map_add, map_smul, hD, p9uRMA_D_inv_eps ε hε]
  rw [ha, hd, one_smul, hsum, LinearEquiv.mul_apply, LinearEquiv.mul_apply, hinv, smul_smul]

end CFSG.StandardType.QTwo

end
