module

public import Mathlib.LinearAlgebra.Charpoly.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Minpoly
public import Mathlib.FieldTheory.Finite.Basic

public section

open Module Polynomial

namespace CFSG.StandardType

namespace OrthTorus

variable {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ} [Fact p.Prime]
  {D : Type} [AddCommGroup D] [Module K D] [FiniteDimensional K D]

theorem pow_pow_zmod_inv_eq_self {M : Type*} [Monoid M] {x : M}
    (hxp : x ^ p = 1) (hxne : x ≠ 1) {e : ZMod p} (he : e ≠ 0) :
    (x ^ e.val) ^ (e⁻¹).val = x := by
  have hp_pos : 0 < p := (Fact.out : p.Prime).pos
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  have hx : IsOfFinOrder x := isOfFinOrder_iff_pow_eq_one.mpr ⟨p, hp_pos, hxp⟩
  have hord : orderOf x = p := orderOf_eq_prime hxp hxne
  have hmod : e.val * (e⁻¹).val ≡ 1 [MOD p] := by
    have h := congrArg ZMod.val (mul_inv_cancel₀ he)
    rw [ZMod.val_mul, ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt hp1] at h
    simpa [Nat.ModEq, Nat.mod_eq_of_lt hp1] using h
  rw [← pow_mul]
  conv_rhs => rw [← pow_one x]
  rw [hx.pow_eq_pow_iff_modEq, hord]
  exact hmod

omit [Finite K] [CharP K 2] [FiniteDimensional K D] in
theorem inv_apply_eq_inv_smul_of_apply_eq_smul {f : D ≃ₗ[K] D} {v : D} {a : K}
    (ha : a ≠ 0) (h : f v = a • v) : f⁻¹ v = a⁻¹ • v := by
  have h' : f (a⁻¹ • v) = v := by
    rw [map_smul, h, smul_smul, inv_mul_cancel₀ ha, one_smul]
  have h'' := congrArg (fun x => f⁻¹ x) h'
  simpa using h''.symm

omit [Finite K] [CharP K 2] [FiniteDimensional K D] in
theorem conj_inv_apply_eq_smul_of_apply_eq_smul {c T : D ≃ₗ[K] D} {v : D} {a : K}
    (hT : T * c * T⁻¹ = c⁻¹) (h : c v = a • v) (hv : v ≠ 0) :
    c⁻¹ (T v) = a • T v ∧ T v ≠ 0 := by
  constructor
  · calc
      c⁻¹ (T v) = (T * c * T⁻¹) (T v) := by rw [hT]
      _ = T (c (T⁻¹ (T v))) := rfl
      _ = T (c v) := by simp
      _ = T (a • v) := by rw [h]
      _ = a • T v := by rw [map_smul]
  · intro hzero
    exact hv (T.injective (by simpa using hzero))

omit [Finite K] [CharP K 2] in
theorem ne_inv_self_of_ne_one {a : K} (h2 : (2 : K) = 0) (ha0 : a ≠ 0) (ha1 : a ≠ 1) :
    a ≠ a⁻¹ := by
  intro h
  have hsq : a * a = 1 := by
    nth_rewrite 1 [h]
    exact inv_mul_cancel₀ ha0
  have hzero : (a - 1) ^ 2 = 0 := by
    calc
      (a - 1) ^ 2 = a ^ 2 - 2 * a + 1 := by ring
      _ = 1 - 0 + 1 := by rw [sq, hsq, h2, zero_mul]
      _ = (2 : K) := by norm_num
      _ = 0 := h2
  exact ha1 (sub_eq_zero.mp (sq_eq_zero_iff.mp hzero))

omit [Finite K] in
theorem eq_inv_of_eigenvectors_of_conj_inv {c : D ≃ₗ[K] D} {β β' : K} {d d' : D}
    (hdim : finrank K D = 2)
    (hβ0 : β ≠ 0) (hβ'0 : β' ≠ 0)
    (hd : d ≠ 0) (hd' : d' ≠ 0)
    (hc_d : c d = β • d) (hc_d' : c d' = β' • d')
    (hβ_ne : β ≠ β') (hβ'_ne_one : β' ≠ 1)
    (hT : ∃ T : D ≃ₗ[K] D, T * c * T⁻¹ = c⁻¹) : β' = β⁻¹ := by
  have hc_inv_d := inv_apply_eq_inv_smul_of_apply_eq_smul hβ0 hc_d
  have hc_inv_d' := inv_apply_eq_inv_smul_of_apply_eq_smul hβ'0 hc_d'
  obtain ⟨T, hT_eq⟩ := hT
  obtain ⟨hTd', hTd'_ne⟩ := conj_inv_apply_eq_smul_of_apply_eq_smul hT_eq hc_d' hd'
  have hβ'_ne_self_inv := ne_inv_self_of_ne_one (CharP.cast_eq_zero K 2) hβ'0 hβ'_ne_one
  by_contra hcontra
  have hβ_inv_ne_β'_inv : β⁻¹ ≠ (β')⁻¹ := by
    intro h
    exact hβ_ne (inv_injective h)
  have hβ_inv_ne_β' : β⁻¹ ≠ β' := fun h => hcontra h.symm
  let μ : Fin 3 → K := ![β⁻¹, (β')⁻¹, β']
  let v : Fin 3 → D := ![d, d', T d']
  have hμ : Function.Injective μ := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [μ]
  have h_eigen : ∀ i, Module.End.HasEigenvector
      ((c⁻¹ : D ≃ₗ[K] D) : D →ₗ[K] D) (μ i) (v i) := by
    intro i
    fin_cases i
    · exact Module.End.hasEigenvector_iff.mpr
        ⟨Module.End.mem_eigenspace_iff.mpr hc_inv_d, hd⟩
    · exact Module.End.hasEigenvector_iff.mpr
        ⟨Module.End.mem_eigenspace_iff.mpr hc_inv_d', hd'⟩
    · exact Module.End.hasEigenvector_iff.mpr
        ⟨Module.End.mem_eigenspace_iff.mpr hTd', hTd'_ne⟩
  have hli := Module.End.eigenvectors_linearIndependent'
    ((c⁻¹ : D ≃ₗ[K] D) : D →ₗ[K] D) μ hμ v h_eigen
  have hcard := hli.fintype_card_le_finrank
  simp at hcard
  omega

omit [Finite K] [CharP K 2] [FiniteDimensional K D] in
theorem linear_aeval_eq_smul_of_eq {f : D →ₗ[K] D} {h : K[X]} {a b : K}
    (ha : a ≠ 0) (h_eq : C a * X + C b = h) {d : D}
    (hd0 : aeval f h d = 0) : f d = (-(b * a⁻¹)) • d := by
  have heval : a • f d + b • d = 0 := by
    rw [← h_eq] at hd0
    simpa using hd0
  have hx : a • f d = -(b • d) := add_eq_zero_iff_eq_neg.mp heval
  have h' := congrArg (fun y : D => a⁻¹ • y) hx
  simp only [smul_neg, smul_smul, inv_mul_cancel₀ ha, one_smul] at h'
  rw [h', neg_smul]
  congr 1
  rw [mul_comm]

omit [Finite K] [CharP K 2] [FiniteDimensional K D] in
theorem linear_eigenvalue_pow (c : D ≃ₗ[K] D) (hcp : c ^ p = 1) (hcne : c ≠ 1)
    (hfix : ∀ u, c u = u → u = 0) {e : ZMod p} (he : e ≠ 0)
    {d : D} (hd : d ≠ 0) {lam : K}
    (hce : ((c ^ e.val : D ≃ₗ[K] D) : D →ₗ[K] D) d = lam • d) :
    ∃ β : K, c d = β • d ∧ β ^ p = 1 ∧ β ≠ 0 ∧ β ≠ 1 ∧ β ^ e.val = lam := by
  have hce_pow_p : ((c ^ e.val : D ≃ₗ[K] D) ^ p) = 1 := by
    rw [← pow_mul, Nat.mul_comm e.val p, pow_mul, hcp, one_pow]
  have h_eig : Module.End.HasEigenvector
      ((c ^ e.val : D ≃ₗ[K] D) : D →ₗ[K] D) lam d :=
    Module.End.hasEigenvector_iff.mpr ⟨Module.End.mem_eigenspace_iff.mpr hce, hd⟩
  have hcoe_p : (↑((c ^ e.val : D ≃ₗ[K] D) ^ p) : D →ₗ[K] D) =
      (↑(c ^ e.val : D ≃ₗ[K] D) : D →ₗ[K] D) ^ p :=
    map_pow (LinearEquiv.automorphismGroup.toLinearMapMonoidHom) (c ^ e.val) p
  have hlam_p : lam ^ p = 1 := by
    have hk := h_eig.pow_apply p
    rw [← hcoe_p, hce_pow_p] at hk
    have hk' : d = lam ^ p • d := by simpa using hk
    have hsub : (lam ^ p - 1) • d = 0 := by
      rw [sub_smul, one_smul, ← hk', sub_self]
    rcases smul_eq_zero.mp hsub with h0 | hd0
    · exact sub_eq_zero.mp h0
    · exact absurd hd0 hd
  let β : K := lam ^ (e⁻¹).val
  have hpow_e : (c ^ e.val : D ≃ₗ[K] D) ^ (e⁻¹).val = c :=
    pow_pow_zmod_inv_eq_self (M := D ≃ₗ[K] D) (x := c) (p := p) (e := e) hcp hcne he
  have hcoe_k : (↑((c ^ e.val : D ≃ₗ[K] D) ^ (e⁻¹).val) : D →ₗ[K] D) =
      (↑(c ^ e.val : D ≃ₗ[K] D) : D →ₗ[K] D) ^ (e⁻¹).val :=
    map_pow (LinearEquiv.automorphismGroup.toLinearMapMonoidHom) (c ^ e.val) (e⁻¹).val
  have hc_d : c d = β • d := by
    have hk := h_eig.pow_apply (e⁻¹).val
    rw [← hcoe_k, hpow_e] at hk
    simpa [β] using hk
  have hβ_p : β ^ p = 1 := by
    dsimp only [β]
    rw [← pow_mul, Nat.mul_comm (e⁻¹).val p, pow_mul, hlam_p, one_pow]
  have hp_pos : 0 < p := (Fact.out : p.Prime).pos
  have hβ0 : β ≠ 0 := by
    intro h0
    rw [h0, zero_pow hp_pos.ne'] at hβ_p
    exact zero_ne_one hβ_p
  have hβ_ne_one : β ≠ 1 := by
    intro hβ1
    have : c d = d := by rw [hc_d, hβ1, one_smul]
    exact hd (hfix d this)
  have hlam_ne_one : lam ≠ 1 := by
    intro hlam
    exact hβ_ne_one (by dsimp only [β]; rw [hlam, one_pow])
  have hβe : β ^ e.val = lam := by
    dsimp only [β]
    have hinv : (e⁻¹) ≠ 0 := inv_ne_zero he
    have h := pow_pow_zmod_inv_eq_self (M := K) (x := lam) (p := p) (e := e⁻¹)
      hlam_p hlam_ne_one hinv
    simpa using h
  exact ⟨β, hc_d, hβ_p, hβ0, hβ_ne_one, hβe⟩

omit [Finite K] in
theorem linear_exponent_eq_or_neg (hdim : finrank K D = 2) (c : D ≃ₗ[K] D)
    {β β' : K} {e e' : ZMod p}
    (hβ_p : β ^ p = 1) (hβ0 : β ≠ 0) (hβ_ne_one : β ≠ 1)
    (hβ'0 : β' ≠ 0) (hβ'_ne_one : β' ≠ 1)
    {lam : K} (hβe : β ^ e.val = lam) (hβ'e' : β' ^ e'.val = lam)
    {d d' : D} (hd : d ≠ 0) (hd' : d' ≠ 0)
    (hc_d : c d = β • d) (hc_d' : c d' = β' • d')
    (hT : ∃ T : D ≃ₗ[K] D, T * c * T⁻¹ = c⁻¹) : e' = e ∨ e' = -e := by
  have hp_pos : 0 < p := (Fact.out : p.Prime).pos
  have hβfin : IsOfFinOrder β := isOfFinOrder_iff_pow_eq_one.mpr ⟨p, hp_pos, hβ_p⟩
  have hβord : orderOf β = p := orderOf_eq_prime hβ_p hβ_ne_one
  by_cases hβ_eq : β = β'
  · have h_eq_pow : β ^ e.val = β ^ e'.val := by rw [hβe, hβ_eq, hβ'e']
    have hmod : e.val ≡ e'.val [MOD p] := by
      have := hβfin.pow_eq_pow_iff_modEq.mp h_eq_pow
      rwa [hβord] at this
    have hee : e = e' := by
      rw [← ZMod.natCast_zmod_val e, ← ZMod.natCast_zmod_val e']
      exact (ZMod.natCast_eq_natCast_iff e.val e'.val p).mpr hmod
    exact Or.inl hee.symm
  · have hβ'_eq_inv : β' = β⁻¹ :=
      eq_inv_of_eigenvectors_of_conj_inv hdim hβ0 hβ'0 hd hd' hc_d hc_d' hβ_eq hβ'_ne_one hT
    have hβ'_pow_inv : (β ^ e'.val)⁻¹ = lam := by
      rw [← inv_pow, ← hβ'_eq_inv]
      exact hβ'e'
    have hprod : β ^ (e.val + e'.val) = 1 := by
      rw [pow_add, hβe, ← hβ'_pow_inv]
      exact inv_mul_cancel₀ (pow_ne_zero e'.val hβ0)
    have hdvd_order : orderOf β ∣ e.val + e'.val :=
      orderOf_dvd_iff_pow_eq_one.mpr hprod
    have hdvd : p ∣ e.val + e'.val := by
      rwa [hβord] at hdvd_order
    have hsum : (e + e' : ZMod p) = 0 := by
      have h0 : ((e.val + e'.val : ℕ) : ZMod p) = 0 :=
        (ZMod.natCast_eq_zero_iff (e.val + e'.val) p).mpr hdvd
      simpa using h0
    exact Or.inr (eq_neg_of_add_eq_zero_right hsum)

omit [Finite K] in
theorem eq_or_eq_neg_of_linear_primary
    (c : D ≃ₗ[K] D) (hdim : finrank K D = 2) (hcp : c ^ p = 1)
    (hfix : ∀ u, c u = u → u = 0)
    (hT : ∃ T : D ≃ₗ[K] D, T * c * T⁻¹ = c⁻¹)
    {h : K[X]} {e e' : ZMod p} (he : e ≠ 0) (he' : e' ≠ 0)
    (h1 : ∃ d : D, d ≠ 0 ∧
      aeval ((c ^ e.val : D ≃ₗ[K] D) : D →ₗ[K] D) h d = 0)
    (h2 : ∃ d : D, d ≠ 0 ∧
      aeval ((c ^ e'.val : D ≃ₗ[K] D) : D →ₗ[K] D) h d = 0)
    (hdeg1 : h.natDegree = 1) : e' = e ∨ e' = -e := by
  have hfin : 0 < finrank K D := by omega
  have hD : Nontrivial D := Module.finrank_pos_iff.mp hfin
  have hcne : c ≠ 1 := by
    intro hc
    obtain ⟨u, hu⟩ := exists_ne (0 : D)
    exact hu (hfix u (by rw [hc]; rfl))
  obtain ⟨d, hd, h1d⟩ := h1
  obtain ⟨d', hd', h2d⟩ := h2
  obtain ⟨a, ha, b, h_eq⟩ := Polynomial.natDegree_eq_one.mp hdeg1
  let lam : K := -(b * a⁻¹)
  have hce_d : ((c ^ e.val : D ≃ₗ[K] D) : D →ₗ[K] D) d = lam • d :=
    linear_aeval_eq_smul_of_eq ha h_eq h1d
  have hce'_d' : ((c ^ e'.val : D ≃ₗ[K] D) : D →ₗ[K] D) d' = lam • d' :=
    linear_aeval_eq_smul_of_eq ha h_eq h2d
  obtain ⟨β, hc_d, hβ_p, hβ0, hβ_ne_one, hβe⟩ :=
    linear_eigenvalue_pow c hcp hcne hfix he hd hce_d
  obtain ⟨β', hc_d', _, hβ'0, hβ'_ne_one, hβ'e'⟩ :=
    linear_eigenvalue_pow c hcp hcne hfix he' hd' hce'_d'
  exact linear_exponent_eq_or_neg hdim c hβ_p hβ0 hβ_ne_one hβ'0 hβ'_ne_one
    hβe hβ'e' hd hd' hc_d hc_d' hT

omit [Finite K] [CharP K 2] [FiniteDimensional K D] in
theorem dvd_of_irreducible_of_aeval_eq_zero {f : D →ₗ[K] D} {h q : K[X]}
    (hh : Irreducible h) {d : D} (hd : d ≠ 0)
    (hh_d : aeval f h d = 0) (hq_d : aeval f q d = 0) : h ∣ q := by
  by_contra hndvd
  have hcop : IsCoprime h q := hh.coprime_iff_not_dvd.mpr hndvd
  obtain ⟨u, v, huv⟩ := hcop
  have h := congrArg (fun r : K[X] => aeval f r d) huv
  simp only [map_add, map_mul, aeval_one] at h
  rw [LinearMap.add_apply, Module.End.mul_apply, Module.End.mul_apply, hh_d, hq_d,
    map_zero, map_zero, add_zero, Module.End.one_apply] at h
  exact hd h.symm

omit [Finite K] [CharP K 2] [FiniteDimensional K D] in
theorem quadratic_apply_apply_eq_smul_of_aeval_eq_zero {f : D →ₗ[K] D} {h : K[X]}
    (hdeg : h.natDegree = 2) {d : D} (hd : aeval f h d = 0) :
    f (f d) = (-(h.coeff 1 * (h.coeff 2)⁻¹)) • f d +
      (-(h.coeff 0 * (h.coeff 2)⁻¹)) • d := by
  have h0 : h ≠ 0 := by
    intro hzero
    rw [hzero, natDegree_zero] at hdeg
    omega
  have ha : h.coeff 2 ≠ 0 := by
    have hlead : h.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr h0
    simpa [Polynomial.leadingCoeff, hdeg] using hlead
  have h_expand : h = C (h.coeff 2) * X ^ 2 + C (h.coeff 1) * X + C (h.coeff 0) := by
    conv_lhs => rw [h.as_sum_range_C_mul_X_pow]
    rw [show h.natDegree + 1 = 3 by omega]
    simp [Finset.sum_range_succ, pow_succ, add_assoc]
    ring
  rw [h_expand] at hd
  have hrel : h.coeff 2 • (f (f d)) + h.coeff 1 • (f d) + h.coeff 0 • d = 0 := by
    simpa [map_add, map_mul, pow_two, smul_add, add_assoc] using hd
  have h' := congrArg (fun z : D => (h.coeff 2)⁻¹ • z) hrel
  simp only [smul_add, smul_smul, smul_zero, inv_mul_cancel₀ ha, one_smul] at h'
  have h'' : f (f d) + (((h.coeff 2)⁻¹ * h.coeff 1) • f d +
      ((h.coeff 2)⁻¹ * h.coeff 0) • d) = 0 := by
    rw [← add_assoc]
    exact h'
  have hx : f (f d) = -(((h.coeff 2)⁻¹ * h.coeff 1) • f d +
      ((h.coeff 2)⁻¹ * h.coeff 0) • d) := add_eq_zero_iff_eq_neg.mp h''
  rw [hx, neg_add, neg_smul, neg_smul]
  congr 1
  · rw [mul_comm]
  · rw [mul_comm]

omit [Finite K] [CharP K 2] [FiniteDimensional K D] in
theorem linearIndependent_pair_of_irreducible_aeval_ne_one
    {f : D ≃ₗ[K] D} {h : K[X]} (hh : Irreducible h) (hdeg : h.natDegree ≠ 1)
    {d : D} (hd : d ≠ 0) (hd0 : aeval (f : D →ₗ[K] D) h d = 0) :
    LinearIndependent K ![d, (f : D →ₗ[K] D) d] := by
  rw [linearIndependent_fin2]
  refine ⟨?_, ?_⟩
  · intro hzero
    exact hd (f.injective (by simpa using hzero))
  · intro a ha
    have ha0 : a ≠ 0 := by
      intro h0
      rw [h0, zero_smul] at ha
      exact hd ha.symm
    have hce_eq : (f : D →ₗ[K] D) d = a⁻¹ • d := by
      have h' := congrArg (fun x : D => a⁻¹ • x) ha
      simpa [smul_smul, inv_mul_cancel₀ ha0] using h'
    have hq_d : aeval (f : D →ₗ[K] D) (X - C a⁻¹) d = 0 := by
      simp [hce_eq]
    have hdvd := dvd_of_irreducible_of_aeval_eq_zero hh hd hd0 hq_d
    have hdeg_le : h.natDegree ≤ (X - C a⁻¹).natDegree :=
      natDegree_le_of_dvd hdvd (X_sub_C_ne_zero a⁻¹)
    rw [natDegree_X_sub_C] at hdeg_le
    have hdeg_pos : 0 < h.natDegree := hh.natDegree_pos
    rcases Nat.lt_or_gt_of_ne hdeg with hlt | hgt
    · omega
    · omega

omit [Finite K] [CharP K 2] [FiniteDimensional K D] in
theorem natDegree_eq_two_of_irreducible_aeval_ne_one
    (hdim : finrank K D = 2) {f : D →ₗ[K] D} {h : K[X]}
    (hh : Irreducible h) (hdeg : h.natDegree ≠ 1)
    {d : D} (hd : d ≠ 0) (hli : LinearIndependent K ![d, f d])
    (hd0 : aeval f h d = 0) : h.natDegree = 2 := by
  let b : Basis (Fin 2) K D :=
    basisOfLinearIndependentOfCardEqFinrank (b := ![d, f d]) hli (by simp [hdim])
  have hb0 : b 0 = d := by simp [b]
  have hb1 : b 1 = f d := by simp [b]
  let alpha : K := b.repr (f (f d)) 1
  let beta : K := b.repr (f (f d)) 0
  have hf2_eq : f (f d) = alpha • f d + beta • d := by
    have hsum := b.sum_repr (f (f d))
    rw [Fin.sum_univ_two] at hsum
    rw [hb0, hb1] at hsum
    conv_lhs => rw [← hsum]
    dsimp only [alpha, beta]
    rw [add_comm]
  let q : K[X] := C (1 : K) * X ^ 2 + C (-alpha) * X + C (-beta)
  have hq_d : aeval f q d = 0 := by
    simp only [q, map_add, map_mul, aeval_C, aeval_X, Algebra.algebraMap_eq_smul_one,
      one_smul, pow_two, Module.End.mul_apply, LinearMap.add_apply,
      LinearMap.smul_apply, Module.End.one_apply]
    rw [hf2_eq]
    module
  have hdvd_q : h ∣ q := dvd_of_irreducible_of_aeval_eq_zero hh hd hd0 hq_d
  have hq_deg : q.natDegree = 2 := Polynomial.natDegree_quadratic (by norm_num)
  have hq_ne : q ≠ 0 := by
    intro hzero
    rw [hzero, natDegree_zero] at hq_deg
    omega
  have hdeg_le2 : h.natDegree ≤ 2 := by
    have := natDegree_le_of_dvd hdvd_q hq_ne
    rwa [hq_deg] at this
  have hdeg_pos : 0 < h.natDegree := hh.natDegree_pos
  rcases Nat.lt_or_gt_of_ne hdeg with hlt | hgt
  · omega
  · omega

omit [Finite K] [CharP K 2] [FiniteDimensional K D] in
theorem exists_conj_of_quadratic_relation (hdim : finrank K D = 2)
    {f g : D →ₗ[K] D} {d d' : D}
    (hli : LinearIndependent K ![d, f d])
    (hli' : LinearIndependent K ![d', g d'])
    {alpha beta : K}
    (hf : f (f d) = alpha • f d + beta • d)
    (hg : g (g d') = alpha • g d' + beta • d') :
    ∃ θ : D ≃ₗ[K] D, ∀ x, θ (f x) = g (θ x) := by
  let b : Basis (Fin 2) K D :=
    basisOfLinearIndependentOfCardEqFinrank (b := ![d, f d]) hli (by simp [hdim])
  let b' : Basis (Fin 2) K D :=
    basisOfLinearIndependentOfCardEqFinrank (b := ![d', g d']) hli' (by simp [hdim])
  have hb0 : b 0 = d := by simp [b]
  have hb1 : b 1 = f d := by simp [b]
  have hb'0 : b' 0 = d' := by simp [b']
  have hb'1 : b' 1 = g d' := by simp [b']
  let θ : D ≃ₗ[K] D := b.equiv b' (Equiv.refl (Fin 2))
  have hθ_b0 : θ (b 0) = b' 0 := by simp [θ]
  have hθ_b1 : θ (b 1) = b' 1 := by simp [θ]
  have hθ_f_d : θ (f d) = g (θ d) := by
    have h1 : f d = b 1 := hb1.symm
    have h2 : d = b 0 := hb0.symm
    rw [h1, h2, hθ_b1, hθ_b0, hb'0, hb'1]
  have hθ_f_fd : θ (f (f d)) = g (g (θ d)) := by
    have hθd : θ d = d' := by
      rw [show d = b 0 from hb0.symm, hθ_b0, hb'0]
    rw [hf, map_add, map_smul, map_smul, hθ_f_d, hθd, ← hg]
  have hlin : (θ : D →ₗ[K] D) * f = g * (θ : D →ₗ[K] D) := by
    apply b.ext
    intro i
    fin_cases i
    · change θ (f (b 0)) = g (θ (b 0))
      rw [hb0]
      exact hθ_f_d
    · change θ (f (b 1)) = g (θ (b 1))
      rw [hb1, hθ_f_d]
      exact hθ_f_fd
  refine ⟨θ, fun x => ?_⟩
  exact congrArg (fun h : D →ₗ[K] D => h x) hlin

theorem conj_pow_eq_pow_of_zmod {G : Type*} [Group G] {c : G}
    (hcp : c ^ p = 1) (hcne : c ≠ 1) {e e' : ZMod p} (he : e ≠ 0)
    (θ : G) (hθ : θ * (c ^ e.val) * θ⁻¹ = c ^ e'.val) :
    θ * c * θ⁻¹ = c ^ (e' * e⁻¹).val := by
  have hc := pow_pow_zmod_inv_eq_self (M := G) (x := c) (p := p) (e := e) hcp hcne he
  have hordc : orderOf c = p := orderOf_eq_prime hcp hcne
  calc
    θ * c * θ⁻¹ = θ * ((c ^ e.val) ^ (e⁻¹).val) * θ⁻¹ := by rw [hc]
    _ = (θ * (c ^ e.val) * θ⁻¹) ^ (e⁻¹).val := by rw [conj_pow]
    _ = (c ^ e'.val) ^ (e⁻¹).val := by rw [hθ]
    _ = c ^ (e'.val * (e⁻¹).val) := by rw [pow_mul]
    _ = c ^ (e' * e⁻¹).val := by
      rw [pow_eq_pow_iff_modEq, hordc]
      rw [← ZMod.natCast_eq_natCast_iff]
      simp only [Nat.cast_mul, ZMod.natCast_zmod_val]

omit [Finite K] [CharP K 2] [FiniteDimensional K D] in
theorem eq_or_eq_neg_of_hroots (c : D ≃ₗ[K] D) (hcp : c ^ p = 1) (hcne : c ≠ 1)
    (hroots : ∀ (e : ZMod p) (θ : D →ₗ[K] D), Function.Injective θ →
      (∀ x, θ (c x) = (c ^ e.val) (θ x)) → e = 1 ∨ e = -1)
    {e e' : ZMod p} (he : e ≠ 0) (θ : D ≃ₗ[K] D)
    (hθ : ∀ x, θ (((c ^ e.val : D ≃ₗ[K] D) : D →ₗ[K] D) x) =
      ((c ^ e'.val : D ≃ₗ[K] D) : D →ₗ[K] D) (θ x)) :
    e' = e ∨ e' = -e := by
  have hθ_eq : θ * (c ^ e.val) = (c ^ e'.val) * θ := by
    ext x
    exact hθ x
  have hθ_conj : θ * (c ^ e.val) * θ⁻¹ = c ^ e'.val := by
    have h := congrArg (fun x : D ≃ₗ[K] D => x * θ⁻¹) hθ_eq
    simpa [mul_assoc] using h
  have hθ_conj_pow : θ * c * θ⁻¹ = c ^ (e' * e⁻¹).val :=
    conj_pow_eq_pow_of_zmod hcp hcne he θ hθ_conj
  have hθ_c : θ * c = (c ^ (e' * e⁻¹).val) * θ := by
    have h := congrArg (fun x : D ≃ₗ[K] D => x * θ) hθ_conj_pow
    simpa [mul_assoc] using h
  have hθ_c_apply : ∀ x, θ (c x) = (c ^ (e' * e⁻¹).val) (θ x) := by
    intro x
    have h := congrArg (fun f : D ≃ₗ[K] D => f x) hθ_c
    simpa using h
  have hf := hroots (e' * e⁻¹) (θ : D →ₗ[K] D) θ.injective hθ_c_apply
  rcases hf with hf | hf
  · left
    calc
      e' = e' * 1 := (mul_one e').symm
      _ = e' * (e * e⁻¹) := by rw [mul_inv_cancel₀ he]
      _ = (e' * e⁻¹) * e := by ring
      _ = 1 * e := by rw [hf]
      _ = e := one_mul e
  · right
    calc
      e' = e' * 1 := (mul_one e').symm
      _ = e' * (e * e⁻¹) := by rw [mul_inv_cancel₀ he]
      _ = (e' * e⁻¹) * e := by ring
      _ = (-1) * e := by rw [hf]
      _ = -e := by ring

omit [Finite K] [CharP K 2] in
theorem eq_or_eq_neg_of_primary_of_natDegree_ne_one
    (c : D ≃ₗ[K] D) (hdim : finrank K D = 2) (hcp : c ^ p = 1)
    (hfix : ∀ u, c u = u → u = 0)
    (hroots : ∀ (e : ZMod p) (θ : D →ₗ[K] D), Function.Injective θ →
      (∀ x, θ (c x) = (c ^ e.val) (θ x)) → e = 1 ∨ e = -1)
    {h : K[X]} (hh : Irreducible h) {e e' : ZMod p} (he : e ≠ 0)
    (h1 : ∃ d : D, d ≠ 0 ∧
      aeval ((c ^ e.val : D ≃ₗ[K] D) : D →ₗ[K] D) h d = 0)
    (h2 : ∃ d : D, d ≠ 0 ∧
      aeval ((c ^ e'.val : D ≃ₗ[K] D) : D →ₗ[K] D) h d = 0)
    (hdeg_ne1 : h.natDegree ≠ 1) : e' = e ∨ e' = -e := by
  have hfin : 0 < finrank K D := by omega
  have hD : Nontrivial D := Module.finrank_pos_iff.mp hfin
  have hcne : c ≠ 1 := by
    intro hc
    obtain ⟨u, hu⟩ := exists_ne (0 : D)
    exact hu (hfix u (by rw [hc]; rfl))
  obtain ⟨d, hd, h1d⟩ := h1
  obtain ⟨d', hd', h2d⟩ := h2
  let ce : D ≃ₗ[K] D := c ^ e.val
  let ce' : D ≃ₗ[K] D := c ^ e'.val
  have h1d' : aeval (ce : D →ₗ[K] D) h d = 0 := h1d
  have h2d' : aeval (ce' : D →ₗ[K] D) h d' = 0 := h2d
  have hli := linearIndependent_pair_of_irreducible_aeval_ne_one hh hdeg_ne1 hd h1d'
  have hli' := linearIndependent_pair_of_irreducible_aeval_ne_one hh hdeg_ne1 hd' h2d'
  have hdeg2 := natDegree_eq_two_of_irreducible_aeval_ne_one hdim hh hdeg_ne1 hd hli h1d'
  have hrel := quadratic_apply_apply_eq_smul_of_aeval_eq_zero hdeg2 h1d'
  have hrel' := quadratic_apply_apply_eq_smul_of_aeval_eq_zero hdeg2 h2d'
  obtain ⟨θ, hθ⟩ := exists_conj_of_quadratic_relation hdim hli hli' hrel hrel'
  exact eq_or_eq_neg_of_hroots c hcp hcne hroots he θ hθ

omit [Finite K] in
theorem blockClass (hp2 : p ≠ 2) (c : D ≃ₗ[K] D) (hdim : finrank K D = 2) (hcp : c ^ p = 1)
    (hfix : ∀ u, c u = u → u = 0) (hT : ∃ T : D ≃ₗ[K] D, T * c * T⁻¹ = c⁻¹)
    (hroots : ∀ (e : ZMod p) (θ : D →ₗ[K] D), Function.Injective θ →
      (∀ x, θ (c x) = (c ^ e.val) (θ x)) → e = 1 ∨ e = -1)
    {h : K[X]} (hh : Irreducible h) (hX : h ≠ X - 1) {e e' : ZMod p} (he : e ≠ 0) (he' : e' ≠ 0)
    (h1 : ∃ d : D, d ≠ 0 ∧ aeval ((c ^ e.val : D ≃ₗ[K] D) : D →ₗ[K] D) h d = 0)
    (h2 : ∃ d : D, d ≠ 0 ∧ aeval ((c ^ e'.val : D ≃ₗ[K] D) : D →ₗ[K] D) h d = 0) :
    e' = e ∨ e' = -e := by
  have _ : p ≠ 2 := hp2
  have _ : h ≠ X - 1 := hX
  by_cases hdeg1 : h.natDegree = 1
  · exact eq_or_eq_neg_of_linear_primary c hdim hcp hfix hT he he' h1 h2 hdeg1
  · exact eq_or_eq_neg_of_primary_of_natDegree_ne_one c hdim hcp hfix hroots hh he h1 h2 hdeg1

end OrthTorus

end CFSG.StandardType

end
