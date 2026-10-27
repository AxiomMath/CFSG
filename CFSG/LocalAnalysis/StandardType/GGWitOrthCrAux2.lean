module

public import CFSG.LocalAnalysis.StandardType.GGWitOrthCrAux
public import CFSG.LocalAnalysis.StandardType.GGSecFiveZSInputs

public section

namespace CFSG.StandardType.ZS

open QuadraticMap

theorem owCr_Q_add_eq {K : Type*} [Field K] {U : Type*} [AddCommGroup U] [Module K U] (Q : QuadraticForm K U) (a u : U) (hu : Q u = 0)
    (hau : polarBilin Q u a = 0) : Q (a + u) = Q a := by
  rw [QuadraticMap.map_add Q, hu, polar_comm, ← polarBilin_apply_apply, hau]
  abel

noncomputable def owCr_N {K : Type*} [Field K] {U : Type*} [AddCommGroup U] [Module K U] (Q : QuadraticForm K U) (a u : U) (ha : Q a ≠ 0) : U →ₗ[K] U :=
  (Q a)⁻¹ • (((polarBilin Q).flip u).smulRight a)
    - (Q a)⁻¹ • ((((polarBilin Q).flip a) + ((polarBilin Q).flip u)).smulRight u)

theorem owCr_N_apply {K : Type*} [Field K] {U : Type*} [AddCommGroup U] [Module K U] (Q : QuadraticForm K U) (a u : U) (ha : Q a ≠ 0) (v : U) :
    owCr_N Q a u ha v = (polarBilin Q v u / Q a) • a
      - ((polarBilin Q v a + polarBilin Q v u) / Q a) • u := by
  simp only [owCr_N, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.add_apply,
    LinearMap.smulRight_apply, LinearMap.flip_apply, polarBilin_apply_apply, smul_smul,
    smul_sub, smul_add, div_eq_inv_mul, map_sub, map_add, map_smul]

theorem owCr_T_apply {K : Type*} [Field K] {U : Type*} [AddCommGroup U] [Module K U] (Q : QuadraticForm K U) (a u : U) (ha : Q a ≠ 0)
    (ha' : Q (a + u) ≠ 0) (hu : Q u = 0) (hau : polarBilin Q u a = 0) (v : U) :
    (owCr_orthRefl Q a ha * owCr_orthRefl Q (a + u) ha') v
      = v + (polarBilin Q v u / Q a) • a
        - ((polarBilin Q v a + polarBilin Q v u) / Q a) • u := by
  rw [LinearEquiv.mul_apply, owCr_orthRefl_apply, owCr_orthRefl_apply,
    owCr_Q_add_eq Q a u hu hau]
  have hcoef : ∀ x y : K,
      (Q a)⁻¹ * (x - (Q a)⁻¹ * (x + y) * (Q a + Q a + 0)) = (Q a)⁻¹ * (-x - 2 * y) := by
    intro x y
    rw [show Q a + Q a + 0 = 2 * Q a by ring]
    field_simp
    ring
  simp only [map_sub, map_add, map_smul, LinearMap.flip_apply, polarBilin_apply_apply,
    polar_self, polar_comm, polar_add_left, polar_smul_left, polar_neg_left, polar_sub_left,
    hu, hau, smul_eq_mul, two_smul, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.add_apply, div_eq_inv_mul, inv_pow]
  rw [hcoef (polar Q a v) (polar Q u v)]
  module

theorem owCr_N_eq_T {K : Type*} [Field K] {U : Type*} [AddCommGroup U] [Module K U] (Q : QuadraticForm K U) (a u : U) (ha : Q a ≠ 0)
    (ha' : Q (a + u) ≠ 0) (hu : Q u = 0) (hau : polarBilin Q u a = 0) :
    owCr_N Q a u ha
      = ((owCr_orthRefl Q a ha * owCr_orthRefl Q (a + u) ha' : U ≃ₗ[K] U) : U →ₗ[K] U) - 1 := by
  ext v
  change owCr_N Q a u ha v
    = (owCr_orthRefl Q a ha * owCr_orthRefl Q (a + u) ha') v - v
  rw [owCr_N_apply, owCr_T_apply Q a u ha ha' hu hau]
  module

theorem owCr_N_cube {K : Type*} [Field K] {U : Type*} [AddCommGroup U] [Module K U] (Q : QuadraticForm K U) (a u : U) (ha : Q a ≠ 0) (hu : Q u = 0)
    (hau : polarBilin Q u a = 0) :
    owCr_N Q a u ha ^ 3 = 0 := by
  have hau' : polar Q a u = 0 := by rw [polar_comm, ← polarBilin_apply_apply, hau]
  ext v
  simp only [pow_succ, pow_zero, Module.End.mul_apply, Module.End.one_apply, owCr_N_apply,
    map_sub, map_add, map_smul, LinearMap.flip_apply, polarBilin_apply_apply, polar_self,
    polar_comm, polar_add_left, polar_smul_left, polar_neg_left, polar_sub_left, hu, hau, hau',
    smul_eq_mul, two_smul, smul_zero, zero_mul, mul_zero, LinearMap.zero_apply,
    inv_mul_cancel₀ ha, mul_inv_cancel₀ ha, inv_pow]
  module

theorem owCr_order_orthRefl {K : Type*} [Field K] {U : Type*} [AddCommGroup U] [Module K U] {p : ℕ} [CharP K p] (hp : p.Prime) (hp3 : 3 ≤ p)
    (Q : QuadraticForm K U) (a u : U) (ha : Q a ≠ 0) (ha' : Q (a + u) ≠ 0)
    (hu : Q u = 0) (hau : polarBilin Q u a = 0) (hu_ne : u ≠ 0) :
    orderOf (owCr_orthRefl Q a ha * owCr_orthRefl Q (a + u) ha') = p := by
  haveI : Fact p.Prime := ⟨hp⟩
  have ha_ne : a ≠ 0 := fun h => ha (by rw [h, QuadraticMap.map_zero])
  haveI : CharP (U →ₗ[K] U) p :=
    Module.charP_end (p := p) ⟨a, (Ideal.torsionOf_eq_bot_iff_of_isTorsionFree (R := K) (M := U) a).mpr ha_ne⟩
  have h2 : (2 : K) ≠ 0 := by
    intro h
    have hdvd : p ∣ 2 := (CharP.cast_eq_zero_iff K p 2).mp h
    have : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
    omega
  set T : U ≃ₗ[K] U := owCr_orthRefl Q a ha * owCr_orthRefl Q (a + u) ha' with hT
  set N : U →ₗ[K] U := owCr_N Q a u ha with hN
  have hNT : (T : U →ₗ[K] U) = 1 + N := by
    rw [hN, hT, owCr_N_eq_T Q a u ha ha' hu hau]
    abel
  have hNcube : N ^ 3 = 0 := by rw [hN]; exact owCr_N_cube Q a u ha hu hau
  have hNp : N ^ p = 0 := by
    rw [← Nat.add_sub_cancel' hp3, pow_add, hNcube, zero_mul]
  have hTp_lin : ((T : U →ₗ[K] U)) ^ p = 1 := by
    rw [hNT]
    rw [add_pow_char_of_commute (p := p) (x := (1 : U →ₗ[K] U)) (y := N)
      (Commute.one_left N), hNp]
    simp
  have hcoe : ∀ n, ((T ^ n : U ≃ₗ[K] U) : U →ₗ[K] U) = ((T : U →ₗ[K] U)) ^ n := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [pow_succ, pow_succ, LinearEquiv.coe_toLinearMap_mul, ih]
  have hTp : T ^ p = 1 := by
    apply LinearEquiv.toLinearMap_injective
    rw [hcoe p, hTp_lin, LinearEquiv.coe_toLinearMap_one]
    rfl
  have hNne : N ≠ 0 := by
    intro h
    have hval : N a = 0 := by rw [h]; rfl
    have hNa : N a = (-2 : K) • u := by
      rw [hN, owCr_N_apply]
      simp only [polarBilin_apply_apply, polar_self, two_smul]
      rw [show polar Q a u = 0 by rw [polar_comm, ← polarBilin_apply_apply, hau]]
      rw [show Q a + Q a + 0 = 2 * Q a by ring, mul_div_cancel_right₀ _ ha]
      module
    rw [hNa] at hval
    rcases smul_eq_zero.mp hval with h' | h'
    · exact absurd h' (neg_ne_zero.mpr h2)
    · exact hu_ne h'
  have hTne : T ≠ 1 := by
    intro h
    apply hNne
    have h2' : (1 : U →ₗ[K] U) + N = (1 : U →ₗ[K] U) + 0 := by
      rw [add_zero, ← hNT, h]
      rfl
    exact add_left_cancel h2'
  exact orderOf_eq_prime hTp hTne


theorem owCr_wit_orth_cr {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {U : Type}
    [AddCommGroup U] [Module (ZMod p) U] [Module.Finite (ZMod p) U]
    (hp5 : 5 ≤ p) (hd : 4 ≤ Module.finrank (ZMod p) U)
    (Q : QuadraticForm (ZMod p) U) (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {A : Subgroup (U ≃ₗ[ZMod p] U)} (hA : ∀ g : U ≃ₗ[ZMod p] U, g ∈ A ↔ IsIsom p Q g) :
    ∀ r ∈ A, IsRefl p r → WitCR p A r := by
  intro r hrA hr
  haveI : NeZero p := ⟨hp.ne_zero⟩
  letI : Field (ZMod p) := @ZMod.instField p ⟨hp⟩
  have h2K : (2 : ZMod p) ≠ 0 := by
    intro h
    have hdiv : p ∣ 2 := (CharP.cast_eq_zero_iff (ZMod p) p 2).mp h
    have : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdiv
    omega
  have hodd : Odd (Nat.card (ZMod p)) := by
    rw [Nat.card_zmod]
    exact hp.eq_two_or_odd'.resolve_left hp2
  obtain ⟨hr2, hrk⟩ := hr
  have hisom : ∀ v, Q (r v) = Q v := (hA r).mp hrA
  obtain ⟨a, ha, rfl⟩ := owCr_refl_form Q hQ h2K hr2 hrk hisom
  obtain ⟨u, hu_ne, huQ, huB⟩ := owCr_exists_isotropic_orth hodd Q hQ hd a ha
  have ha' : Q (a + u) ≠ 0 := by
    rw [owCr_Q_add_eq Q a u huQ huB]; exact ha
  have h4 : (4 : ZMod p) ≠ 0 := by
    intro h
    have hdiv : p ∣ 4 := (CharP.cast_eq_zero_iff (ZMod p) p 4).mp h
    have : p ≤ 4 := Nat.le_of_dvd (by norm_num) hdiv
    omega
  let b : U := (2 : ZMod p) • a + u
  have hBau : polar Q a u = 0 := by
    rw [polar_comm]
    exact (polarBilin_apply_apply Q u a).symm.trans huB
  have hbQ : Q b = 4 * Q a := by
    have hb_eq : b = (2 : ZMod p) • a + u := rfl
    rw [hb_eq, QuadraticMap.map_add Q, QuadraticMap.map_smul, polar_smul_left, hBau, huQ]
    ring
  have hb : Q b ≠ 0 := by rw [hbQ]; exact mul_ne_zero h4 ha
  let g : U ≃ₗ[ZMod p] U := owCr_orthRefl Q b hb
  have hBab : polarBilin Q a b = 4 * Q a := by
    have hb_eq : b = (2 : ZMod p) • a + u := rfl
    rw [hb_eq, polarBilin_apply_apply, polar_add_right, polar_smul_right, polar_self, hBau]
    ring
  have hga : g a = -(a + u) := by
    have hg_eq : g = owCr_orthRefl Q b hb := rfl
    rw [hg_eq, owCr_orthRefl_apply]
    have hratio : polarBilin Q a b / Q b = 1 := by
      rw [hBab, hbQ]
      exact div_self (mul_ne_zero h4 ha)
    rw [hratio, one_smul]
    simp only [b]
    module
  have hg : ∀ v, Q (g v) = Q v := owCr_orthRefl_isIsom Q b hb
  have hga_ne : Q (g a) ≠ 0 := by rw [hg a]; exact ha
  have hconj : g * owCr_orthRefl Q a ha * g⁻¹ = owCr_orthRefl Q (a + u) ha' := by
    rw [owCr_orthRefl_conj Q g hg a ha hga_ne]
    convert owCr_orthRefl_neg Q (a + u) ha' (show Q (-(a + u)) ≠ 0 by rwa [← hga]) using 2
  have horder : orderOf (owCr_orthRefl Q a ha * owCr_orthRefl Q (a + u) ha') = p :=
    owCr_order_orthRefl hp (by omega) Q a u ha ha' huQ huB hu_ne
  refine ⟨g, (hA g).mpr (owCr_orthRefl_isIsom Q b hb), ?_⟩
  rw [hconj, horder]
  omega

end CFSG.StandardType.ZS

end
