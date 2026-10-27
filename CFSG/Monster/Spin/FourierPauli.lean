module

public import CFSG.Monster.Spin.Coords
import CFSG.Monster.FourierTriality

public noncomputable section

namespace CFSG.Monster.Spin

open CFSG.Monster.Code Matrix

private theorem zmod2_cases : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide

private theorem add_eq_one_of_ne : ∀ a b : ZMod 2, a ≠ b → a + b = 1 := by decide

private theorem two_eq_zero' : (2 : ZMod 2) = 0 := rfl

private theorem zero_ne_one' : (0 : ZMod 2) ≠ 1 := by decide

private theorem sgn_one' : sgn 1 = -1 := rfl

@[expose] def Fvec (u : C) : SpinIdx → ℚ := E 0 (π₀ u) + sgn (μ₀ u) • E 1 (π₀ u)

theorem existsUnique_add_smul_ΩC (u : C) :
    ∃! p : C₀ × ZMod 2, u = (p.1 : C) + p.2 • ΩC := by
  refine ⟨(π₀ u, μ₀ u), (π₀_add_μ₀ u).symm, fun p hp => ?_⟩
  have h : splitC u = p := by
    rw [hp]
    exact splitC.apply_symm_apply p
  exact h.symm

theorem Fvec_add_smul_ΩC (c : C₀) (k : ZMod 2) :
    Fvec ((c : C) + k • ΩC) = E 0 c + sgn k • E 1 c := by
  have h1 : π₀ ((c : C) + k • ΩC) = c := by
    rw [map_add, map_smul, π₀_coe, π₀_ΩC, smul_zero, add_zero]
  have h2 : μ₀ ((c : C) + k • ΩC) = k := by
    rw [map_add, map_smul, μ₀_coe, μ₀_ΩC, smul_eq_mul, mul_one, zero_add]
  rw [Fvec, h1, h2]

theorem Fvec_coe (c : C₀) : Fvec (c : C) = E 0 c + E 1 c := by
  have := Fvec_add_smul_ΩC c 0
  rwa [zero_smul, add_zero, sgn_zero, one_smul] at this

theorem Fvec_coe_add_ΩC (c : C₀) : Fvec ((c : C) + ΩC) = E 0 c - E 1 c := by
  have := Fvec_add_smul_ΩC c 1
  rwa [one_smul, sgn_one', neg_one_smul, ← sub_eq_add_neg] at this

theorem E_zero_eq (c : C₀) : E 0 c = (1 / 2 : ℚ) • (Fvec (c : C) + Fvec ((c : C) + ΩC)) := by
  rw [Fvec_coe, Fvec_coe_add_ΩC]
  module

theorem E_one_eq (c : C₀) : E 1 c = (1 / 2 : ℚ) • (Fvec (c : C) - Fvec ((c : C) + ΩC)) := by
  rw [Fvec_coe, Fvec_coe_add_ΩC]
  module

theorem Fvec_dotProduct_Fvec (u v : C) : Fvec u ⬝ᵥ Fvec v = if u = v then 2 else 0 := by
  simp only [Fvec, add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul,
    E_dotProduct_E, Prod.mk.injEq, smul_eq_mul, zero_ne_one', zero_ne_one'.symm, false_and,
    ite_false, true_and, mul_zero, add_zero, zero_add]
  by_cases hπ : π₀ u = π₀ v
  · by_cases hμ : μ₀ u = μ₀ v
    · have huv : u = v := eq_of_π₀_μ₀ hπ hμ
      subst huv
      simp only [ite_true, mul_one, sgn_mul_self]
      norm_num
    · have huv : u ≠ v := fun h => hμ (h ▸ rfl)
      simp only [hπ, ite_true, huv, ite_false, mul_one]
      rw [← sgn_add, add_eq_one_of_ne _ _ (Ne.symm hμ), sgn_one']
      norm_num
  · have huv : u ≠ v := fun h => hπ (h ▸ rfl)
    simp only [hπ, huv, ite_false, mul_zero, add_zero]

theorem linearIndependent_Fvec : LinearIndependent ℚ Fvec := by
  rw [Fintype.linearIndependent_iff]
  intro g hg v
  have h := congrArg (· ⬝ᵥ Fvec v) hg
  simp only [sum_dotProduct, smul_dotProduct, Fvec_dotProduct_Fvec, smul_eq_mul, mul_ite,
    mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true, zero_dotProduct] at h
  linarith

theorem card_C_eq_finrank : Fintype.card C = Module.finrank ℚ (SpinIdx → ℚ) := by
  rw [card_C, Module.finrank_fintype_fun_eq_card, card_spinIdx]

@[expose] def Fbasis : Module.Basis C ℚ (SpinIdx → ℚ) :=
  basisOfLinearIndependentOfCardEqFinrank linearIndependent_Fvec card_C_eq_finrank

@[simp] theorem coe_Fbasis : ⇑Fbasis = Fvec :=
  coe_basisOfLinearIndependentOfCardEqFinrank _ _

theorem E_vecMul_qmatR (s : ZMod 2) (a : C) (δ : Cocode) (η : ZMod 2) (x : C₀) :
    E η x ᵥ* qmatR ℚ s a δ =
      sgn (s + η * μ₀ a + pair (shift a x) δ) • E (η + pair ΩC δ) (shift a x) :=
  single_vecMul_qmatR s a δ (η, x)

theorem π₀_add_eq_shift (u a : C) : π₀ (u + a) = shift a (π₀ u) := by
  rw [shift, map_add, map_add, π₀_coe]

theorem Fvec_vecMul_Tmat (u a : C) : Fvec u ᵥ* Tmat a = Fvec (u + a) := by
  rw [Tmat_eq_qmatR, Fvec, add_vecMul, smul_vecMul, E_vecMul_qmatR, E_vecMul_qmatR, Fvec,
    π₀_add_eq_shift, map_add]
  simp only [pair_zero_right, add_zero, zero_mul, zero_add, one_mul, smul_smul, ← sgn_add,
    sgn_zero, one_smul]

theorem Fvec_vecMul_Dmat (u : C) (δ : Cocode) : Fvec u ᵥ* Dmat δ = sgn (pair u δ) • Fvec u := by
  rw [Fvec, add_vecMul, smul_vecMul, E_vecMul_Dmat, E_vecMul_Dmat]
  have hp := pair_π₀ u δ
  rcases zmod2_cases (pair ΩC δ) with h | h
  · rw [h, mul_zero, add_zero] at hp
    rw [h, add_zero, add_zero, hp, smul_add, smul_comm (sgn (μ₀ u))]
  · rw [h, mul_one] at hp
    have h1 : (1 : ZMod 2) + 1 = 0 := rfl
    rw [h, zero_add, h1, hp, sgn_add, smul_add, smul_smul, smul_smul, mul_left_comm,
      sgn_mul_self, mul_one]
    abel

theorem Fvec_vecMul_zmat_pow (u : C) (s : ZMod 2) : Fvec u ᵥ* zmat ^ s.val = sgn s • Fvec u := by
  rcases zmod2_cases s with rfl | rfl
  · rw [ZMod.val_zero, pow_zero, vecMul_one, sgn_zero, one_smul]
  · rw [ZMod.val_one, pow_one, zmat, vecMul_neg, vecMul_one, sgn_one', neg_one_smul]

theorem Fvec_vecMul_qmatR (u : C) (s : ZMod 2) (a : C) (δ : Cocode) :
    Fvec u ᵥ* qmatR ℚ s a δ = sgn (s + pair (u + a) δ) • Fvec (u + a) := by
  rw [← zmat_pow_mul_Tmat_mul_Dmat, ← vecMul_vecMul, ← vecMul_vecMul, Fvec_vecMul_zmat_pow,
    smul_vecMul, Fvec_vecMul_Tmat, smul_vecMul, Fvec_vecMul_Dmat, smul_smul, ← sgn_add]

theorem Fvec_vecMul_Xmat (u : C) (e : Parker) :
    Fvec u ᵥ* Xmat e = sgn (e.sign + P e.code + θ e.code u) • Fvec (u + e.code) := by
  rw [Xmat_eq_qmatR, Fvec_vecMul_qmatR, pair_thetaD, θ_add_right, θ_self,
    show e.sign + (θ e.code u + P e.code) = e.sign + P e.code + θ e.code u by ring]

theorem qmatR_congr {R : Type*} [CommRing R] {s t : ZMod 2} {a b : C} {δ ε : Cocode}
    (h₁ : s = t) (h₂ : a = b) (h₃ : δ = ε) : qmatR R s a δ = qmatR R t b ε := by
  rw [h₁, h₂, h₃]

theorem Tmat_mul_Tmat (a b : C) : Tmat a * Tmat b = Tmat (a + b) := by
  rw [Tmat_eq_qmatR, Tmat_eq_qmatR, Tmat_eq_qmatR, qmatR_mul]
  exact qmatR_congr (by simp) rfl (by simp)

theorem Dmat_mul_Dmat (δ ε : Cocode) : Dmat δ * Dmat ε = Dmat (δ + ε) := by
  rw [Dmat_eq_qmatR, Dmat_eq_qmatR, Dmat_eq_qmatR, qmatR_mul]
  exact qmatR_congr (by simp) (by simp) rfl

theorem Dmat_mul_Tmat (δ : Cocode) (a : C) :
    Dmat δ * Tmat a = zmat ^ (pair a δ).val * (Tmat a * Dmat δ) := by
  rw [Dmat_eq_qmatR, Tmat_eq_qmatR, qmatR_mul, qmatR_mul, zmat_pow_mul_qmatR]
  exact qmatR_congr (by simp) (by simp) (by simp)

theorem Xmat_eq_zmat_pow_mul (a : C) (s : ZMod 2) :
    Xmat ⟨a, s⟩ = zmat ^ s.val * Tmat a * Dmat (thetaD a) := by
  rw [zmat_pow_mul_Tmat_mul_Dmat, Xmat_eq_qmatR]

theorem Xmat_mul_Xmat (e f : Parker) :
    Xmat e * Xmat f = Xmat (e * f) * Dmat (Acocode e.code f.code) := by
  rw [Xmat_eq_qmatR, Xmat_eq_qmatR, Xmat_eq_qmatR, Dmat_eq_qmatR, qmatR_mul, qmatR_mul,
    Parker.mul_code, Parker.mul_sign, pair_thetaD, pair_zero_left, thetaD_add,
    add_assoc (thetaD e.code + thetaD f.code), add_self_cocode]
  simp only [add_zero]

theorem Xmat_mul_self (e : Parker) : Xmat e * Xmat e = zmat ^ (P e.code).val := by
  rw [Xmat_eq_qmatR, qmatR_mul, zmat_pow_eq_qmatR, pair_self_thetaD, add_self_C',
    add_self_cocode, zmod2_add_self, zero_add]

theorem Xmat_mul_Dmat (e : Parker) (δ : Cocode) :
    Xmat e * Dmat δ = zmat ^ (pair e.code δ).val * (Dmat δ * Xmat e) := by
  rw [Xmat_eq_qmatR, Dmat_eq_qmatR, qmatR_mul, qmatR_mul, zmat_pow_mul_qmatR]
  refine qmatR_congr ?_ (by simp) (add_comm _ _)
  simp only [pair_zero_left, add_zero, zero_add]
  linear_combination (-pair e.code δ) * two_eq_zero'

theorem spin_Fourier_Pauli_identities :
    (∀ (c : C₀) (k : ZMod 2), Fvec ((c : C) + k • ΩC) = E 0 c + sgn k • E 1 c) ∧
    (∀ u v : C, Fvec u ⬝ᵥ Fvec v = if u = v then 2 else 0) ∧
    LinearIndependent ℚ Fvec ∧ Submodule.span ℚ (Set.range Fvec) = ⊤ ∧
    (∀ c : C₀, E 0 c = (1 / 2 : ℚ) • (Fvec (c : C) + Fvec ((c : C) + ΩC)) ∧
      E 1 c = (1 / 2 : ℚ) • (Fvec (c : C) - Fvec ((c : C) + ΩC))) ∧
    (∀ (u : C) (e : Parker),
      Fvec u ᵥ* Xmat e = sgn (e.sign + P e.code + θ e.code u) • Fvec (u + e.code)) ∧
    (∀ (u : C) (δ : Cocode), Fvec u ᵥ* Dmat δ = sgn (pair u δ) • Fvec u) ∧
    (∀ u a : C, Fvec u ᵥ* Tmat a = Fvec (u + a)) ∧
    (∀ a b : C, Tmat a * Tmat b = Tmat (a + b)) ∧
    (∀ δ ε : Cocode, Dmat δ * Dmat ε = Dmat (δ + ε)) ∧
    (∀ (δ : Cocode) (a : C), Dmat δ * Tmat a = zmat ^ (pair a δ).val * (Tmat a * Dmat δ)) ∧
    (∀ (a : C) (s : ZMod 2), Xmat ⟨a, s⟩ = zmat ^ s.val * Tmat a * Dmat (thetaD a)) ∧
    (∀ e f : Parker, Xmat e * Xmat f = Xmat (e * f) * Dmat (Acocode e.code f.code) ∧
      ∀ u : C, pair u (Acocode e.code f.code) = A e.code f.code u) ∧
    (∀ e : Parker, Xmat e * Xmat e = zmat ^ (P e.code).val) ∧
    (∀ (e : Parker) (δ : Cocode),
      Xmat e * Dmat δ = zmat ^ (pair e.code δ).val * (Dmat δ * Xmat e)) := by
  refine ⟨Fvec_add_smul_ΩC, Fvec_dotProduct_Fvec, linearIndependent_Fvec, ?_,
    fun c => ⟨E_zero_eq c, E_one_eq c⟩, Fvec_vecMul_Xmat, Fvec_vecMul_Dmat, Fvec_vecMul_Tmat,
    Tmat_mul_Tmat, Dmat_mul_Dmat, Dmat_mul_Tmat, Xmat_eq_zmat_pow_mul,
    fun e f => ⟨Xmat_mul_Xmat e f, fun u => pair_Acocode _ _ u⟩, Xmat_mul_self, Xmat_mul_Dmat⟩
  rw [← coe_Fbasis]
  exact Fbasis.span_eq

end CFSG.Monster.Spin
