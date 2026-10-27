module

public import CFSG.Quasithin.Vol2.Ch10SecI1CovM
public import CFSG.Quasithin.Background.B4ModelsAction

public section

noncomputable section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.ASInputs.C10KH

open CFSG.Quasithin CFSG.Quasithin.JonesParshall CFSG.Assembly.LowTwoRank Matrix

theorem exists_addHom_one (K : Type) [Field K] [CharP K 2] : ∃ ℓ : K →+ ZMod 2, ℓ 1 = 1 := by
  have h2 : ∀ x : K, 2 • x = 0 := fun x => by rw [two_nsmul, CharTwo.add_self_eq_zero]
  let _ : Module (ZMod 2) K := AddCommGroup.zmodModule h2
  have h : ¬ ∀ φ : Module.Dual (ZMod 2) K, φ 1 = 0 := fun h =>
    one_ne_zero ((Module.forall_dual_apply_eq_zero_iff (ZMod 2) (1 : K)).mp h)
  push Not at h
  obtain ⟨φ, hφ⟩ := h
  refine ⟨φ.toAddMonoidHom, ?_⟩
  change φ 1 = 1
  revert hφ
  generalize φ 1 = u
  revert u
  decide

theorem sq_eq_one_of_charTwo {K : Type} [Field K] [CharP K 2] {A : Type} [AddCommGroup A]
    [Module K A] (x : Multiplicative A) : x ^ 2 = 1 := by
  apply Multiplicative.toAdd.injective
  rw [toAdd_pow, toAdd_one, two_nsmul, ← two_smul K, CharTwo.two_eq_zero, zero_smul]

theorem sec_sq_eq_one {D : FFModel} (h : ∀ x : D.Amb, x ^ 2 = 1) (x : D.Sec) : x ^ 2 = 1 := by
  induction x using QuotientGroup.induction_on with | H m => ?_
  rw [← QuotientGroup.mk_pow]
  have : m ^ 2 = 1 := Subtype.ext (by rw [Subgroup.coe_pow, h, Subgroup.coe_one])
  rw [this, QuotientGroup.mk_one]

section Nat

variable {ι : Type} [Fintype ι] {K : Type} [Field K]

@[expose] def matPair (ℓ : K →+ ZMod 2) (J : Matrix ι ι K) (x y : Multiplicative (ι → K)) :
    ZMod 2 :=
  ℓ (Multiplicative.toAdd x ⬝ᵥ (J *ᵥ Multiplicative.toAdd y))

theorem matPair_mul_left (ℓ : K →+ ZMod 2) (J : Matrix ι ι K) (x y z : Multiplicative (ι → K)) :
    matPair ℓ J (x * y) z = matPair ℓ J x z + matPair ℓ J y z := by
  simp only [matPair, toAdd_mul, add_dotProduct, map_add]

theorem matPair_mul_right (ℓ : K →+ ZMod 2) (J : Matrix ι ι K) (x y z : Multiplicative (ι → K)) :
    matPair ℓ J x (y * z) = matPair ℓ J x y + matPair ℓ J x z := by
  simp only [matPair, toAdd_mul, mulVec_add, dotProduct_add, map_add]

theorem matPair_one_left (ℓ : K →+ ZMod 2) (J : Matrix ι ι K) (y : Multiplicative (ι → K)) :
    matPair ℓ J 1 y = 0 := by
  simp only [matPair, toAdd_one, zero_dotProduct, map_zero]

theorem matPair_one_right (ℓ : K →+ ZMod 2) (J : Matrix ι ι K) (x : Multiplicative (ι → K)) :
    matPair ℓ J x 1 = 0 := by
  simp only [matPair, toAdd_one, mulVec_zero, dotProduct_zero, map_zero]

variable [DecidableEq ι]

theorem matPair_secPairing (ℓ : K →+ ZMod 2) (J : Matrix ι ι K) (Γ : Subgroup (GL ι K)) :
    SecPairing (FFModel.nat Γ) (matPair ℓ J) where
  add_left := matPair_mul_left ℓ J
  add_right := matPair_mul_right ℓ J
  ker_left k hk y _ := by
    have hk1 : k = 1 := hk
    rw [hk1]
    exact matPair_one_left ℓ J y
  ker_right x _ k hk := by
    have hk1 : k = 1 := hk
    rw [hk1]
    exact matPair_one_right ℓ J x

theorem matPair_nondeg {ℓ : K →+ ZMod 2} (hℓ : ℓ 1 = 1) {J : Matrix ι ι K} (hJ : J * J = 1)
    {x : Multiplicative (ι → K)} (hx : ∀ y : Multiplicative (ι → K), matPair ℓ J x y = 0) :
    x = 1 := by
  set v := Multiplicative.toAdd x with hv
  have h0 : ∀ w : ι → K, v ⬝ᵥ (J *ᵥ w) = 0 := by
    intro w
    by_contra hp
    have h1 := hx (Multiplicative.ofAdd ((v ⬝ᵥ (J *ᵥ w))⁻¹ • w))
    rw [matPair, toAdd_ofAdd, mulVec_smul, dotProduct_smul, smul_eq_mul, inv_mul_cancel₀ hp,
      hℓ] at h1
    exact one_ne_zero h1
  have h1 : v ᵥ* J = 0 := by
    funext i
    have := h0 (Pi.single i 1)
    rwa [dotProduct_mulVec, dotProduct_single, mul_one] at this
  have h2 : v = 0 := by
    rw [← vecMul_one v, ← hJ, ← vecMul_vecMul, h1, zero_vecMul]
  apply Multiplicative.toAdd.injective
  rw [← hv, h2, toAdd_one]

theorem matPair_invariant (ℓ : K →+ ZMod 2) {J : Matrix ι ι K} {Γ : Subgroup (GL ι K)}
    (hΓ : ∀ g ∈ Γ, ((g : GL ι K) : Matrix ι ι K)ᵀ * J * (g : Matrix ι ι K) = J) (g : ↥Γ)
    (x y : Multiplicative (ι → K)) :
    matPair ℓ J (natAct Γ g x) (natAct Γ g y) = matPair ℓ J x y := by
  simp only [matPair, natAct, toAdd_ofAdd]
  congr 1
  set G := ((g : GL ι K) : Matrix ι ι K)
  rw [← vecMul_transpose, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, hΓ g g.2]

end Nat

section NatCover

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K] [Finite K] [CharP K 2]
  {W : Type} [CommGroup W] [Finite W]

theorem natCover_card_le (hW2 : ∀ w : W, w ^ 2 = 1) {Gm : Subgroup (MulAut W)} {Z : Subgroup W}
    (hZ : Z ≤ fixV Gm) (hcomm : commV Gm = ⊤) {Γ : Subgroup (GL ι K)}
    (hR : (FFModel.nat Γ).Realizes Gm ⊤ Z) {J : Matrix ι ι K} (hJ : J * J = 1)
    (hΓ : ∀ g ∈ Γ, ((g : GL ι K) : Matrix ι ι K)ᵀ * J * (g : Matrix ι ι K) = J) {d : ℕ}
    (hH1 : ∀ {M : Type} [AddCommGroup M] [Module (ZMod 2) M] [Finite M]
      (ρ : Representation (ZMod 2) (FFModel.nat Γ).Gam M), (FFModel.nat Γ).IsModel ρ →
        Module.finrank (ZMod 2) (H1 ρ) ≤ d) :
    Nat.card Z ≤ 2 ^ d := by
  obtain ⟨ℓ, hℓ⟩ := exists_addHom_one K
  have : Finite (FFModel.nat Γ).Gam := inferInstanceAs (Finite ↥Γ)
  exact cover_card_le_of_form hW2 hZ hcomm hR (FFModel.nat_isActionModel Γ)
    (sec_sq_eq_one fun x => sq_eq_one_of_charTwo (K := K) (A := ι → K) x)
    (matPair_secPairing ℓ J Γ)
    (fun x _ hx => Subgroup.mem_bot.mpr (matPair_nondeg hℓ hJ fun y => hx y (Subgroup.mem_top y)))
    (fun γ x _ y _ => matPair_invariant ℓ hΓ γ x y) hH1

end NatCover

section SL2

variable {K : Type} [Field K]

@[expose] def jTwo (K : Type) [Field K] : Matrix (Fin 2) (Fin 2) K := !![0, 1; 1, 0]

theorem jTwo_mul_self : jTwo K * jTwo K = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [jTwo, Matrix.mul_apply, Fin.sum_univ_two]

theorem transpose_jTwo_mul [CharP K 2] (g : Matrix (Fin 2) (Fin 2) K) :
    gᵀ * jTwo K * g = g.det • jTwo K := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [jTwo, Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two]
  · linear_combination g 1 0 * g 0 0 * h2
  · linear_combination g 0 1 * g 1 0 * h2
  · linear_combination g 0 1 * g 1 0 * h2
  · linear_combination g 1 1 * g 0 1 * h2

theorem det_of_mem_statedSL {n : ℕ} {g : GL (Fin n) K} (hg : g ∈ StatedSL n K) :
    (g : Matrix (Fin n) (Fin n) K).det = 1 :=
  CFSG.Open.StatedAPI.det_of_mem_statedSL hg

variable [Finite K] [CharP K 2] {W : Type} [CommGroup W] [Finite W]

theorem sl2Cover_card_le (hW2 : ∀ w : W, w ^ 2 = 1) {Gm : Subgroup (MulAut W)} {Z : Subgroup W}
    (hZ : Z ≤ fixV Gm) (hcomm : commV Gm = ⊤) (hR : (FFModel.nat (StatedSL 2 K)).Realizes Gm ⊤ Z)
    {d : ℕ} (hH1 : ∀ {M : Type} [AddCommGroup M] [Module (ZMod 2) M] [Finite M]
      (ρ : Representation (ZMod 2) (FFModel.nat (StatedSL 2 K)).Gam M),
        (FFModel.nat (StatedSL 2 K)).IsModel ρ → Module.finrank (ZMod 2) (H1 ρ) ≤ d) :
    Nat.card Z ≤ 2 ^ d :=
  natCover_card_le hW2 hZ hcomm hR jTwo_mul_self
    (fun g hg => by rw [transpose_jTwo_mul, det_of_mem_statedSL hg, one_smul]) hH1

end SL2

section Sp4

variable {K : Type} [Field K]

theorem spJ_mul_self : Explicit.spJ K * Explicit.spJ K = 1 := by
  simp [Explicit.spJ, Matrix.fromBlocks_multiply, Matrix.fromBlocks_one]

variable [Finite K] [CharP K 2] {W : Type} [CommGroup W] [Finite W]

theorem sp4Cover_card_le (hW2 : ∀ w : W, w ^ 2 = 1) {Gm : Subgroup (MulAut W)} {Z : Subgroup W}
    (hZ : Z ≤ fixV Gm) (hcomm : commV Gm = ⊤) (hR : (FFModel.nat (StatedSp 2 K)).Realizes Gm ⊤ Z)
    {d : ℕ} (hH1 : ∀ {M : Type} [AddCommGroup M] [Module (ZMod 2) M] [Finite M]
      (ρ : Representation (ZMod 2) (FFModel.nat (StatedSp 2 K)).Gam M),
        (FFModel.nat (StatedSp 2 K)).IsModel ρ → Module.finrank (ZMod 2) (H1 ρ) ≤ d) :
    Nat.card Z ≤ 2 ^ d :=
  natCover_card_le hW2 hZ hcomm hR spJ_mul_self
    (fun g hg => by
      rw [← Explicit.sp4_eq_statedSp K] at hg
      exact hg) hH1

end Sp4

end CFSG.Quasithin.ASInputs.C10KH
