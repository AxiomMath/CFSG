module

public import CFSG.Quasithin.Background.F918Z3Cg2Par
public import CFSG.Quasithin.Background.F918Z3Cg2Fix

public section

namespace CFSG.Quasithin

open scoped Matrix

namespace Z3Cg2

theorem card_fixV_conj {V : Type} [CommGroup V] (s y : MulAut V) :
    Nat.card ↥(fixV (Subgroup.zpowers (s * y * s⁻¹))) = Nat.card ↥(fixV (Subgroup.zpowers y)) :=
  card_fixV_zpowers_conj s y

section Model

variable {V : Type} [CommGroup V] [Finite V] {D X G T' : Subgroup (MulAut V)} {s : MulAut V}
  {F : Type} [Field F] [Finite F] [CharP F 2] {d : ℕ}
  {β : V ≃* Multiplicative (Matrix (Fin d) (Fin d) F)}
  {ρ : ↥D →* Matrix.GeneralLinearGroup (Fin d) F}
  {σ : ↥X →* Matrix.GeneralLinearGroup (Fin d) F}

omit [Finite V] in
theorem card_fixV_sq_of_left (hM : IsMatModel D X β ρ σ) {I : Subgroup V} (hI0 : I ≠ ⊥)
    (hIinv : ∀ y ∈ D, ∀ v ∈ I, y v ∈ I)
    (hImin : ∀ U ≤ I, (∀ y ∈ D, ∀ v ∈ U, y v ∈ U) → U = ⊥ ∨ U = I) {a : ℕ}
    (hO : OrthMinusData D I a) {y x : MulAut V} (hy : y ∈ D) (hx : x ∈ X) (hy1 : y ≠ 1)
    (hyy : y * y = 1) (hxx : x * x = 1) :
    Nat.card ↥(fixV (Subgroup.zpowers (y * x))) ^ 2 = Nat.card V := by
  have hP := rho_mul_self (ρ := ρ) hy hyy
  have hQ := sigma_mul_self (σ := σ) hx hxx
  have hfree := hO.free y hy hy1 hyy
  rw [Z3D.card_inf_fixV_zpowers_of_mem hM hI0 hIinv hImin hy,
    Z3D.card_eq_pow hM hI0 hIinv hImin] at hfree
  obtain ⟨S, hS⟩ := exists_split_of_free hP hfree
  have hcard := card_fixed_of_split hP hQ hS
  rw [card_fixV_zpowers_eq β (y * x) (fun M => (ρ ⟨y, hy⟩ : Matrix (Fin d) (Fin d) F) * M *
    ((σ ⟨x, hx⟩ : Matrix (Fin d) (Fin d) F))ᵀ) (toAdd_mul_apply hM hy hx), hcard, card_V_eq β]

theorem card_fixV_sq_of_mem_sup (hZ : Z37 D X G T' s) (hM : IsMatModel D X β ρ σ)
    {I : Subgroup V} (hI0 : I ≠ ⊥) (hIinv : ∀ y ∈ D, ∀ v ∈ I, y v ∈ I)
    (hImin : ∀ U ≤ I, (∀ y ∈ D, ∀ v ∈ U, y v ∈ U) → U = ⊥ ∨ U = I) {a : ℕ}
    (hO : OrthMinusData D I a) {j : MulAut V} (hj : j ∈ D ⊔ X) (hj1 : j ≠ 1) (hjj : j * j = 1) :
    Nat.card ↥(fixV (Subgroup.zpowers j)) ^ 2 = Nat.card V := by
  obtain ⟨y, hy, x, hx, rfl⟩ := exists_mul_of_mem_sup hZ.comm hj
  obtain ⟨hyy, hxx⟩ := sq_eq_one_of_mul_eq_one hZ hy hx hjj
  by_cases hy1 : y = 1
  · subst hy1
    rw [one_mul] at hj1 ⊢
    have hx' : x ∈ D.map (MulAut.conj s).toMonoidHom := by
      rw [← hZ.swapDX]
      exact hx
    obtain ⟨y', hy', hy'x⟩ := hx'
    have hxe : x = s * y' * s⁻¹ := hy'x.symm
    subst hxe
    have hy'1 : y' ≠ 1 := by
      rintro rfl
      apply hj1
      simp
    have hy'y' : y' * y' = 1 := by
      calc y' * y' = s⁻¹ * (s * y' * s⁻¹ * (s * y' * s⁻¹)) * s := by group
        _ = 1 := by rw [hxx]; group
    have h := card_fixV_sq_of_left hM hI0 hIinv hImin hO hy' X.one_mem hy'1 hy'y' (mul_one 1)
    rw [mul_one] at h
    rw [card_fixV_conj]
    exact h
  · exact card_fixV_sq_of_left hM hI0 hIinv hImin hO hy hx hy1 hyy hxx

end Model

section Distinct

variable {F : Type} [Field F] [CharP F 2] {d : ℕ}

omit [CharP F 2] in
theorem exists_single_ne {A : Matrix (Fin d) (Fin d) F} (hA : A ≠ 1) :
    ∃ i, A *ᵥ Pi.single i 1 ≠ Pi.single i 1 := by
  by_contra h
  push Not at h
  apply hA
  apply Matrix.ext_of_mulVec_single
  intro i
  rw [h i, Matrix.one_mulVec]

theorem exists_fixed_left_not_fixed_right {P Q : Matrix (Fin d) (Fin d) F} (hP : P * P = 1)
    (hP1 : P ≠ 1) (hQ1 : Q ≠ 1) : ∃ M : Matrix (Fin d) (Fin d) F, P * M = M ∧ M * Qᵀ ≠ M := by
  obtain ⟨i, hi⟩ := exists_single_ne hP1
  obtain ⟨k, hk⟩ := exists_single_ne hQ1
  set y : Fin d → F := Pi.single i 1 with hy
  set w : Fin d → F := P *ᵥ y + y with hw
  have hw0 : w ≠ 0 := by
    intro h
    apply hi
    have h' := eq_neg_of_add_eq_zero_left h
    rw [h', InvolMat.neg_eq_self F]
  have hPw : P *ᵥ w = w := by
    simp only [hw, Matrix.mulVec_add, Matrix.mulVec_mulVec, hP, Matrix.one_mulVec]
    rw [add_comm]
  refine ⟨Matrix.vecMulVec w (Pi.single k 1), ?_, ?_⟩
  · rw [Matrix.mul_vecMulVec, hPw]
  · intro h
    rw [Matrix.vecMulVec_mul, Matrix.vecMul_transpose] at h
    obtain ⟨l, hl⟩ : ∃ l, w l ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hw0 (funext hcon)
    apply hk
    funext m
    have h2 := congrFun (congrFun h l) m
    simp only [Matrix.vecMulVec_apply] at h2
    exact mul_left_cancel₀ hl h2

variable {V : Type} [CommGroup V] {D X : Subgroup (MulAut V)}
  {β : V ≃* Multiplicative (Matrix (Fin d) (Fin d) F)}
  {ρ : ↥D →* Matrix.GeneralLinearGroup (Fin d) F}
  {σ : ↥X →* Matrix.GeneralLinearGroup (Fin d) F}

theorem fixV_ne_of_model (hM : IsMatModel D X β ρ σ) {y x : MulAut V} (hy : y ∈ D) (hx : x ∈ X)
    (hy1 : y ≠ 1) (hyy : y * y = 1) (hx1 : x ≠ 1) :
    fixV (Subgroup.zpowers y) ≠ fixV (Subgroup.zpowers x) := by
  have hP := rho_mul_self (ρ := ρ) hy hyy
  have hP1 : (ρ ⟨y, hy⟩ : Matrix (Fin d) (Fin d) F) ≠ 1 := fun h =>
    hy1 (eq_one_of_rho_eq_one hM hy h)
  have hQ1 : (σ ⟨x, hx⟩ : Matrix (Fin d) (Fin d) F) ≠ 1 := fun h =>
    hx1 (eq_one_of_sigma_eq_one hM hx h)
  obtain ⟨M, hM1, hM2⟩ := exists_fixed_left_not_fixed_right hP hP1 hQ1
  intro heq
  set v : V := β.symm (Multiplicative.ofAdd M) with hv'
  have hv : Multiplicative.toAdd (β v) = M := by simp [hv']
  have h1 : v ∈ fixV (Subgroup.zpowers y) := by
    rw [Z3D.mem_fixV_zpowers_iff]
    apply β.injective
    apply Multiplicative.toAdd.injective
    rw [toAdd_left_apply hM hy, hv, hM1]
  have h2 : v ∈ fixV (Subgroup.zpowers x) := heq ▸ h1
  rw [Z3D.mem_fixV_zpowers_iff] at h2
  apply hM2
  have h3 := congrArg (fun u => Multiplicative.toAdd (β u)) h2
  simp only [toAdd_right_apply hM hx, hv] at h3
  exact h3

end Distinct

end Z3Cg2

end CFSG.Quasithin
