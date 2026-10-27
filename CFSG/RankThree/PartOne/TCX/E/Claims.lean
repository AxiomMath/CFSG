module

public import CFSG.RankThree.PartOne.TCX.E.Engine
public import CFSG.RankThree.PartOne.KLCE.TypeSU
public import CFSG.LieType.Universal.Unitary.Clause0
public import CFSG.RankThree.PartOne.KLCE.TypeSL

public section

namespace CFSG.RankThree.PartOne.TCX.E

open Subgroup Matrix CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.RankThree.PartOne
open CFSG.RankThree.PartOne.KLCE

section Abstract

@[expose] def LayerClaims2 (p : ℕ) {G : Type} [Group G] (α : MulAut G) (Q : Subgroup G) : Prop :=
  (∀ g ∈ Q, α g ∈ Q) ∧ (∀ e ∈ Q, ¬ ∀ g ∈ Q, α g = e * g * e⁻¹) ∧
    (∃ (t' : StatedLieTag) (n' f'' : ℕ), 1 ≤ f'' ∧
      LieModel (↥Q ⧸ Subgroup.center ↥Q) t' n' 2 (p * f'')) ∧
    ∃ t₁ ∈ Q, α t₁ = t₁ ∧ ∃ t₂ ∈ Q, α t₂ = t₂ ∧ (∃ k : ℕ, orderOf t₁ = 2 ^ k) ∧
      (∃ k : ℕ, orderOf t₂ = 2 ^ k) ∧ t₁ * t₂ ≠ t₂ * t₁

theorem layerDatum2_of_model {p : ℕ} {M : Type} [Group M] (F₀ : M → M) {D : Type} [Group D]
    (ρ' : D →* M) (τ' : D →* D) (hρ' : Function.Injective ρ')
    (hcompat : ∀ d, F₀ (ρ' d) = ρ' (τ' d))
    (hclaims : ∀ {G : Type} [Group G] (α : MulAut G) (φ : D →* G), Function.Injective φ →
      (∀ d, α (φ d) = φ (τ' d)) → ∀ Q : Subgroup G, φ.range = Q → LayerClaims2 p α Q) :
    LayerDatum2 p F₀ ρ'.range := by
  intro G _ _ ψ hψ hPψ α _ hψα _
  obtain ⟨φ, hφinj, hψφ, hφrange⟩ := exists_hom_of_push ψ hψ ρ' hρ' hPψ
  have hαφ : ∀ d, α (φ d) = φ (τ' d) := fun d => by
    apply hψ
    rw [hψα, hψφ, hcompat, hψφ]
  obtain ⟨-, hout, hmodel, hfix⟩ := hclaims α φ hφinj hαφ _ hφrange
  exact ⟨hout, hmodel, hfix⟩

theorem not_inner_of_class {G D R : Type} [Group G] [Group D] (φ : D →* G)
    (hφ : Function.Injective φ) (α : MulAut G) (τ' : D →* D) (hαφ : ∀ d, α (φ d) = φ (τ' d))
    (χ : D → R) (hχ : ∀ E d : D, χ (E * d * E⁻¹) = χ d) (d : D) (hd : χ (τ' d) ≠ χ d) :
    ∀ e ∈ φ.range, ¬ ∀ g ∈ φ.range, α g = e * g * e⁻¹ := by
  rintro _ ⟨E, rfl⟩ hall
  have h := hall (φ d) ⟨d, rfl⟩
  rw [hαφ, ← map_inv, ← map_mul, ← map_mul] at h
  have h2 : τ' d = E * d * E⁻¹ := hφ h
  exact hd (by rw [h2, hχ])

end Abstract

section Trace

variable {n : ℕ} {K : Type} [Field K]

theorem trace_conj_units (u : GL (Fin n) K) (M : Matrix (Fin n) (Fin n) K) :
    Matrix.trace ((u : Matrix (Fin n) (Fin n) K) * M * ((u⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) =
      Matrix.trace M := by
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]

end Trace

section SL

variable {m : ℕ} {K' : Type} [Field K']

theorem trace_transvection_pair {i j : Fin (m + 2)} (hij : i ≠ j) (a b : K') :
    Matrix.trace (((SpecialLinearGroup.transvection hij a *
        SpecialLinearGroup.transvection hij.symm b : SpecialLinearGroup (Fin (m + 2)) K') :
        Matrix (Fin (m + 2)) (Fin (m + 2)) K')) = ((m + 2 : ℕ) : K') + a * b := by
  rw [Matrix.SpecialLinearGroup.coe_mul, SpecialLinearGroup.transvection_coe,
    SpecialLinearGroup.transvection_coe, mul_add, add_mul, add_mul, Matrix.one_mul,
    Matrix.mul_one, Matrix.single_mul_single_same]
  simp [Matrix.trace_add, Matrix.trace_one, Matrix.trace_single_eq_of_ne _ _ _ hij,
    Matrix.trace_single_eq_of_ne _ _ _ hij.symm, Matrix.trace_single_eq_same]

theorem sl_claims2 {p f' : ℕ} (hp5 : 5 ≤ p) (hf' : 1 ≤ f') [Finite K'] [CharP K' 2]
    (hK' : Nat.card K' = 2 ^ (p * f')) {σ' : K' ≃+* K'} (hσ' : σ' ≠ 1) {G : Type} [Group G]
    (α : MulAut G) (φ : SpecialLinearGroup (Fin (m + 2)) K' →* G) (hφ : Function.Injective φ)
    (hαφ : ∀ B, α (φ B) = φ (SpecialLinearGroup.map σ'.toRingHom B)) (Q : Subgroup G)
    (hQ : φ.range = Q) : LayerClaims2 p α Q := by
  obtain ⟨hstab, -, -, hmodel, hfix⟩ := sl_type_claims hp5 hf' hK' hσ' α φ hφ hαφ Q hQ
  refine ⟨hstab, ?_, hmodel, hfix⟩
  subst hQ
  have h01 : (0 : Fin (m + 2)) ≠ 1 := by simp
  obtain ⟨a, ha⟩ : ∃ a, σ' a ≠ a := by
    by_contra h
    exact hσ' (RingEquiv.ext fun a => by_contra fun hne => h ⟨a, hne⟩)
  refine not_inner_of_class φ hφ α (SpecialLinearGroup.map σ'.toRingHom) hαφ
    (fun d => Matrix.trace (d : Matrix (Fin (m + 2)) (Fin (m + 2)) K')) (fun E d => ?_)
    (SpecialLinearGroup.transvection h01 a * SpecialLinearGroup.transvection h01.symm 1) ?_
  · show Matrix.trace ((E * d * E⁻¹ : SpecialLinearGroup (Fin (m + 2)) K') :
      Matrix (Fin (m + 2)) (Fin (m + 2)) K') =
      Matrix.trace (d : Matrix (Fin (m + 2)) (Fin (m + 2)) K')
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul,
      inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mul]
  · simp only [map_mul, map_transvection]
    rw [trace_transvection_pair h01, trace_transvection_pair h01]
    simp only [map_one, mul_one]
    intro h
    exact ha (add_left_cancel h)

end SL

section SU

variable {m : ℕ} {K : Type} [Field K] {g : ℕ}

theorem mem_statedSU_iff_n [Finite K] {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ g) ^ 2)
    (A : GL (Fin n) K) : A ∈ StatedSU n (2 ^ g) K ↔ (A : Matrix (Fin n) (Fin n) K).det = 1 ∧
      ((A : Matrix (Fin n) (Fin n) K).map (· ^ 2 ^ g))ᵀ * (A : Matrix (Fin n) (Fin n) K) = 1 := by
  have h := (CFSG.LinearGroups.unitary_scalar_kernel Nat.prime_two hK (n := n) hn).1
  have := Set.ext_iff.1 h A
  simpa using this

@[expose] noncomputable def permGLn [CharP K 2] {n : ℕ} (σ : Equiv.Perm (Fin n)) : GL (Fin n) K :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (σ.permMatrix K) (by
    rw [Matrix.det_permutation]
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h])

omit [Field K] in
theorem coe_permGLn [Field K] [CharP K 2] {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    ((permGLn σ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = σ.permMatrix K := rfl

theorem map_pow_permMatrix_n {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    (σ.permMatrix K).map (· ^ 2 ^ g) = σ.permMatrix K := by
  ext i j
  simp only [Matrix.map_apply, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply,
    Equiv.toPEquiv_apply]
  split_ifs <;> simp [zero_pow (pow_ne_zero g (two_ne_zero))]

theorem permGLn_mem [Finite K] [CharP K 2] {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ g) ^ 2)
    (σ : Equiv.Perm (Fin n)) : permGLn σ ∈ StatedSU n (2 ^ g) K := by
  rw [mem_statedSU_iff_n hn hK, coe_permGLn, map_pow_permMatrix_n, Matrix.transpose_permMatrix,
    ← Matrix.permMatrix_mul, mul_inv_cancel, Matrix.permMatrix_one, Matrix.det_permutation]
  refine ⟨?_, rfl⟩
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
  · simp [h]
  · simpa [h] using CharTwo.neg_eq (1 : K)

@[expose] def dvec (l : K) (i : Fin (m + 3)) : K := if i = 0 then l else if i = 1 then l⁻¹ else 1

theorem prod_dvec (l : K) (hl : l ≠ 0) : ∏ i : Fin (m + 3), dvec l i = 1 := by
  have h : ∀ i : Fin (m + 1), dvec l i.succ.succ = 1 := fun i => by
    simp [dvec, Fin.succ_ne_zero, Fin.succ_succ_ne_one]
  rw [Fin.prod_univ_succ, Fin.prod_univ_succ, Finset.prod_congr rfl (fun i _ => h i)]
  simp [dvec, hl]

theorem sum_dvec (l : K) : ∑ i : Fin (m + 3), dvec l i = l + l⁻¹ + ((m + 1 : ℕ) : K) := by
  have h : ∀ i : Fin (m + 1), dvec l i.succ.succ = 1 := fun i => by
    simp [dvec, Fin.succ_ne_zero, Fin.succ_succ_ne_one]
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Finset.sum_congr rfl (fun i _ => h i)]
  simp [dvec, add_assoc]

@[expose] noncomputable def diagSU (l : Kˣ) : GL (Fin (m + 3)) K :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.diagonal (dvec (l : K))) (by
    rw [Matrix.det_diagonal, prod_dvec _ l.ne_zero]
    exact one_ne_zero)

theorem coe_diagSU (l : Kˣ) :
    ((diagSU l : GL (Fin (m + 3)) K) : Matrix (Fin (m + 3)) (Fin (m + 3)) K) =
      Matrix.diagonal (dvec (l : K)) := rfl

theorem diagSU_mem [Finite K] (hK : Nat.card K = (2 ^ g) ^ 2) (l : Kˣ)
    (hl : l ^ (2 ^ g + 1) = 1) : (diagSU l : GL (Fin (m + 3)) K) ∈ StatedSU (m + 3) (2 ^ g) K := by
  have hl' : (l : K) ^ (2 ^ g + 1) = 1 := by
    have := congrArg (fun u : Kˣ => (u : K)) hl
    simpa using this
  rw [mem_statedSU_iff_n (by omega) hK, coe_diagSU, Matrix.det_diagonal,
    prod_dvec _ l.ne_zero]
  refine ⟨rfl, ?_⟩
  rw [Matrix.diagonal_map (by simp [zero_pow (pow_ne_zero g two_ne_zero)]),
    Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  have h0 : (l : K) ≠ 0 := l.ne_zero
  by_cases hi0 : i = 0
  · subst hi0
    simpa [dvec, ← pow_succ] using hl'
  · by_cases hi1 : i = 1
    · subst hi1
      simp only [dvec, hi0, ite_false, ite_true]
      rw [inv_pow, ← mul_inv, ← pow_succ, hl', inv_one]
    · simp [dvec, hi0, hi1]

end SU

section PermHelpers

variable {K : Type} [Field K] {n : ℕ}

theorem permMatrix_injective_n :
    Function.Injective (fun σ : Equiv.Perm (Fin n) => σ.permMatrix K) := fun σ τ h => by
  have h1 : σ.toPEquiv = τ.toPEquiv := PEquiv.toMatrix_injective h
  refine Equiv.ext fun x => ?_
  have := congrArg (fun e : Fin n ≃. Fin n => e x) h1
  simpa [Equiv.toPEquiv_apply] using this

theorem swap_ne_one_n {a b : Fin n} (hab : a ≠ b) : Equiv.swap a b ≠ 1 := fun h => by
  have := congrArg (fun f : Equiv.Perm (Fin n) => f a) h
  simp only [Equiv.swap_apply_left, Equiv.Perm.coe_one, id_eq] at this
  exact hab this.symm

theorem swap_swap_noncomm {a b c : Fin n} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    Equiv.swap a b * Equiv.swap b c ≠ Equiv.swap b c * Equiv.swap a b := fun h => by
  have := congrArg (fun f : Equiv.Perm (Fin n) => f a) h
  simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_left,
    Equiv.swap_apply_of_ne_of_ne hab hac] at this
  exact hbc this

end PermHelpers

section SUClaims

variable {m : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]

omit [CharP K 2] in
theorem lieModel_psu_of_range_n {p f' : ℕ} (hp5 : 5 ≤ p) (hf' : 1 ≤ f')
    (hK : Nat.card K = (2 ^ (p * f')) ^ 2) {G : Type} [Group G]
    (φ : ↥(StatedSU (m + 3) (2 ^ (p * f')) K) →* G) (hφ : Function.Injective φ) :
    LieModel (↥φ.range ⧸ Subgroup.center ↥φ.range) .PSU (m + 3) 2 (p * f') := by
  have hg : 1 ≤ p * f' := by nlinarith
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hbig : 2 ^ 5 ≤ 2 ^ (p * f') := Nat.pow_le_pow_right (by norm_num) (by nlinarith)
  have hnq : (m + 3, 2 ^ (p * f')) ≠ (3, 2) := by
    intro h
    simp only [Prod.mk.injEq] at h
    omega
  let e : ↥(StatedSU (m + 3) (2 ^ (p * f')) K) ≃* ↥φ.range := MonoidHom.ofInjective hφ
  let e' : ↥(StatedSU (m + 3) (2 ^ (p * f')) K) ⧸
      Subgroup.center ↥(StatedSU (m + 3) (2 ^ (p * f')) K) ≃*
      ↥φ.range ⧸ Subgroup.center ↥φ.range :=
    QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)
  let e'' : ↥(StatedSU (m + 3) (2 ^ (p * f')) K) ⧸
      Subgroup.center ↥(StatedSU (m + 3) (2 ^ (p * f')) K) ≃*
      StatedProj (StatedSU (m + 3) (2 ^ (p * f')) K) :=
    QuotientGroup.quotientMulEquivOfEq
      (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card (p := 2) (f := p * f') hK
        (by omega) hnq).2
  have hadm : StatedLieAdmissible .PSU (m + 3) 2 (p * f') := ⟨Nat.prime_two, hg, by omega, hnq⟩
  refine Or.inl ⟨by decide, ?_⟩
  exact ⟨hadm, K, inferInstance, inferInstance, hK, ⟨e'.symm.trans e''⟩⟩

theorem su_claims2 {p f' : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hf' : 1 ≤ f')
    (hK : Nat.card K = (2 ^ (p * f')) ^ 2) {σ : K ≃+* K} (hσ : orderOf σ = p) {G : Type}
    [Group G] (α : MulAut G) (φ : ↥(StatedSU (m + 3) (2 ^ (p * f')) K) →* G)
    (hφ : Function.Injective φ)
    (τ : ↥(StatedSU (m + 3) (2 ^ (p * f')) K) →* ↥(StatedSU (m + 3) (2 ^ (p * f')) K))
    (hτ : ∀ A, (((τ A : ↥(StatedSU (m + 3) (2 ^ (p * f')) K)) : GL (Fin (m + 3)) K) :
        Matrix (Fin (m + 3)) (Fin (m + 3)) K) =
      (((A : ↥(StatedSU (m + 3) (2 ^ (p * f')) K)) : GL (Fin (m + 3)) K) :
        Matrix (Fin (m + 3)) (Fin (m + 3)) K).map σ)
    (hαφ : ∀ A, α (φ A) = φ (τ A)) (Q : Subgroup G) (hQ : φ.range = Q) :
    LayerClaims2 p α Q := by
  have hg : 1 ≤ p * f' := by nlinarith
  have hn : 1 ≤ m + 3 := by omega
  have hc : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact p.Prime := ⟨hp⟩
  have hpodd : Odd p := hp.odd_of_ne_two (by omega)
  have hσp : σ ^ p = 1 := by rw [← hσ]; exact pow_orderOf_eq_one σ
  set i₀ : Fin (m + 3) := ⟨0, by omega⟩ with hi₀
  set i₁ : Fin (m + 3) := ⟨1, by omega⟩ with hi₁
  set i₂ : Fin (m + 3) := ⟨2, by omega⟩ with hi₂
  have h01 : i₀ ≠ i₁ := fun h => by simp [hi₀, hi₁] at h
  have h12 : i₁ ≠ i₂ := fun h => by simp [hi₁, hi₂, Fin.ext_iff] at h
  have h02 : i₀ ≠ i₂ := fun h => by simp [hi₀, hi₂, Fin.ext_iff] at h
  set s₁ : ↥(StatedSU (m + 3) (2 ^ (p * f')) K) :=
    ⟨permGLn (Equiv.swap i₀ i₁), permGLn_mem hn hK _⟩ with hs₁
  set s₂ : ↥(StatedSU (m + 3) (2 ^ (p * f')) K) :=
    ⟨permGLn (Equiv.swap i₁ i₂), permGLn_mem hn hK _⟩ with hs₂
  have hτs : ∀ π : Equiv.Perm (Fin (m + 3)), ∀ h : permGLn π ∈ StatedSU (m + 3) (2 ^ (p * f')) K,
      τ ⟨permGLn π, h⟩ = ⟨permGLn π, h⟩ := fun π h => by
    apply Subtype.ext
    apply Units.ext
    rw [hτ]
    change (π.permMatrix K).map σ = π.permMatrix K
    ext i j
    simp only [Matrix.map_apply, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply,
      Equiv.toPEquiv_apply]
    split_ifs <;> simp
  subst hQ
  refine ⟨?_, ?_, ⟨.PSU, m + 3, f', hf', lieModel_psu_of_range_n hp5 hf' hK φ hφ⟩, ?_⟩
  · rintro _ ⟨A, rfl⟩
    exact ⟨τ A, (hαφ A).symm⟩
  ·
    obtain ⟨l, hl, hmove⟩ := exists_normOne_ne_fixed hp hp5 hf' hK hσ
    set A₀ : ↥(StatedSU (m + 3) (2 ^ (p * f')) K) := ⟨diagSU l, diagSU_mem hK l hl⟩ with hA₀
    refine not_inner_of_class φ hφ α τ hαφ
      (fun d => Matrix.trace (((d : ↥(StatedSU (m + 3) (2 ^ (p * f')) K)) : GL (Fin (m + 3)) K) :
        Matrix (Fin (m + 3)) (Fin (m + 3)) K)) (fun E d => ?_) A₀ ?_
    · show Matrix.trace ((((E * d * E⁻¹ : ↥(StatedSU (m + 3) (2 ^ (p * f')) K)) :
        GL (Fin (m + 3)) K)) : Matrix (Fin (m + 3)) (Fin (m + 3)) K) = _
      have := trace_conj_units (E : GL (Fin (m + 3)) K)
        (((d : ↥(StatedSU (m + 3) (2 ^ (p * f')) K)) : GL (Fin (m + 3)) K) :
          Matrix (Fin (m + 3)) (Fin (m + 3)) K)
      rw [← this]
      rfl
    · show Matrix.trace (((τ A₀ : ↥(StatedSU (m + 3) (2 ^ (p * f')) K)) : GL (Fin (m + 3)) K) :
        Matrix (Fin (m + 3)) (Fin (m + 3)) K) ≠ Matrix.trace
          (((A₀ : ↥(StatedSU (m + 3) (2 ^ (p * f')) K)) : GL (Fin (m + 3)) K) :
            Matrix (Fin (m + 3)) (Fin (m + 3)) K)
      rw [hτ, hA₀]
      simp only [coe_diagSU]
      rw [Matrix.diagonal_map (map_zero σ), Matrix.trace_diagonal, Matrix.trace_diagonal]
      have e1 : ∑ i : Fin (m + 3), σ (dvec (l : K) i) =
          σ (l : K) + (σ (l : K))⁻¹ + ((m + 1 : ℕ) : K) := by
        have := congrArg σ (sum_dvec (m := m) (l : K))
        simp only [map_sum] at this
        rw [this]
        simp
      show ∑ i : Fin (m + 3), σ (dvec (l : K) i) ≠ ∑ i : Fin (m + 3), dvec (l : K) i
      rw [e1, sum_dvec]
      intro h
      have h1 : σ (l : K) + (σ (l : K))⁻¹ = (l : K) + (l : K)⁻¹ := add_right_cancel h
      have hl0 : (l : K) ≠ 0 := l.ne_zero
      have hx0 : σ (l : K) ≠ 0 := fun h0 => hl0 (σ.injective (by rw [h0, map_zero]))
      have h2 : (σ (l : K) - l) * (σ (l : K) * l - 1) = 0 := by
        field_simp at h1
        linear_combination h1
      rcases mul_eq_zero.1 h2 with h3 | h3
      · exact hmove (sub_eq_zero.1 h3)
      ·
        have h4 : σ (l : K) = (l : K)⁻¹ := eq_inv_of_mul_eq_one_left (sub_eq_zero.1 h3)
        have h5 : σ^[2] (l : K) = l := by
          change σ (σ (l : K)) = l
          rw [h4, map_inv₀, h4, inv_inv]
        have h6 : ∀ k : ℕ, σ^[2 * k] (l : K) = l := by
          intro k
          induction k with
          | zero => rfl
          | succ k ih =>
            rw [show 2 * (k + 1) = 2 * k + 2 by ring, Function.iterate_add_apply, h5, ih]
        obtain ⟨k, hk⟩ := hpodd
        have h7 : σ^[p] (l : K) = l := by
          rw [← RingAut.coe_pow, hσp]
          rfl
        have h10 : σ (l : K) = l := by
          have h8 := Function.iterate_succ_apply' (⇑σ) (2 * k) (l : K)
          rw [h6 k] at h8
          rw [hk] at h7
          exact h8.symm.trans h7
        exact hmove h10
  · refine ⟨φ s₁, ⟨s₁, rfl⟩, ?_, φ s₂, ⟨s₂, rfl⟩, ?_, ⟨1, ?_⟩, ⟨1, ?_⟩, ?_⟩
    · rw [hαφ, hs₁, hτs]
    · rw [hαφ, hs₂, hτs]
    · rw [orderOf_injective φ hφ, pow_one]
      refine orderOf_eq_prime ?_ ?_
      · apply Subtype.ext
        apply Units.ext
        change ((Equiv.swap i₀ i₁).permMatrix K) ^ 2 = 1
        rw [pow_two, ← Matrix.permMatrix_mul, Equiv.swap_mul_self, Matrix.permMatrix_one]
      · intro h
        have h1 := congrArg (fun u : ↥(StatedSU (m + 3) (2 ^ (p * f')) K) =>
          ((u : GL (Fin (m + 3)) K) : Matrix (Fin (m + 3)) (Fin (m + 3)) K)) h
        change (Equiv.swap i₀ i₁).permMatrix K = 1 at h1
        rw [← Matrix.permMatrix_one (R := K)] at h1
        exact swap_ne_one_n h01 (permMatrix_injective_n h1)
    · rw [orderOf_injective φ hφ, pow_one]
      refine orderOf_eq_prime ?_ ?_
      · apply Subtype.ext
        apply Units.ext
        change ((Equiv.swap i₁ i₂).permMatrix K) ^ 2 = 1
        rw [pow_two, ← Matrix.permMatrix_mul, Equiv.swap_mul_self, Matrix.permMatrix_one]
      · intro h
        have h1 := congrArg (fun u : ↥(StatedSU (m + 3) (2 ^ (p * f')) K) =>
          ((u : GL (Fin (m + 3)) K) : Matrix (Fin (m + 3)) (Fin (m + 3)) K)) h
        change (Equiv.swap i₁ i₂).permMatrix K = 1 at h1
        rw [← Matrix.permMatrix_one (R := K)] at h1
        exact swap_ne_one_n h12 (permMatrix_injective_n h1)
    · intro h
      rw [← map_mul, ← map_mul] at h
      have h' := hφ h
      have h1 := congrArg (fun u : ↥(StatedSU (m + 3) (2 ^ (p * f')) K) =>
        ((u : GL (Fin (m + 3)) K) : Matrix (Fin (m + 3)) (Fin (m + 3)) K)) h'
      change (Equiv.swap i₀ i₁).permMatrix K * (Equiv.swap i₁ i₂).permMatrix K =
        (Equiv.swap i₁ i₂).permMatrix K * (Equiv.swap i₀ i₁).permMatrix K at h1
      rw [← Matrix.permMatrix_mul, ← Matrix.permMatrix_mul] at h1
      exact swap_swap_noncomm h01 h12 h02 (permMatrix_injective_n h1).symm

end SUClaims

end CFSG.RankThree.PartOne.TCX.E
