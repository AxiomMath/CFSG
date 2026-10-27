module

public import CFSG.LinearAlgebra.LinearGroups.UnitaryScalarKernel
public import CFSG.LocalAnalysis.ComponentInitial.FieldFiniteAutomorphism
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Blueprint.Catalog

public section

namespace CFSG.RankThree.PartOne.KLCE

open Subgroup Matrix CFSG.Blueprint CFSG.Assembly.LowTwoRank

section Elements

variable {K : Type} [Field K] [CharP K 2]

@[expose] noncomputable def permGL (σ : Equiv.Perm (Fin 3)) : GL (Fin 3) K :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (σ.permMatrix K) (by
    rw [Matrix.det_permutation]
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h])

omit [CharP K 2] in
theorem coe_permGL (σ : Equiv.Perm (Fin 3)) :
    ((permGL σ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = σ.permMatrix K := rfl

end Elements

section Membership

variable {K : Type} [Field K] {g : ℕ}

theorem mem_statedSU_iff [Finite K] (hK : Nat.card K = (2 ^ g) ^ 2) (A : GL (Fin 3) K) :
    A ∈ StatedSU 3 (2 ^ g) K ↔ (A : Matrix (Fin 3) (Fin 3) K).det = 1 ∧
      ((A : Matrix (Fin 3) (Fin 3) K).map (· ^ 2 ^ g))ᵀ * (A : Matrix (Fin 3) (Fin 3) K) = 1 := by
  have h := (CFSG.LinearGroups.unitary_scalar_kernel Nat.prime_two hK (n := 3)
    (by norm_num)).1
  have := Set.ext_iff.1 h A
  simpa using this

theorem map_pow_permMatrix [CharP K 2] (σ : Equiv.Perm (Fin 3)) :
    (σ.permMatrix K).map (· ^ 2 ^ g) = σ.permMatrix K := by
  ext i j
  simp only [Matrix.map_apply, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply,
    Equiv.toPEquiv_apply]
  split_ifs <;> simp [zero_pow (pow_ne_zero g (two_ne_zero))]

theorem permGL_mem [Finite K] [CharP K 2] (hK : Nat.card K = (2 ^ g) ^ 2)
    (σ : Equiv.Perm (Fin 3)) : permGL σ ∈ StatedSU 3 (2 ^ g) K := by
  rw [mem_statedSU_iff hK, coe_permGL, map_pow_permMatrix, Matrix.transpose_permMatrix,
    ← Matrix.permMatrix_mul, mul_inv_cancel, Matrix.permMatrix_one, Matrix.det_permutation]
  refine ⟨?_, rfl⟩
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
  · simp [h]
  · simpa [h] using CharTwo.neg_eq (1 : K)

end Membership

section Diagonal

variable {K : Type} [Field K] {g : ℕ}

@[expose] noncomputable def diag3GL (l : Kˣ) : GL (Fin 3) K :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero
    (Matrix.diagonal ![(l : K), ((l⁻¹ : Kˣ) : K), 1]) (by
      rw [Matrix.det_diagonal, Fin.prod_univ_three]
      simp)

theorem coe_diag3GL (l : Kˣ) :
    ((diag3GL l : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      Matrix.diagonal ![(l : K), ((l⁻¹ : Kˣ) : K), 1] := rfl

theorem diag3GL_mem [Finite K] (hK : Nat.card K = (2 ^ g) ^ 2) (l : Kˣ)
    (hl : l ^ (2 ^ g + 1) = 1) : diag3GL l ∈ StatedSU 3 (2 ^ g) K := by
  rw [mem_statedSU_iff hK, coe_diag3GL, Matrix.det_diagonal, Fin.prod_univ_three]
  have h1 : (l : K) ^ (2 ^ g + 1) = 1 := by
    have := congrArg (fun u : Kˣ => (u : K)) hl
    simpa using this
  refine ⟨by simp, ?_⟩
  have e : (Matrix.diagonal ![(l : K), ((l⁻¹ : Kˣ) : K), 1]).map (· ^ 2 ^ g) =
      Matrix.diagonal ![(l : K) ^ 2 ^ g, ((l⁻¹ : Kˣ) : K) ^ 2 ^ g, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [zero_pow (pow_ne_zero g two_ne_zero)]
  have hinv : ((l⁻¹ : Kˣ) : K) ^ 2 ^ g * ((l⁻¹ : Kˣ) : K) = 1 := by
    rw [Units.val_inv_eq_inv_val, inv_pow, ← mul_inv, ← pow_succ, h1, inv_one]
  rw [e, Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  fin_cases i
  · simpa [← pow_succ] using h1
  · simpa using hinv
  · simp

end Diagonal

section NormOne

variable {K : Type} [Field K] [Finite K] [CharP K 2] {g : ℕ}

omit [CharP K 2] in
theorem card_normOne (hK : Nat.card K = (2 ^ g) ^ 2) :
    Nat.card (rootsOfUnity (2 ^ g + 1) K) = 2 ^ g + 1 := by
  have : NeZero (2 ^ g + 1) := ⟨by positivity⟩
  refine CFSG.LinearGroups.card_rootsOfUnity_of_dvd ?_
  rw [hK]
  have h := Nat.sq_sub_sq (2 ^ g) 1
  rw [one_pow] at h
  rw [h]
  exact Dvd.intro _ rfl

omit [Finite K] in
theorem eq_one_of_eq_inv (l : Kˣ) (h : l = l⁻¹) : l = 1 := by
  have h1 : (l : K) * l = 1 := by
    have := congrArg (fun u : Kˣ => (u : K) * l) h
    simpa using this
  have h2 : ((l : K) - 1) ^ 2 = 0 := by
    have h2' : (2 : K) = 0 := CharTwo.two_eq_zero
    linear_combination h1 + (1 - (l : K)) * h2'
  have := pow_eq_zero_iff (two_ne_zero) |>.1 h2
  exact Units.ext (sub_eq_zero.1 this)

theorem exists_normOne_ne_one (hK : Nat.card K = (2 ^ g) ^ 2) (hg : 1 ≤ g) :
    ∃ l : Kˣ, l ^ (2 ^ g + 1) = 1 ∧ l ≠ l⁻¹ := by
  have h := card_normOne hK
  have h2 : 2 ≤ 2 ^ g := by
    calc 2 = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ g := Nat.pow_le_pow_right (by norm_num) hg
  have h1 : 1 < Nat.card (rootsOfUnity (2 ^ g + 1) K) := by omega
  have := Finite.one_lt_card_iff_nontrivial.1 h1
  obtain ⟨x, hx⟩ := exists_ne (1 : ↥(rootsOfUnity (2 ^ g + 1) K))
  refine ⟨(x : Kˣ), (mem_rootsOfUnity _ _).1 x.2, fun hh => hx ?_⟩
  exact Subtype.ext (eq_one_of_eq_inv _ hh)

omit [CharP K 2] in
theorem exists_normOne_ne_fixed {p f' : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hf' : 1 ≤ f')
    (hK : Nat.card K = (2 ^ (p * f')) ^ 2) {σ : K ≃+* K} (hσ : orderOf σ = p) :
    ∃ l : Kˣ, l ^ (2 ^ (p * f') + 1) = 1 ∧ σ (l : K) ≠ l := by
  classical
  by_contra hcon
  push Not at hcon
  have hn : 1 ≤ 2 * (p * f') := by nlinarith
  have hF : Nat.card K = 2 ^ (2 * (p * f')) := by rw [hK, ← pow_mul, mul_comm]
  obtain ⟨σ₀, -, -, -, -, hA⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      Nat.prime_two hn hF
  obtain ⟨-, S, hS, hSc⟩ := hA (Subgroup.zpowers σ)
  rw [Nat.card_zpowers, hσ, show 2 * (p * f') = p * (2 * f') by ring,
    Nat.mul_div_cancel_left _ hp.pos] at hSc
  have hstab : ∀ a : K, σ a = a → ∀ τ ∈ Subgroup.zpowers σ, τ a = a := by
    intro a ha
    let H : Subgroup (K ≃+* K) :=
      { carrier := {τ | τ a = a}
        mul_mem' := fun {x y} hx hy => by
          have hx' : x a = a := hx
          have hy' : y a = a := hy
          change x (y a) = a
          rw [hy', hx']
        one_mem' := rfl
        inv_mem' := fun {x} hx => by
          have hx' : x a = a := hx
          change x⁻¹ a = a
          exact (RingEquiv.symm_apply_eq x).2 hx'.symm }
    exact Subgroup.zpowers_le.2 (show σ ∈ H from ha)
  have hfix : ∀ l : ↥(rootsOfUnity (2 ^ (p * f') + 1) K), ((l : Kˣ) : K) ∈ S := fun l => by
    have h1 : σ ((l : Kˣ) : K) = (l : Kˣ) := hcon _ ((mem_rootsOfUnity _ _).1 l.2)
    have : ((l : Kˣ) : K) ∈ (S : Set K) := by
      rw [hS]
      exact hstab _ h1
    exact this
  let f : ↥(rootsOfUnity (2 ^ (p * f') + 1) K) → (↥S)ˣ := fun l =>
    Units.mk0 ⟨((l : Kˣ) : K), hfix l⟩ (fun h => (l : Kˣ).ne_zero (congrArg Subtype.val h))
  have hf : Function.Injective f := fun l₁ l₂ h => by
    apply Subtype.ext
    apply Units.ext
    have := congrArg (fun u : (↥S)ˣ => ((u : ↥S) : K)) h
    simpa [f] using this
  have hcard := Nat.card_le_card_of_injective f hf
  rw [card_normOne hK, Nat.card_units, hSc] at hcard
  have h1 : 2 ^ (2 * f') ≤ 2 ^ (p * f') :=
    Nat.pow_le_pow_right (by norm_num) (by nlinarith)
  have h2 : 0 < 2 ^ (2 * f') := by positivity
  omega

end NormOne

section Center

variable {K : Type} [Field K]

theorem permMatrix_swap01 :
    (Equiv.swap (0 : Fin 3) 1).permMatrix K = !![0, 1, 0; 1, 0, 0; 0, 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.swap_apply_def]

theorem permMatrix_swap12 :
    (Equiv.swap (1 : Fin 3) 2).permMatrix K = !![1, 0, 0; 0, 0, 1; 0, 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.swap_apply_def]

theorem eq_scalar_of_commute {Z : Matrix (Fin 3) (Fin 3) K}
    (h01 : !![0, 1, 0; 1, 0, 0; 0, 0, 1] * Z = Z * !![0, 1, 0; 1, 0, 0; 0, 0, 1])
    (h12 : !![1, 0, 0; 0, 0, 1; 0, 1, 0] * Z = Z * !![1, 0, 0; 0, 0, 1; 0, 1, 0])
    {l m : K} (hlm : l ≠ m)
    (hd : Matrix.diagonal ![l, m, 1] * Z = Z * Matrix.diagonal ![l, m, 1]) :
    ∃ a : K, Z = Matrix.scalar (Fin 3) a := by
  have a1 := congrFun (congrFun h01 0) 0
  have a2 := congrFun (congrFun h01 0) 1
  have a3 := congrFun (congrFun h01 0) 2
  have a4 := congrFun (congrFun h01 2) 0
  have b1 := congrFun (congrFun h12 0) 1
  have b2 := congrFun (congrFun h12 1) 1
  have b3 := congrFun (congrFun h12 1) 2
  have b4 := congrFun (congrFun h12 1) 0
  have d1 := congrFun (congrFun hd 0) 1
  simp [Matrix.mul_apply, Fin.sum_univ_three] at a1 a2 a3 a4 b1 b2 b3 b4 d1
  have hb : Z 0 1 = 0 := by
    have : (l - m) * Z 0 1 = 0 := by linear_combination d1
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hlm)
  have h02 : Z 0 2 = 0 := by rw [← b1]; exact hb
  have h10 : Z 1 0 = 0 := by rw [a1]; exact hb
  have h20 : Z 2 0 = 0 := by rw [b4, h10]
  have h21 : Z 2 1 = 0 := by rw [← a4]; exact h20
  have h12 : Z 1 2 = 0 := by rw [a3]; exact h02
  have h22 : Z 2 2 = Z 0 0 := by rw [b3, a2]
  refine ⟨Z 0 0, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.scalar_apply, hb, h02, h10, h20, h21, h12, h22, a2]

variable [Finite K] [CharP K 2] {g : ℕ}

theorem eq_scalar_of_mem_center (hK : Nat.card K = (2 ^ g) ^ 2) (hg : 1 ≤ g)
    {z : ↥(StatedSU 3 (2 ^ g) K)} (hz : z ∈ Subgroup.center ↥(StatedSU 3 (2 ^ g) K)) :
    ∃ c : Kˣ, (z : GL (Fin 3) K) = Matrix.GeneralLinearGroup.scalar (Fin 3) c ∧ c ^ 3 = 1 := by
  obtain ⟨l, hl, hl2⟩ := exists_normOne_ne_one hK hg
  have key : ∀ A : GL (Fin 3) K, A ∈ StatedSU 3 (2 ^ g) K →
      (A : Matrix (Fin 3) (Fin 3) K) * ((z : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        ((z : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * A := fun A hA => by
    have := congrArg (fun x : ↥(StatedSU 3 (2 ^ g) K) =>
      ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) (Subgroup.mem_center_iff.1 hz ⟨A, hA⟩)
    simpa using this
  have h01 := key (permGL (Equiv.swap 0 1)) (permGL_mem hK _)
  have h12 := key (permGL (Equiv.swap 1 2)) (permGL_mem hK _)
  have hd := key (diag3GL l) (diag3GL_mem hK l hl)
  rw [coe_permGL, permMatrix_swap01] at h01
  rw [coe_permGL, permMatrix_swap12] at h12
  rw [coe_diag3GL] at hd
  have hne : ((l : Kˣ) : K) ≠ ((l⁻¹ : Kˣ) : K) := fun h => hl2 (Units.ext h)
  obtain ⟨a, ha⟩ := eq_scalar_of_commute h01 h12 hne hd
  have hdet := ((mem_statedSU_iff hK _).1 z.2).1
  rw [ha] at hdet
  have h3 : a ^ 3 = 1 := by
    simpa [Matrix.scalar_apply, Matrix.det_diagonal] using hdet
  have ha0 : a ≠ 0 := fun h => by simp [h] at h3
  refine ⟨Units.mk0 a ha0, Units.ext ?_, Units.ext (by simpa using h3)⟩
  rw [ha, Matrix.GeneralLinearGroup.coe_scalar]
  rfl

theorem center_statedSU_eq (hK : Nat.card K = (2 ^ g) ^ 2) (hg : 1 ≤ g) :
    Subgroup.center ↥(StatedSU 3 (2 ^ g) K) =
      (StatedScalars (Fin 3) K).subgroupOf (StatedSU 3 (2 ^ g) K) := by
  ext z
  constructor
  · intro hz
    obtain ⟨c, hc, -⟩ := eq_scalar_of_mem_center hK hg hz
    exact ⟨c, hc.symm⟩
  · intro hz
    rw [Subgroup.mem_center_iff]
    intro t
    have hzc : (z : GL (Fin 3) K) ∈ Subgroup.center (GL (Fin 3) K) := by
      rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
      exact hz
    apply Subtype.ext
    exact Subgroup.mem_center_iff.1 hzc (t : GL (Fin 3) K)

end Center

section Perm

variable {K : Type} [Field K]

theorem map_ringEquiv_permMatrix (σ : K ≃+* K) (π : Equiv.Perm (Fin 3)) :
    (π.permMatrix K).map σ = π.permMatrix K := by
  ext i j
  simp only [Matrix.map_apply, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply,
    Equiv.toPEquiv_apply]
  split_ifs <;> simp

theorem permGL_swap_sq (a b : Fin 3) : (permGL (Equiv.swap a b) : GL (Fin 3) K) ^ 2 = 1 := by
  apply Units.ext
  rw [pow_two, Units.val_mul, coe_permGL, ← Matrix.permMatrix_mul, Equiv.swap_mul_self,
    Matrix.permMatrix_one]
  rfl

theorem permGL_swap01_ne_one : (permGL (Equiv.swap 0 1) : GL (Fin 3) K) ≠ 1 := by
  intro h
  have := congrArg (fun u : GL (Fin 3) K => ((u : Matrix (Fin 3) (Fin 3) K)) 0 0) h
  simp [coe_permGL] at this

theorem permGL_swap12_ne_one : (permGL (Equiv.swap 1 2) : GL (Fin 3) K) ≠ 1 := by
  intro h
  have := congrArg (fun u : GL (Fin 3) K => ((u : Matrix (Fin 3) (Fin 3) K)) 1 1) h
  simp [coe_permGL] at this

theorem permGL_noncomm : (permGL (Equiv.swap 0 1) : GL (Fin 3) K) * permGL (Equiv.swap 1 2) ≠
    permGL (Equiv.swap 1 2) * permGL (Equiv.swap 0 1) := by
  intro h
  have := congrArg (fun u : GL (Fin 3) K => ((u : Matrix (Fin 3) (Fin 3) K)) 0 1) h
  simp [Units.val_mul, coe_permGL, permMatrix_swap01, permMatrix_swap12, Matrix.mul_apply,
    Fin.sum_univ_three] at this

end Perm

section Claims

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem lieModel_psu_of_range {p f' : ℕ} (hp5 : 5 ≤ p) (hf' : 1 ≤ f')
    (hK : Nat.card K = (2 ^ (p * f')) ^ 2) {G : Type} [Group G]
    (φ : ↥(StatedSU 3 (2 ^ (p * f')) K) →* G) (hφ : Function.Injective φ) :
    LieModel (↥φ.range ⧸ Subgroup.center ↥φ.range) .PSU 3 2 (p * f') := by
  have hg : 1 ≤ p * f' := by nlinarith
  let e : ↥(StatedSU 3 (2 ^ (p * f')) K) ≃* ↥φ.range := MonoidHom.ofInjective hφ
  let e' : ↥(StatedSU 3 (2 ^ (p * f')) K) ⧸ Subgroup.center ↥(StatedSU 3 (2 ^ (p * f')) K) ≃*
      ↥φ.range ⧸ Subgroup.center ↥φ.range :=
    QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)
  let e'' : ↥(StatedSU 3 (2 ^ (p * f')) K) ⧸ Subgroup.center ↥(StatedSU 3 (2 ^ (p * f')) K) ≃*
      StatedProj (StatedSU 3 (2 ^ (p * f')) K) :=
    QuotientGroup.quotientMulEquivOfEq (center_statedSU_eq hK hg)
  have hadm : StatedLieAdmissible .PSU 3 2 (p * f') := by
    refine ⟨Nat.prime_two, hg, le_refl _, ?_⟩
    intro h
    simp only [Prod.mk.injEq] at h
    have : 2 ^ 5 ≤ 2 ^ (p * f') := Nat.pow_le_pow_right (by norm_num) (by nlinarith)
    omega
  refine Or.inl ⟨by decide, ?_⟩
  exact ⟨hadm, K, inferInstance, inferInstance, hK, ⟨e'.symm.trans e''⟩⟩

theorem su3_type_claims {p f' : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hf' : 1 ≤ f')
    (hK : Nat.card K = (2 ^ (p * f')) ^ 2) {σ : K ≃+* K} (hσ : orderOf σ = p) {G : Type}
    [Group G] (α : MulAut G) (φ : ↥(StatedSU 3 (2 ^ (p * f')) K) →* G)
    (hφ : Function.Injective φ)
    (τ : ↥(StatedSU 3 (2 ^ (p * f')) K) →* ↥(StatedSU 3 (2 ^ (p * f')) K))
    (hτ : ∀ A, (((τ A : ↥(StatedSU 3 (2 ^ (p * f')) K)) : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) =
      (((A : ↥(StatedSU 3 (2 ^ (p * f')) K)) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).map σ)
    (hαφ : ∀ A, α (φ A) = φ (τ A)) (Q : Subgroup G) (hQ : φ.range = Q) :
    (∀ g ∈ Q, α g ∈ Q) ∧ (∃ g ∈ Q, α g ≠ g) ∧ (∀ z ∈ Subgroup.center ↥Q, z ^ 3 = 1) ∧
      (∃ (t' : StatedLieTag) (n' f'' : ℕ), 1 ≤ f'' ∧
        LieModel (↥Q ⧸ Subgroup.center ↥Q) t' n' 2 (p * f'')) ∧
      ∃ t₁ ∈ Q, α t₁ = t₁ ∧ ∃ t₂ ∈ Q, α t₂ = t₂ ∧ (∃ k : ℕ, orderOf t₁ = 2 ^ k) ∧
        (∃ k : ℕ, orderOf t₂ = 2 ^ k) ∧ t₁ * t₂ ≠ t₂ * t₁ := by
  subst hQ
  have hg : 1 ≤ p * f' := by nlinarith
  have hc : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set s₁ : ↥(StatedSU 3 (2 ^ (p * f')) K) :=
    ⟨permGL (Equiv.swap 0 1), permGL_mem hK _⟩ with hs₁
  set s₂ : ↥(StatedSU 3 (2 ^ (p * f')) K) :=
    ⟨permGL (Equiv.swap 1 2), permGL_mem hK _⟩ with hs₂
  have hτs : ∀ π : Equiv.Perm (Fin 3), ∀ h : permGL π ∈ StatedSU 3 (2 ^ (p * f')) K,
      τ ⟨permGL π, h⟩ = ⟨permGL π, h⟩ := fun π h => by
    apply Subtype.ext
    apply Units.ext
    rw [hτ]
    exact map_ringEquiv_permMatrix σ π
  refine ⟨?_, ?_, ?_, ⟨.PSU, 3, f', hf', lieModel_psu_of_range hp5 hf' hK φ hφ⟩, ?_⟩
  · rintro _ ⟨A, rfl⟩
    exact ⟨τ A, (hαφ A).symm⟩
  · obtain ⟨l, hl, hmove⟩ := exists_normOne_ne_fixed hp hp5 hf' hK hσ
    set A₀ : ↥(StatedSU 3 (2 ^ (p * f')) K) := ⟨diag3GL l, diag3GL_mem hK l hl⟩ with hA₀
    refine ⟨φ A₀, ⟨A₀, rfl⟩, ?_⟩
    rw [hαφ]
    intro h
    have h1 := hφ h
    have h2 := congrArg (fun A : ↥(StatedSU 3 (2 ^ (p * f')) K) =>
      ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 0) h1
    simp only [hτ, hA₀, coe_diag3GL, Matrix.map_apply] at h2
    simp at h2
    exact hmove h2
  · intro z hz
    let e : ↥(StatedSU 3 (2 ^ (p * f')) K) ≃* ↥φ.range := MonoidHom.ofInjective hφ
    have hw : e.symm z ∈ Subgroup.center ↥(StatedSU 3 (2 ^ (p * f')) K) := by
      rw [Subgroup.mem_center_iff]
      intro t
      apply e.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact Subgroup.mem_center_iff.1 hz (e t)
    obtain ⟨c, hcz, hc3⟩ := eq_scalar_of_mem_center hK hg hw
    have hw3 : (e.symm z) ^ 3 = 1 := by
      apply Subtype.ext
      apply Units.ext
      rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, hcz]
      have : (Matrix.GeneralLinearGroup.scalar (Fin 3) c : GL (Fin 3) K) ^ 3 = 1 := by
        rw [← map_pow, hc3, map_one]
      have := congrArg (fun u : GL (Fin 3) K => (u : Matrix (Fin 3) (Fin 3) K)) this
      simpa using this
    calc z ^ 3 = e ((e.symm z) ^ 3) := by rw [map_pow, MulEquiv.apply_symm_apply]
      _ = 1 := by rw [hw3, map_one]
  · refine ⟨φ s₁, ⟨s₁, rfl⟩, ?_, φ s₂, ⟨s₂, rfl⟩, ?_, ⟨1, ?_⟩, ⟨1, ?_⟩, ?_⟩
    · rw [hαφ, hs₁, hτs]
    · rw [hαφ, hs₂, hτs]
    · rw [orderOf_injective φ hφ, pow_one]
      refine orderOf_eq_prime ?_ ?_
      · apply Subtype.ext
        simpa [hs₁] using permGL_swap_sq (K := K) 0 1
      · intro h
        exact permGL_swap01_ne_one (K := K) (congrArg Subtype.val h)
    · rw [orderOf_injective φ hφ, pow_one]
      refine orderOf_eq_prime ?_ ?_
      · apply Subtype.ext
        simpa [hs₂] using permGL_swap_sq (K := K) 1 2
      · intro h
        exact permGL_swap12_ne_one (K := K) (congrArg Subtype.val h)
    · intro h
      rw [← map_mul, ← map_mul] at h
      exact permGL_noncomm (K := K) (congrArg Subtype.val (hφ h))

end Claims

end CFSG.RankThree.PartOne.KLCE
