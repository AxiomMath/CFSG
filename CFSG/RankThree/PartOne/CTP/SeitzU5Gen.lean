module

public import CFSG.RankThree.PartOne.CTP.SeitzU5Alg
public import CFSG.RankThree.PartOne.CTP.SeitzU5Span
public import CFSG.ClassicalGroups.Unitary.Base
public import CFSG.ClassicalInvolution.Phan.Standard

public section

namespace CFSG.RankThree.PartOne.CTP.U5Gen

open Matrix CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.Unitary
  CFSG.ClassicalInvolution.Phan CFSG.LieType.BorelTits CFSG.RankThree.PartOne.CTP.U5Alg

section Generic

variable {K : Type} [Field K] (σ : K ≃+* K)

@[expose] noncomputable def dgSU (t : Fin 5 → K) (ht : ∀ i, σ (t i) * t i = 1)
    (hdet : ∏ i, t i = 1) : SUid σ 5 :=
  mkSU σ (Matrix.diagonal t) (by rw [Matrix.det_diagonal]; exact hdet) (by
    intro x y
    simp only [herm, Matrix.mulVec_diagonal, map_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    linear_combination (σ (x i) * y i) * ht i)

@[expose] noncomputable def shiftSU : SUid σ 5 :=
  mkSU σ (Equiv.Perm.permMatrix K (finRotate 5)⁻¹)
    (by rw [Matrix.det_permutation, map_inv, sign_finRotate]; norm_num) (by
    intro x y
    have hm : ∀ v : Fin 5 → K,
        (Equiv.Perm.permMatrix K (finRotate 5)⁻¹ *ᵥ v) = fun i => v (i - 1) := by
      intro v; ext i
      simp [Matrix.mulVec, dotProduct, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]
    rw [hm, hm]
    exact Equiv.sum_comp ((finRotate 5)⁻¹ : Equiv.Perm (Fin 5)) (fun i => σ (x i) * y i))

theorem ne_zero_of_norm_one {η : K} (hη : σ η * η = 1) : η ≠ 0 := by
  rintro rfl
  simp at hη

@[expose] noncomputable def kSU (h2 : (2 : K) = 0) (η : K) (hη : σ η * η = 1) : SUid σ 5 :=
  mkSU σ (kMat η ((η ^ 5)⁻¹)) (by
    rw [kMat_det h2, mul_inv_cancel₀ (pow_ne_zero 5 (ne_zero_of_norm_one σ hη))]) (by
    intro x y
    have hρ : σ ((η ^ 5)⁻¹) * (η ^ 5)⁻¹ = 1 := by
      rw [map_inv₀, map_pow, ← mul_inv, ← mul_pow, hη, one_pow, inv_one]
    have := kMat_conjTr_mul h2 σ.toRingHom hη hρ
    rw [herm_mulVec]
    have h1 : conjTr σ (kMat η ((η ^ 5)⁻¹)) * kMat η ((η ^ 5)⁻¹) = 1 := this
    rw [h1, Matrix.one_mulVec])

@[expose] noncomputable def hSU (γ : K) (hγ : σ γ * γ = 1) : SUid σ 5 :=
  dgSU σ ![(γ ^ 4)⁻¹, γ, γ, γ, γ] (by
    intro i
    have h0 : γ ≠ 0 := ne_zero_of_norm_one σ hγ
    fin_cases i
    · simp only [Fin.zero_eta, Matrix.cons_val_zero, map_inv₀, map_pow]
      rw [← mul_inv, ← mul_pow, hγ, one_pow, inv_one]
    all_goals simpa using hγ) (by
    have h0 : γ ≠ 0 := ne_zero_of_norm_one σ hγ
    simp [Fin.prod_univ_five]
    field_simp)

@[expose] def mat (g : SUid σ 5) : Matrix (Fin 5) (Fin 5) K :=
  ((g : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K)

theorem mat_mul (g h : SUid σ 5) : mat σ (g * h) = mat σ g * mat σ h := rfl

theorem mat_hSU (γ : K) (hγ : σ γ * γ = 1) : mat σ (hSU σ γ hγ) = hMat γ := by
  rw [hMat_eq_diagonal]
  rfl

theorem mat_kSU (h2 : (2 : K) = 0) (η : K) (hη : σ η * η = 1) :
    mat σ (kSU σ h2 η hη) = kMat η ((η ^ 5)⁻¹) := rfl

theorem mat_comm_eq (g₁ g₂ : SUid σ 5) (U : Matrix (Fin 5) (Fin 5) K)
    (hU : mat σ g₁ * mat σ g₂ = U * (mat σ g₂ * mat σ g₁)) :
    mat σ (g₁ * g₂ * g₁⁻¹ * g₂⁻¹) = U := by
  have h1 : (g₁ * g₂ * g₁⁻¹ * g₂⁻¹) * (g₂ * g₁) = g₁ * g₂ := by group
  have h2 : mat σ (g₁ * g₂ * g₁⁻¹ * g₂⁻¹) * mat σ (g₂ * g₁) = U * mat σ (g₂ * g₁) := by
    rw [← mat_mul, h1, mat_mul, hU, mat_mul]
  exact (Units.mul_left_inj ((g₂ * g₁ : SUid σ 5) : GL (Fin 5) K)).mp h2

theorem mat_comm_hk (h2 : (2 : K) = 0) (γ η : K) (hγ : σ γ * γ = 1) (hη : σ η * η = 1) :
    mat σ (hSU σ γ hγ * kSU σ h2 η hη * (hSU σ γ hγ)⁻¹ * (kSU σ h2 η hη)⁻¹) =
      U5 (((η ^ 5)⁻¹ + 1) * ((γ ^ 5)⁻¹ + 1))
        (((η ^ 5)⁻¹)⁻¹ * ((η ^ 5)⁻¹ + 1) * (γ ^ 5 + 1))
        (((η ^ 5)⁻¹ + ((η ^ 5)⁻¹)⁻¹) * (γ ^ 5 + 1)) := by
  refine mat_comm_eq σ _ _ _ ?_
  rw [mat_hSU, mat_kSU]
  exact hMat_mul_kMat h2 (ne_zero_of_norm_one σ hγ) (ne_zero_of_norm_one σ hη)
    (inv_ne_zero (pow_ne_zero 5 (ne_zero_of_norm_one σ hη)))

@[expose] def yVec : Fin 5 → K := ![0, 1, 1, 1, 1]

theorem herm_yVec (h2 : (2 : K) = 0) : herm σ (yVec : Fin 5 → K) yVec = 0 := by
  simp only [herm, Fin.sum_univ_five, yVec]
  simp
  linear_combination 2 * h2

theorem mat_tv_yVec (hσ : ∀ c, σ (σ c) = c) (h2 : (2 : K) = 0) {b : K} (hb : b + σ b = 0) :
    mat σ (tv hσ (herm_yVec σ h2) hb) = U5 0 0 b := by
  show tvMat σ yVec b = U5 0 0 b
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tvMat, vecMulVec, yVec, U5, A5]

@[expose] noncomputable def pp (η γ : K) : K := ((η ^ 5)⁻¹ + 1) * ((γ ^ 5)⁻¹ + 1)

theorem rr_eq {η γ : K} (hη : σ η * η = 1) (hγ : σ γ * γ = 1) :
    ((η ^ 5)⁻¹)⁻¹ * ((η ^ 5)⁻¹ + 1) * (γ ^ 5 + 1) = σ (pp η γ) := by
  have hη0 : η ≠ 0 := ne_zero_of_norm_one σ hη
  have hγ0 : γ ≠ 0 := ne_zero_of_norm_one σ hγ
  have h1 : σ η = η⁻¹ := by field_simp; linear_combination hη
  have h2' : σ γ = γ⁻¹ := by field_simp; linear_combination hγ
  rw [pp, map_mul, map_add, map_add, map_inv₀, map_inv₀, map_pow, map_pow, h1, h2', map_one]
  field_simp
  ring

theorem comm_mem {G : Type*} [Group G] (M : Subgroup G) {a b : G} (ha : a ∈ M) (hb : b ∈ M) :
    a * b * a⁻¹ * b⁻¹ ∈ M :=
  M.mul_mem (M.mul_mem (M.mul_mem ha hb) (M.inv_mem ha)) (M.inv_mem hb)

theorem tv_mem_of_four (hσ : ∀ c, σ (σ c) = c) (h2 : (2 : K) = 0) (M : Subgroup (SUid σ 5))
    {γ η γ' η' : K} (hγ : σ γ * γ = 1) (hη : σ η * η = 1) (hγ' : σ γ' * γ' = 1)
    (hη' : σ η' * η' = 1) (m1 : hSU σ γ hγ ∈ M) (m2 : kSU σ h2 η hη ∈ M)
    (m3 : hSU σ γ' hγ' ∈ M) (m4 : kSU σ h2 η' hη' ∈ M)
    (hb : (σ (pp η γ) * pp η' γ' + σ (pp η' γ') * pp η γ) +
      σ (σ (pp η γ) * pp η' γ' + σ (pp η' γ') * pp η γ) = 0) :
    tv hσ (herm_yVec σ h2) hb ∈ M := by
  set K₁ := hSU σ γ hγ * kSU σ h2 η hη * (hSU σ γ hγ)⁻¹ * (kSU σ h2 η hη)⁻¹ with hK₁
  set K₂ := hSU σ γ' hγ' * kSU σ h2 η' hη' * (hSU σ γ' hγ')⁻¹ * (kSU σ h2 η' hη')⁻¹ with hK₂
  have hK₁M : K₁ ∈ M := comm_mem M m1 m2
  have hK₂M : K₂ ∈ M := comm_mem M m3 m4
  have e1 := mat_comm_hk σ h2 γ η hγ hη
  have e2 := mat_comm_hk σ h2 γ' η' hγ' hη'
  rw [rr_eq σ hη hγ] at e1
  rw [rr_eq σ hη' hγ'] at e2
  have e3 : mat σ (K₁ * K₂ * K₁⁻¹ * K₂⁻¹) =
      U5 0 0 (σ (pp η γ) * pp η' γ' + σ (pp η' γ') * pp η γ) := by
    refine mat_comm_eq σ _ _ _ ?_
    rw [hK₁, hK₂, e1, e2]
    exact U5_comm h2 _ _ _ _ _ _
  have e4 : K₁ * K₂ * K₁⁻¹ * K₂⁻¹ = tv hσ (herm_yVec σ h2) hb := by
    apply Subtype.ext
    apply Units.ext
    exact (e3.trans (mat_tv_yVec σ hσ h2 hb).symm)
  rw [← e4]
  exact comm_mem M hK₁M hK₂M

theorem tv_congr (hσ : ∀ c, σ (σ c) = c) {n : ℕ} {a : Fin n → K} (ha : herm σ a a = 0)
    {c c' : K} (e : c = c') (hc : c + σ c = 0) (hc' : c' + σ c' = 0) :
    tv hσ ha hc = tv hσ ha hc' := by
  subst e
  rfl

end Generic

section Root

variable {K : Type} [Field K] [Finite K] [CharP K 2] {f : ℕ}

local notation "σ" => unitaryInvolution K 2 f

theorem B5_trace_zero (hσ : ∀ c, σ (σ c) = c) (h2 : (2 : K) = 0) {x : K}
    (hx : x ∈ CFSG.RankThree.PartOne.CTP.U5Span.B5 K f) : x + σ x = 0 := by
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨p, -, p', -, rfl⟩ := hx
    rw [map_add, map_mul, map_mul, hσ, hσ]
    linear_combination (σ p * p' + σ p' * p) * h2
  | zero => simp
  | add x y _ _ hx hy =>
    rw [map_add]
    linear_combination hx + hy
  | neg x _ hx =>
    rw [map_neg]
    linear_combination -hx

theorem tv_mem_of_closure (hσ : ∀ c, σ (σ c) = c) (h2 : (2 : K) = 0) (M : Subgroup (SUid σ 5))
    (hD : ∀ (γ : K) (hγ : σ γ * γ = 1), hSU σ γ hγ ∈ M)
    (hC : ∀ (η : K) (hη : σ η * η = 1), kSU σ h2 η hη ∈ M) {x : K}
    (hx : x ∈ CFSG.RankThree.PartOne.CTP.U5Span.B5 K f) :
    ∃ hx' : x + σ x = 0, tv hσ (herm_yVec σ h2) hx' ∈ M := by
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨p, hp, p', hp', rfl⟩ := hx
    obtain ⟨ρ, ⟨η, hη, rfl⟩, z, ⟨γ, hγ, rfl⟩, rfl⟩ := hp
    obtain ⟨ρ', ⟨η', hη', rfl⟩, z', ⟨γ', hγ', rfl⟩, rfl⟩ := hp'
    have hb := B5_trace_zero hσ h2 (AddSubgroup.subset_closure
      ⟨_, ⟨_, ⟨η, hη, rfl⟩, _, ⟨γ, hγ, rfl⟩, rfl⟩, _, ⟨_, ⟨η', hη', rfl⟩, _, ⟨γ', hγ', rfl⟩, rfl⟩,
        rfl⟩)
    exact ⟨hb, tv_mem_of_four σ hσ h2 M hγ hη hγ' hη' (hD γ hγ) (hC η hη) (hD γ' hγ')
      (hC η' hη') hb⟩
  | zero =>
    have h0 : (0 : K) + σ 0 = 0 := by simp
    exact ⟨h0, by rw [tv_zero hσ (herm_yVec σ h2) h0]; exact M.one_mem⟩
  | add x y hx hy ihx ihy =>
    obtain ⟨hcx, hmx⟩ := ihx
    obtain ⟨hcy, hmy⟩ := ihy
    have hcxy : (x + y) + σ (x + y) = 0 := by rw [map_add]; linear_combination hcx + hcy
    exact ⟨hcxy, by
      rw [← tv_mul_tv hσ (herm_yVec σ h2) hcx hcy hcxy]
      exact M.mul_mem hmx hmy⟩
  | neg x hx ihx =>
    obtain ⟨hcx, hmx⟩ := ihx
    have e : -x = x := CharTwo.neg_eq x
    have hcn : -x + σ (-x) = 0 := by rw [e]; exact hcx
    exact ⟨hcn, by rw [tv_congr σ hσ (herm_yVec σ h2) e hcn hcx]; exact hmx⟩

theorem tv_mem_y (hK : Nat.card K = (2 ^ f) ^ 2) (hf : 6 ≤ f) (h5 : 5 ∣ 2 ^ f + 1)
    (h2 : (2 : K) = 0) (M : Subgroup (SUid σ 5))
    (hD : ∀ (γ : K) (hγ : σ γ * γ = 1), hSU σ γ hγ ∈ M)
    (hC : ∀ (η : K) (hη : σ η * η = 1), kSU σ h2 η hη ∈ M) {c : K} (hc : c + σ c = 0) :
    tv (unitaryInvolution_involutive hK) (herm_yVec σ h2) hc ∈ M := by
  have hfix : σ c = c := by
    have : σ c = -c := by linear_combination hc
    rw [this]
    exact CharTwo.neg_eq c
  have hB := CFSG.RankThree.PartOne.CTP.U5Span.mem_B5_of_fixed hK hf h5 hfix
  obtain ⟨hc', hm⟩ := tv_mem_of_closure (unitaryInvolution_involutive hK) h2 M hD hC hB
  exact hm

end Root

section Plane

variable {K : Type} [Field K] [Finite K] [CharP K 2] {f : ℕ}

local notation "σ" => unitaryInvolution K 2 f

@[expose] def Cset (hσ : ∀ c : K, σ (σ c) = c) (M : Subgroup (SUid σ 5)) : Set (Fin 5 → K) :=
  {a | ∃ ha : herm σ a a = 0, ∀ (c : K) (hc : c + σ c = 0), tv hσ ha hc ∈ M}

theorem dgSU_smul (t : Fin 5 → K) (ht : ∀ i, σ (t i) * t i = 1) (hdet : ∏ i, t i = 1)
    (v : Fin 5 → K) : dgSU σ t ht hdet • v = fun i => t i * v i := by
  show Matrix.diagonal t *ᵥ v = _
  ext i
  exact Matrix.mulVec_diagonal t v i

theorem tv_smul_centre (hσ : ∀ c : K, σ (σ c) = c) (a : Fin 5 → K) (ha : herm σ a a = 0)
    (lam : K) (ha' : herm σ (lam • a) (lam • a) = 0) {c : K} (hc : c + σ c = 0)
    (hc' : σ lam * lam * c + σ (σ lam * lam * c) = 0) :
    tv hσ ha' hc = tv hσ ha hc' := by
  apply ext_smul
  intro v
  rw [tv_smul, tv_smul, herm_smul_left, smul_smul]
  congr 2
  ring

theorem zero_mem_Cset (hσ : ∀ c : K, σ (σ c) = c) (M : Subgroup (SUid σ 5)) :
    (0 : Fin 5 → K) ∈ Cset hσ M := by
  refine ⟨herm_zero_left _ _, fun c hc => ?_⟩
  have : tv hσ (herm_zero_left σ (0 : Fin 5 → K)) hc = 1 := by
    apply ext_smul
    intro v
    rw [tv_smul, one_smul]
    simp
  rw [this]
  exact M.one_mem

theorem Cset_smul (hσ : ∀ c : K, σ (σ c) = c) (M : Subgroup (SUid σ 5)) {a : Fin 5 → K}
    (ha : a ∈ Cset hσ M) (lam : K) : lam • a ∈ Cset hσ M := by
  obtain ⟨ha0, ha⟩ := ha
  have ha' : herm σ (lam • a) (lam • a) = 0 := by
    rw [herm_smul_left, herm_smul_right, ha0]; ring
  refine ⟨ha', fun c hc => ?_⟩
  have hc' : σ lam * lam * c + σ (σ lam * lam * c) = 0 := by
    rw [map_mul, map_mul, hσ]
    linear_combination (σ lam * lam) * hc
  rw [tv_smul_centre hσ a ha0 lam ha' hc hc']
  exact ha _ _

theorem Cset_conj (hσ : ∀ c : K, σ (σ c) = c) (M : Subgroup (SUid σ 5)) (g : SUid σ 5)
    (hg : ∀ x ∈ M, g * x * g⁻¹ ∈ M) {a : Fin 5 → K} (ha : a ∈ Cset hσ M) :
    g • a ∈ Cset hσ M := by
  obtain ⟨ha0, ha⟩ := ha
  have ha' : herm σ (g • a) (g • a) = 0 := by rw [herm_smul_smul, ha0]
  refine ⟨ha', fun c hc => ?_⟩
  have : tv hσ ha' hc = g * tv hσ ha0 hc * g⁻¹ := by
    apply ext_smul
    intro v
    rw [conj_smul_of_tv g _ (tv_smul hσ ha0 hc), tv_smul]
  rw [this]
  exact hg _ (ha c hc)

theorem Cset_conj_mem (hσ : ∀ c : K, σ (σ c) = c) (M : Subgroup (SUid σ 5)) (g : SUid σ 5)
    (hg : g ∈ M) {a : Fin 5 → K} (ha : a ∈ Cset hσ M) : g • a ∈ Cset hσ M :=
  Cset_conj hσ M g (fun _ hx => M.mul_mem (M.mul_mem hg hx) (M.inv_mem hg)) ha

theorem Cset_pair (hσ : ∀ c : K, σ (σ c) = c) (M : Subgroup (SUid σ 5)) (h2 : (2 : K) = 0)
    {a a' : Fin 5 → K} (ha : a ∈ Cset hσ M) (ha' : a' ∈ Cset hσ M)
    (hlam : σ (herm σ a' a) = herm σ a' a) (hne : herm σ a' a ≠ 0) : a + a' ∈ Cset hσ M := by
  obtain ⟨ha'0, ha'⟩ := ha'
  have hc : (herm σ a' a)⁻¹ + σ (herm σ a' a)⁻¹ = 0 := by
    rw [map_inv₀, hlam]
    linear_combination (herm σ a' a)⁻¹ * h2
  have hg : tv hσ ha'0 hc ∈ M := ha' _ _
  have := Cset_conj_mem hσ M (tv hσ ha'0 hc) hg ha
  rwa [tv_smul, inv_mul_cancel₀ hne, one_smul] at this

@[expose] noncomputable def dgTau (τ : K) (hτ : σ τ * τ = 1) : SUid σ 5 :=
  dgSU σ ![1, 1, 1, τ, τ⁻¹] (by
    intro i
    have h0 : τ ≠ 0 := ne_zero_of_norm_one σ hτ
    fin_cases i
    · simp
    · simp
    · simp
    · simpa using hτ
    · simp only [Fin.reduceFinMk, Matrix.cons_val]
      rw [map_inv₀, ← mul_inv, hτ, inv_one]) (by
    have h0 : τ ≠ 0 := ne_zero_of_norm_one σ hτ
    simp [Fin.prod_univ_five, h0])

theorem dgTau_smul (τ : K) (hτ : σ τ * τ = 1) (v : Fin 5 → K) :
    dgTau τ hτ • v = ![v 0, v 1, v 2, τ * v 3, τ⁻¹ * v 4] := by
  rw [dgTau, dgSU_smul]
  ext i
  fin_cases i <;> simp

theorem plane_point (hσ : ∀ c : K, σ (σ c) = c) (h2 : (2 : K) = 0) (M : Subgroup (SUid σ 5))
    (hD : ∀ (τ : K) (hτ : σ τ * τ = 1), dgTau τ hτ ∈ M)
    (hy : (yVec : Fin 5 → K) ∈ Cset hσ M) {τ : K} (hτ : σ τ * τ = 1) (hτ1 : τ ≠ 1) :
    (![0, 0, 0, 1 + τ, 1 + τ⁻¹] : Fin 5 → K) ∈ Cset hσ M := by
  have h0 : τ ≠ 0 := ne_zero_of_norm_one σ hτ
  have hστ : σ τ = τ⁻¹ := by field_simp; linear_combination hτ
  have hy' := Cset_conj_mem hσ M (dgTau τ hτ) (hD τ hτ) hy
  rw [dgTau_smul] at hy'
  have hlam : herm σ (![yVec 0, yVec 1, yVec 2, τ * yVec 3, τ⁻¹ * yVec 4] : Fin 5 → K) yVec =
      τ + τ⁻¹ := by
    simp only [herm, Fin.sum_univ_five, yVec]
    simp [hστ, map_inv₀]
    linear_combination h2
  have hne : τ + τ⁻¹ ≠ 0 := by
    intro h
    have h1 : τ ^ 2 + 1 = 0 := by field_simp at h; linear_combination h
    have h3 : (τ + 1) ^ 2 = 0 := by linear_combination h1 + (τ) * h2
    have h4 : τ + 1 = 0 := pow_eq_zero_iff (two_ne_zero) |>.mp h3
    exact hτ1 (by linear_combination h4 - h2)
  have := Cset_pair hσ M h2 hy hy' (by rw [hlam, map_add, map_inv₀, hστ, inv_inv]; ring)
    (by rw [hlam]; exact hne)
  convert this using 1
  ext i
  fin_cases i <;> simp [yVec] <;> linear_combination (-1) * h2

theorem plane_all_of_point (hσ : ∀ c : K, σ (σ c) = c) (h2 : (2 : K) = 0)
    (M : Subgroup (SUid σ 5)) (hD : ∀ (τ : K) (hτ : σ τ * τ = 1), dgTau τ hτ ∈ M)
    {u₃ u₄ : K} (hu₃ : u₃ ≠ 0) (hu₄ : u₄ ≠ 0) (hun : σ u₃ * u₃ = σ u₄ * u₄)
    (hu : (![0, 0, 0, u₃, u₄] : Fin 5 → K) ∈ Cset hσ M) (a₃ a₄ : K)
    (h : σ a₃ * a₃ = σ a₄ * a₄) : (![0, 0, 0, a₃, a₄] : Fin 5 → K) ∈ Cset hσ M := by
  by_cases ha3 : a₃ = 0
  · have ha4 : a₄ = 0 := by
      subst ha3
      simp only [map_zero, mul_zero] at h
      rcases mul_eq_zero.mp h.symm with h' | h'
      · exact (map_eq_zero σ).mp h'
      · exact h'
    have : (![0, 0, 0, a₃, a₄] : Fin 5 → K) = 0 := by
      ext i
      fin_cases i <;> simp [ha3, ha4]
    rw [this]
    exact zero_mem_Cset hσ M
  · have ha4 : a₄ ≠ 0 := by
      intro h4
      subst h4
      simp only [map_zero, mul_zero] at h
      rcases mul_eq_zero.mp h with h' | h'
      · exact ha3 ((map_eq_zero σ).mp h')
      · exact ha3 h'
    obtain ⟨s, hs⟩ : ∃ s : K, s ^ 2 = u₄ * a₃ / (u₃ * a₄) := by
      obtain ⟨s, hs⟩ := FiniteField.isSquare_of_char_two (F := K) (ringChar.eq K 2)
        (u₄ * a₃ / (u₃ * a₄))
      exact ⟨s, by rw [sq]; exact hs.symm⟩
    have hs0 : s ≠ 0 := by
      rintro rfl
      have : u₄ * a₃ / (u₃ * a₄) = 0 := by rw [← hs]; ring
      rcases div_eq_zero_iff.mp this with h' | h'
      · exact mul_ne_zero hu₄ ha3 h'
      · exact mul_ne_zero hu₃ ha4 h'
    have hσu₃ : σ u₃ ≠ 0 := (map_ne_zero σ).mpr hu₃
    have hσa₄ : σ a₄ ≠ 0 := (map_ne_zero σ).mpr ha4
    have hws : σ (u₄ * a₃ / (u₃ * a₄)) * (u₄ * a₃ / (u₃ * a₄)) = 1 := by
      rw [map_div₀, map_mul, map_mul, div_mul_div_comm]
      have e1 : σ u₄ * σ a₃ * (u₄ * a₃) = (σ u₄ * u₄) * (σ a₃ * a₃) := by ring
      have e2 : σ u₃ * σ a₄ * (u₃ * a₄) = (σ u₃ * u₃) * (σ a₄ * a₄) := by ring
      rw [e1, e2, ← hun, ← h]
      exact div_self (mul_ne_zero (mul_ne_zero hσu₃ hu₃)
        (mul_ne_zero ((map_ne_zero σ).mpr ha3) ha3))
    have hsn : σ s * s = 1 := by
      have hsq : (σ s * s) ^ 2 = 1 := by
        calc (σ s * s) ^ 2 = σ (s ^ 2) * s ^ 2 := by rw [map_pow]; ring
          _ = 1 := by rw [hs]; exact hws
      have h3 : (σ s * s + 1) ^ 2 = 0 := by linear_combination hsq + (σ s * s + 1) * h2
      have h4 : σ s * s + 1 = 0 := pow_eq_zero_iff two_ne_zero |>.mp h3
      linear_combination h4 - h2
    have hs' : s ^ 2 * (u₃ * a₄) = u₄ * a₃ := by
      rw [hs]; field_simp
    have hmem := Cset_conj_mem hσ M (dgTau s hsn) (hD s hsn) hu
    rw [dgTau_smul] at hmem
    have hmem' := Cset_smul hσ M hmem (a₃ / (s * u₃))
    convert hmem' using 1
    ext i
    fin_cases i
    · simp
    · simp
    · simp
    · simp only [Fin.reduceFinMk, Matrix.cons_val, Pi.smul_apply, smul_eq_mul]
      field_simp
    · simp only [Fin.reduceFinMk, Matrix.cons_val, Pi.smul_apply, smul_eq_mul]
      field_simp
      linear_combination hs'

theorem plane_all (hσ : ∀ c : K, σ (σ c) = c) (hσi : IsUnitaryInvolution σ) (h2 : (2 : K) = 0)
    (M : Subgroup (SUid σ 5)) (hD : ∀ (τ : K) (hτ : σ τ * τ = 1), dgTau τ hτ ∈ M)
    (hy : (yVec : Fin 5 → K) ∈ Cset hσ M) (a₃ a₄ : K) (h : σ a₃ * a₃ = σ a₄ * a₄) :
    (![0, 0, 0, a₃, a₄] : Fin 5 → K) ∈ Cset hσ M := by
  obtain ⟨τ₀, hτ₀, hτ₀1⟩ := hσi.exists_norm_one_ne_one
  have hτ0 : τ₀ ≠ 0 := ne_zero_of_norm_one σ hτ₀
  have hu₀ := plane_point hσ h2 M hD hy hτ₀ hτ₀1
  have hu : 1 + τ₀ ≠ 0 := by
    intro h'
    exact hτ₀1 (by linear_combination h' - h2)
  have hστ : σ τ₀ = τ₀⁻¹ := by field_simp; linear_combination hτ₀
  have hu' : 1 + τ₀⁻¹ ≠ 0 := by
    intro h'
    apply hu
    have : τ₀ * (1 + τ₀⁻¹) = 1 + τ₀ := by field_simp; ring
    rw [← this, h', mul_zero]
  refine plane_all_of_point hσ h2 M hD hu hu' ?_ hu₀ a₃ a₄ h
  rw [map_add, map_add, map_one, map_inv₀, hστ, inv_inv]
  ring

@[expose] def extVec (i : ℕ) (a : Fin 2 → K) : Fin 5 → K := blockSel K 5 2 i *ᵥ a

theorem herm_extVec_left (i : ℕ) (a : Fin 2 → K) (v : Fin 5 → K) :
    herm σ (extVec i a) v = herm σ a ((blockSel K 5 2 i)ᵀ *ᵥ v) := by
  have hL : ∀ k j, σ (blockSel K 5 2 i k j) = blockSel K 5 2 i k j := by
    intro k j
    simp only [blockSel_apply]
    split_ifs <;> simp
  simp only [herm, extVec, Matrix.mulVec, dotProduct, map_sum, map_mul, hL,
    Matrix.transpose_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  ring

theorem herm_extVec_self {i : ℕ} (hi : i + 2 ≤ 5) (a : Fin 2 → K) :
    herm σ (extVec i a) (extVec i a) = herm σ a a := by
  rw [herm_extVec_left, extVec, Matrix.mulVec_mulVec, blockSel_transpose_mul_self hi,
    Matrix.one_mulVec]

omit [Finite K] [CharP K 2] in
theorem blockMat_mulVec (i : ℕ) (A : Matrix (Fin 2) (Fin 2) K) (v : Fin 5 → K) :
    blockMat 5 i A *ᵥ v = v + blockSel K 5 2 i *ᵥ ((A - 1) *ᵥ ((blockSel K 5 2 i)ᵀ *ᵥ v)) := by
  rw [blockMat, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]

theorem blockEmb2_eq_tv (hσ : ∀ c : K, σ (σ c) = c) (i : Fin 4) {a : Fin 2 → K} {c : K}
    (ha : herm σ a a = 0) (hc : c + σ c = 0) (g : Su K 2 f 2)
    (hg : ∀ v, g • v = v + (c * herm σ a v) • a) :
    blockEmb2 K 2 f 4 i g =
      tv hσ (show herm σ (extVec (i : ℕ) a) (extVec (i : ℕ) a) = 0 by
        rw [herm_extVec_self (by omega)]; exact ha) hc := by
  apply ext_smul
  intro v
  rw [tv_smul, smul_def]
  show blockMat 5 (i : ℕ) ((g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ v = _
  rw [blockMat_mulVec]
  have hA : ∀ w : Fin 2 → K,
      (((g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) - 1) *ᵥ w = (c * herm σ a w) • a := by
    intro w
    have := hg w
    rw [smul_def] at this
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, this]
    abel
  rw [hA, Matrix.mulVec_smul, herm_extVec_left]
  rfl

theorem range_blockEmb2_le (hσ : ∀ c : K, σ (σ c) = c) (hσi : IsUnitaryInvolution σ)
    (M : Subgroup (SUid σ 5)) (i : Fin 4)
    (hi : ∀ a : Fin 2 → K, herm σ a a = 0 → extVec (i : ℕ) a ∈ Cset hσ M) :
    (blockEmb2 K 2 f 4 i).range ≤ M := by
  have hT : T σ 2 ≤ M.comap (blockEmb2 K 2 f 4 i) := by
    rw [T, Subgroup.closure_le]
    rintro g ⟨a, c, ha, hc, hg⟩
    obtain ⟨_, hcm⟩ := hi a ha
    rw [SetLike.mem_coe, Subgroup.mem_comap, blockEmb2_eq_tv hσ i ha hc g hg]
    exact hcm c hc
  rintro _ ⟨g, rfl⟩
  have : g ∈ T σ 2 := by rw [T_two_eq_top hσi]; trivial
  exact hT this

theorem shiftSU_smul (v : Fin 5 → K) : shiftSU σ • v = fun i => v (i - 1) := by
  show Equiv.Perm.permMatrix K (finRotate 5)⁻¹ *ᵥ v = _
  ext i
  simp [Matrix.mulVec, dotProduct, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]

theorem shiftSU_smul' (v : Fin 5 → K) : shiftSU σ • v = ![v 4, v 0, v 1, v 2, v 3] := by
  rw [shiftSU_smul]
  ext i
  fin_cases i <;> rfl

omit [Finite K] [CharP K 2] in
theorem extVec_eq (i : ℕ) (a : Fin 2 → K) (k : Fin 5) :
    extVec i a k = if (k : ℕ) = i then a 0 else if (k : ℕ) = i + 1 then a 1 else 0 := by
  simp only [extVec, Matrix.mulVec, dotProduct, Fin.sum_univ_two, blockSel_apply, Fin.val_zero,
    Fin.val_one]
  by_cases h0 : (k : ℕ) = i
  · simp [h0]
  · by_cases h1 : (k : ℕ) = i + 1
    · simp [h1]
    · simp [h0, h1]

theorem shift_extVec (i : Fin 3) (a : Fin 2 → K) :
    shiftSU σ • extVec (i : ℕ) a = extVec ((i : ℕ) + 1) a := by
  rw [shiftSU_smul']
  ext k
  simp only [extVec_eq]
  fin_cases i <;> fin_cases k <;> simp

theorem shift_shift_extVec_three (a : Fin 2 → K) :
    shiftSU σ • (shiftSU σ • extVec 3 a) = extVec 0 a := by
  rw [shiftSU_smul', shiftSU_smul']
  ext k
  simp only [extVec_eq]
  fin_cases k <;> simp

omit [Finite K] in
theorem two_eq_zero : (2 : K) = 0 := CharP.cast_eq_zero K 2

theorem eq_top_of_ext3_shift (hK : Nat.card K = (2 ^ f) ^ 2) (hq : 2 ^ f ≠ 2)
    (M : Subgroup (SUid σ 5))
    (hext3 : ∀ a : Fin 2 → K, herm σ a a = 0 →
      extVec 3 a ∈ Cset (unitaryInvolution_involutive hK) M)
    (hS : ∀ x ∈ M, shiftSU σ * x * (shiftSU σ)⁻¹ ∈ M) : M = ⊤ := by
  have hσ : ∀ c : K, σ (σ c) = c := unitaryInvolution_involutive hK
  have hσi : IsUnitaryInvolution σ := isUnitaryInvolution_unitaryInvolution (p := 2) (f := f) hK
  have hshift : ∀ {v : Fin 5 → K}, v ∈ Cset hσ M → shiftSU σ • v ∈ Cset hσ M :=
    fun hv => Cset_conj hσ M _ hS hv
  have hext0 : ∀ a : Fin 2 → K, herm σ a a = 0 → extVec 0 a ∈ Cset hσ M := by
    intro a ha
    rw [← shift_shift_extVec_three]
    exact hshift (hshift (hext3 a ha))
  have hext1 : ∀ a : Fin 2 → K, herm σ a a = 0 → extVec 1 a ∈ Cset hσ M := by
    intro a ha
    have := shift_extVec (K := K) (f := f) (0 : Fin 3) a
    simp only [Fin.val_zero, zero_add] at this
    rw [← this]
    exact hshift (hext0 a ha)
  have hext2 : ∀ a : Fin 2 → K, herm σ a a = 0 → extVec 2 a ∈ Cset hσ M := by
    intro a ha
    have := shift_extVec (K := K) (f := f) (1 : Fin 3) a
    simp only [Fin.val_one] at this
    rw [← this]
    exact hshift (hext1 a ha)
  rw [eq_top_iff, ← iSup_range_blockEmb2 (K := K) (p := 2) (f := f) hK hq 4]
  refine iSup_le fun i => range_blockEmb2_le hσ hσi M i ?_
  fin_cases i
  · exact hext0
  · exact hext1
  · exact hext2
  · exact hext3

theorem eq_top_of_diag_circ_shift (hK : Nat.card K = (2 ^ f) ^ 2) (hf : 6 ≤ f)
    (h5 : 5 ∣ 2 ^ f + 1) (M : Subgroup (SUid σ 5))
    (hD : ∀ (t : Fin 5 → K) (ht : ∀ i, σ (t i) * t i = 1) (hdet : ∏ i, t i = 1),
      dgSU σ t ht hdet ∈ M)
    (hC : ∀ (η : K) (hη : σ η * η = 1), kSU σ (two_eq_zero (K := K)) η hη ∈ M)
    (hS : ∀ x ∈ M, shiftSU σ * x * (shiftSU σ)⁻¹ ∈ M) : M = ⊤ := by
  have h2 : (2 : K) = 0 := two_eq_zero
  have hσ : ∀ c : K, σ (σ c) = c := unitaryInvolution_involutive hK
  have hσi : IsUnitaryInvolution σ := isUnitaryInvolution_unitaryInvolution (p := 2) (f := f) hK
  have hDh : ∀ (γ : K) (hγ : σ γ * γ = 1), hSU σ γ hγ ∈ M := fun γ hγ => hD _ _ _
  have hy : (yVec : Fin 5 → K) ∈ Cset hσ M :=
    ⟨herm_yVec σ h2, fun c hc => tv_mem_y hK hf h5 h2 M hDh hC hc⟩
  have hDτ : ∀ (τ : K) (hτ : σ τ * τ = 1), dgTau τ hτ ∈ M := fun τ hτ => hD _ _ _
  have hq : 2 ^ f ≠ 2 := by
    have : 2 ^ 6 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
    omega
  refine eq_top_of_ext3_shift hK hq M (fun a ha => ?_) hS
  have e : extVec 3 a = ![0, 0, 0, a 0, a 1] := by
    ext k
    fin_cases k <;> simp [extVec_eq]
  rw [e]
  refine plane_all hσ hσi h2 M hDτ hy (a 0) (a 1) ?_
  simp only [herm, Fin.sum_univ_two] at ha
  linear_combination ha - (σ (a 1) * a 1) * h2

end Plane

end CFSG.RankThree.PartOne.CTP.U5Gen
