module

public import CFSG.Quasithin.Background.SimsF5Defs2
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutIface

public section

namespace CFSG.Quasithin.SimsF5

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open Matrix CFSG.Open CFSG.Fischer CFSG.Fischer.Classification.Beta U42F431
open CFSG.ComponentClassification.CatFactsSmall.PSp43
open scoped Pointwise

local instance (priority := high) mkDecEqF4 : DecidableEq F4 := fun a b =>
  decidable_of_iff (a.code = b.code) (by cases a; cases b; simp)

@[expose] def mkTp (i j : ℕ) : ℕ := (tpLit.getD i []).getD j 0

theorem mk_tab : ∀ i j : Fin 45, (tauFun i j).val = mkTp i j := by
  decide +kernel

@[expose] def mkFL : List ℕ :=
  [0, 2, 1, 3, 5, 4, 6, 8, 7, 9, 11, 10, 12, 14, 13, 15, 16, 18, 17, 22, 24, 23, 19, 21, 20, 35,
    36, 38, 37, 42, 44, 43, 39, 41, 40, 25, 26, 28, 27, 32, 34, 33, 29, 31, 30]

theorem mk_x_tab : ∀ m : Fin 45, (x45 m).val = xL.getD m 0 := by decide +kernel

theorem mk_y_tab : ∀ m : Fin 45, (y45 m).val = yL.getD m 0 := by decide +kernel

theorem mk_f_tab : ∀ m : Fin 45, (f45 m).val = mkFL.getD m 0 := by decide +kernel

theorem mk_q_x : ∀ j k : Fin 45, xL.getD (mkTp j k) 0 = mkTp (xL.getD j 0) (xL.getD k 0) := by
  decide +kernel

theorem mk_q_y : ∀ j k : Fin 45, yL.getD (mkTp j k) 0 = mkTp (yL.getD j 0) (yL.getD k 0) := by
  decide +kernel

theorem mk_q_f : ∀ j k : Fin 45,
    mkFL.getD (mkTp j k) 0 = mkTp (mkFL.getD j 0) (mkFL.getD k 0) := by
  decide +kernel

theorem mk_tau_inj_aux : ∀ i j : Fin 45, mkTp i 0 = mkTp j 0 → mkTp i 1 = mkTp j 1 →
    mkTp i 3 = mkTp j 3 → i = j := by
  decide +kernel

theorem mk_tau_inj : ∀ i j : Fin 45, (∀ k : Fin 45, mkTp i k = mkTp j k) → i = j := by
  intro i j h
  exact mk_tau_inj_aux i j (h 0) (h 1) (h 3)

@[expose] def mkQ (g : Equiv.Perm (Fin 45)) : Prop :=
  ∀ j k : Fin 45, g (tauFun j k) = tauFun (g j) (g k)

theorem mkQ_mul {g h : Equiv.Perm (Fin 45)} (hg : mkQ g) (hh : mkQ h) : mkQ (g * h) := by
  intro j k
  simp only [Equiv.Perm.mul_apply]
  rw [hh, hg]

theorem mkQ_inv {g : Equiv.Perm (Fin 45)} (hg : mkQ g) : mkQ g⁻¹ := by
  intro j k
  have h := hg (g⁻¹ j) (g⁻¹ k)
  simp only [Equiv.Perm.coe_inv, Equiv.apply_symm_apply] at h
  rw [← h]
  simp

theorem mkQ_x : mkQ x45 := by
  intro j k
  apply Fin.ext
  simp only [mk_x_tab, mk_tab]
  exact mk_q_x j k

theorem mkQ_y : mkQ y45 := by
  intro j k
  apply Fin.ext
  simp only [mk_y_tab, mk_tab]
  exact mk_q_y j k

theorem mkQ_f : mkQ f45 := by
  intro j k
  apply Fin.ext
  simp only [mk_f_tab, mk_tab]
  exact mk_q_f j k

theorem mkQ_of_mem {a : Equiv.Perm (Fin 45)} (ha : a ∈ QA45.originalSubgroup) : mkQ a := by
  rw [QA45_closure] at ha
  induction ha using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl | rfl
    exacts [mkQ_x, mkQ_y, mkQ_f]
  | one => intro j k; rfl
  | mul x y _ _ hx hy => exact mkQ_mul hx hy
  | inv x _ hx => exact mkQ_inv hx

theorem mk_conj_tau {a : Equiv.Perm (Fin 45)} (ha : mkQ a) (j : Fin 45) :
    a * tauPerm j * a⁻¹ = tauPerm (a j) := by
  apply Equiv.ext
  intro k
  show a (tauFun j (a⁻¹ k)) = tauFun (a j) k
  rw [ha]
  simp

theorem mk_tauPerm_inj : Function.Injective tauPerm := by
  intro i j h
  apply mk_tau_inj
  intro k
  have h1 : (tauFun i k).val = (tauFun j k).val :=
    congrArg (fun p : Equiv.Perm (Fin 45) => (p k).val) h
  rw [mk_tab, mk_tab] at h1
  exact h1

theorem mk_vec_eta (v : Fin 4 → F4) : v = ![v 0, v 1, v 2, v 3] := by
  ext i
  fin_cases i <;> rfl

theorem mk_exists_smul {v : Fin 4 → F4} (hv : v ≠ 0) (hiso : hU v v = 0) :
    ∃ t : F4, t ≠ 0 ∧ v = t • uPt (uIdx v) := by
  have e := mk_vec_eta v
  have hv' : ![v 0, v 1, v 2, v 3] ≠ 0 := by rwa [← e]
  have hiso' : hU ![v 0, v 1, v 2, v 3] ![v 0, v 1, v 2, v 3] = 0 := by rwa [← e]
  obtain ⟨t, ht⟩ := exists_eq_smul_uPt _ _ _ _ hv' hiso'
  rw [← e] at ht
  refine ⟨t, ?_, ht⟩
  rintro rfl
  exact hv (by rw [ht, zero_smul])

theorem mk_cube : ∀ t : F4, t ≠ 0 → t * t * t = 1 := by decide +kernel

theorem mk_tU_smul (a b : Fin 4 → F4) {t : F4} (ht : t ≠ 0) : tU (t • a) b = tU a b := by
  have h3 := mk_cube t ht
  ext i
  simp only [tU, hU, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  linear_combination ((a 0 * a 0 * b 0 + a 1 * a 1 * b 1 + a 2 * a 2 * b 2 + a 3 * a 3 * b 3) *
    a i) * h3

theorem mk_tU_idx {q : Fin 4 → F4} (hq : q ≠ 0) (hiso : hU q q = 0) (j : Fin 45) :
    uIdx (tU q (uPt j)) = tauFun (uIdx q) j := by
  obtain ⟨t, ht0, ht⟩ := mk_exists_smul hq hiso
  unfold tauFun
  generalize uIdx q = i at ht ⊢
  rw [ht, mk_tU_smul _ _ ht0]

@[expose] def mkAct (A : Matrix (Fin 4) (Fin 4) F4) (j : Fin 45) : Fin 45 := uIdx (A *ᵥ uPt j)

theorem mk_su_unitary {A : GL (Fin 4) F4} (hA : A ∈ StatedSU 4 2 F4) :
    ((A : Matrix (Fin 4) (Fin 4) F4).map (fun x => x ^ 2))ᵀ * (A : Matrix (Fin 4) (Fin 4) F4) =
      1 := by
  have h := (CFSG.LinearGroups.unitary_scalar_kernel (K := F4) (p := 2) (f := 1) Nat.prime_two
    (by rw [Nat.card_eq_fintype_card, F4.card]; norm_num) (n := 4) (by norm_num)).1
  have h2 : A ∈ (StatedSU 4 (2 ^ 1) F4 : Set (GL (Fin 4) F4)) := hA
  rw [h] at h2
  exact h2.2

theorem mk_sq_mulVec (A : Matrix (Fin 4) (Fin 4) F4) (x : Fin 4 → F4) :
    (fun i => (A *ᵥ x) i ^ 2) = (A.map (fun t => t ^ 2)) *ᵥ (fun i => x i ^ 2) := by
  funext i
  have e : ⇑(frobenius F4 2) = fun t => t ^ 2 := funext fun t => rfl
  have h := RingHom.map_mulVec (frobenius F4 2) A x i
  rw [e] at h
  simpa [Function.comp_def] using h

theorem mk_hU_eq_dot (x y : Fin 4 → F4) : hU x y = (fun i => x i ^ 2) ⬝ᵥ y := by
  simp [hU, dotProduct, Fin.sum_univ_four, sq]

theorem mk_hU_mulVec {A : Matrix (Fin 4) (Fin 4) F4}
    (hA : (A.map (fun x => x ^ 2))ᵀ * A = 1) (x y : Fin 4 → F4) :
    hU (A *ᵥ x) (A *ᵥ y) = hU x y := by
  rw [mk_hU_eq_dot, mk_hU_eq_dot, mk_sq_mulVec, Matrix.dotProduct_mulVec,
    ← Matrix.vecMul_transpose, Matrix.vecMul_vecMul, hA, Matrix.vecMul_one]

theorem mk_uIdx_uPt (j : Fin 45) : uIdx (uPt j) = j := by
  simpa using uIdx_smul_uPt j 1 one_ne_zero

theorem mkAct_spec {A : GL (Fin 4) F4} (hA : A ∈ StatedSU 4 2 F4) (j : Fin 45) :
    ∃ t : F4, t ≠ 0 ∧
      (A : Matrix (Fin 4) (Fin 4) F4) *ᵥ uPt j =
        t • uPt (mkAct (A : Matrix (Fin 4) (Fin 4) F4) j) := by
  have hu := mk_su_unitary hA
  have hne : (A : Matrix (Fin 4) (Fin 4) F4) *ᵥ uPt j ≠ 0 := by
    intro h
    have h1 : uPt j = 0 := by
      have h2 := congrArg (fun v => ((A⁻¹ : GL (Fin 4) F4) : Matrix (Fin 4) (Fin 4) F4) *ᵥ v) h
      simpa [Matrix.mulVec_mulVec] using h2
    exact (uPt_spec j).1 h1
  have hiso : hU ((A : Matrix (Fin 4) (Fin 4) F4) *ᵥ uPt j)
      ((A : Matrix (Fin 4) (Fin 4) F4) *ᵥ uPt j) = 0 := by
    rw [mk_hU_mulVec hu]
    exact (uPt_spec j).2
  exact mk_exists_smul hne hiso

theorem mkAct_mul {A B : GL (Fin 4) F4} (hA : A ∈ StatedSU 4 2 F4) (hB : B ∈ StatedSU 4 2 F4)
    (j : Fin 45) :
    mkAct ((A * B : GL (Fin 4) F4) : Matrix (Fin 4) (Fin 4) F4) j =
      mkAct (A : Matrix (Fin 4) (Fin 4) F4) (mkAct (B : Matrix (Fin 4) (Fin 4) F4) j) := by
  obtain ⟨t, ht0, ht⟩ := mkAct_spec hB j
  obtain ⟨s, hs0, hs⟩ := mkAct_spec hA (mkAct (B : Matrix (Fin 4) (Fin 4) F4) j)
  have h : ((A * B : GL (Fin 4) F4) : Matrix (Fin 4) (Fin 4) F4) *ᵥ uPt j =
      (t * s) • uPt (mkAct (A : Matrix (Fin 4) (Fin 4) F4)
        (mkAct (B : Matrix (Fin 4) (Fin 4) F4) j)) := by
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, ht, Matrix.mulVec_smul, hs, smul_smul]
  show uIdx _ = _
  rw [h]
  exact uIdx_smul_uPt _ _ (mul_ne_zero ht0 hs0)

theorem mkAct_one (j : Fin 45) :
    mkAct ((1 : GL (Fin 4) F4) : Matrix (Fin 4) (Fin 4) F4) j = j := by
  simp only [mkAct, Units.val_one, Matrix.one_mulVec]
  exact mk_uIdx_uPt j

@[expose] def mkActHom : ↥(StatedSU 4 2 F4) →* Equiv.Perm (Fin 45) where
  toFun A :=
    { toFun := mkAct ((A : GL (Fin 4) F4) : Matrix (Fin 4) (Fin 4) F4)
      invFun := mkAct (((A⁻¹ : ↥(StatedSU 4 2 F4)) : GL (Fin 4) F4) : Matrix (Fin 4) (Fin 4) F4)
      left_inv := fun j => by
        rw [← mkAct_mul (A⁻¹).2 A.2, ← Subgroup.coe_mul, inv_mul_cancel]
        exact mkAct_one j
      right_inv := fun j => by
        rw [← mkAct_mul A.2 (A⁻¹).2, ← Subgroup.coe_mul, mul_inv_cancel]
        exact mkAct_one j }
  map_one' := Equiv.ext fun j => mkAct_one j
  map_mul' A B := Equiv.ext fun j => mkAct_mul A.2 B.2 j

theorem mkAct_scalar (c : F4ˣ) (j : Fin 45) :
    mkAct ((Matrix.GeneralLinearGroup.scalar (Fin 4) c : GL (Fin 4) F4) :
      Matrix (Fin 4) (Fin 4) F4) j = j := by
  have h : ((Matrix.GeneralLinearGroup.scalar (Fin 4) c : GL (Fin 4) F4) :
      Matrix (Fin 4) (Fin 4) F4) *ᵥ uPt j = (c : F4) • uPt j := by
    rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
    ext i
    simp [Matrix.mulVec_diagonal]
  show uIdx _ = j
  rw [h]
  exact uIdx_smul_uPt j _ c.ne_zero

theorem mk_scalars_le_ker :
    (StatedScalars (Fin 4) F4).subgroupOf (StatedSU 4 2 F4) ≤ mkActHom.ker := by
  intro A hA
  rw [Subgroup.mem_subgroupOf] at hA
  obtain ⟨c, hc⟩ := MonoidHom.mem_range.1 hA
  rw [MonoidHom.mem_ker]
  apply Equiv.ext
  intro j
  show mkAct _ j = j
  rw [← hc]
  exact mkAct_scalar c j

@[expose] def mkActProj : StatedProj (StatedSU 4 2 F4) →* Equiv.Perm (Fin 45) :=
  QuotientGroup.lift _ mkActHom mk_scalars_le_ker

theorem mk_card_P :
    Nat.card QP45.originalSubgroup = 25920 := by
  rw [← CFSG.Certificates.RawSchreierDatum.orderCertificate_eq_card _ QP45_ok]
  exact QP45_valid.2

theorem mk_card_A :
    Nat.card QA45.originalSubgroup = 51840 := by
  rw [← CFSG.Certificates.RawSchreierDatum.orderCertificate_eq_card _ QA45_ok]
  exact QA45_valid.2

section Transport

variable {K : Type} [Field K]

@[expose] noncomputable def mkRho (φ : K ≃+* F4) {G : Type} [Group G]
    (m : G ≃* StatedProj (StatedSU 4 2 K)) : G →* Equiv.Perm (Fin 45) :=
  mkActProj.comp ((CFSG.Open.StatedSUFieldChange.statedProjSUEquiv φ 4 2).toMonoidHom.comp
    m.toMonoidHom)

theorem mkRho_mk (φ : K ≃+* F4) {G : Type} [Group G] (m : G ≃* StatedProj (StatedSU 4 2 K))
    (x : G) (M : ↥(StatedSU 4 2 K)) (h : m x = QuotientGroup.mk M) (j : Fin 45) :
    mkRho φ m x j = uIdx (((M : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map φ *ᵥ uPt j) := by
  show mkActProj (CFSG.Open.StatedSUFieldChange.statedProjSUEquiv φ 4 2 (m x)) j = _
  rw [h]
  rfl

theorem mk_K_two (φ : K ≃+* F4) : (2 : K) = 0 := by
  apply φ.injective
  rw [map_ofNat, map_zero]
  exact F4.two_eq_zero

theorem mk_K_sq_sq (φ : K ≃+* F4) (x : K) : (x ^ 2) ^ 2 = x := by
  apply φ.injective
  simp only [map_pow]
  exact F4.sq_sq (φ x)

theorem mk_hU_map (φ : K ≃+* F4) (v w : Fin 4 → K) :
    φ (U42Hermitian K v w) = hU (fun i => φ (v i)) (fun i => φ (w i)) := by
  simp [U42Hermitian, hU, Fin.sum_univ_four, map_pow, sq]

@[expose] def mkTrvMat (σ : K →+* K) (p : Fin 4 → K) : Matrix (Fin 4) (Fin 4) K :=
  1 + Matrix.vecMulVec p (σ ∘ p)

theorem mk_dot_eq {σ : K →+* K} (hσ : ∀ x, σ x = x ^ 2) (p : Fin 4 → K) :
    (σ ∘ p) ⬝ᵥ p = U42Hermitian K p p := by
  simp [U42Hermitian, dotProduct, hσ]

theorem mkTrvMat_mul_self {σ : K →+* K} (hσ : ∀ x, σ x = x ^ 2) (hK2 : (2 : K) = 0)
    {p : Fin 4 → K} (hp : U42Hermitian K p p = 0) : mkTrvMat σ p * mkTrvMat σ p = 1 := by
  have hq : (σ ∘ p) ⬝ᵥ p = 0 := by rw [mk_dot_eq hσ, hp]
  have hAA : Matrix.vecMulVec p (σ ∘ p) * Matrix.vecMulVec p (σ ∘ p) = 0 := by
    rw [Matrix.vecMulVec_mul_vecMulVec, hq, zero_smul, Matrix.vecMulVec_zero]
  have hA2 : Matrix.vecMulVec p (σ ∘ p) + Matrix.vecMulVec p (σ ∘ p) = 0 := by
    rw [← two_smul K, hK2, zero_smul]
  unfold mkTrvMat
  calc (1 + Matrix.vecMulVec p (σ ∘ p)) * (1 + Matrix.vecMulVec p (σ ∘ p))
      = 1 + (Matrix.vecMulVec p (σ ∘ p) + Matrix.vecMulVec p (σ ∘ p)) +
        Matrix.vecMulVec p (σ ∘ p) * Matrix.vecMulVec p (σ ∘ p) := by noncomm_ring
    _ = 1 := by rw [hA2, hAA]; simp

theorem mkTrvMat_map_transpose {σ : K →+* K} (hσσ : ∀ x, σ (σ x) = x) (p : Fin 4 → K) :
    ((mkTrvMat σ p).map σ)ᵀ = mkTrvMat σ p := by
  ext i j
  by_cases h : i = j
  · subst h
    simp [mkTrvMat, Matrix.vecMulVec_apply, hσσ, mul_comm]
  · simp [mkTrvMat, Matrix.vecMulVec_apply, hσσ, mul_comm, h, Ne.symm h]

theorem mkTrvMat_det {σ : K →+* K} (hσ : ∀ x, σ x = x ^ 2) (hK2 : (2 : K) = 0)
    {p : Fin 4 → K} (hp : U42Hermitian K p p = 0) : (mkTrvMat σ p).det = 1 := by
  have h := congrArg Matrix.det (mkTrvMat_mul_self hσ hK2 hp)
  rw [Matrix.det_mul, Matrix.det_one] at h
  rcases mul_self_eq_one_iff.1 h with h1 | h1
  · exact h1
  · rw [h1]
    linear_combination (-1 : K) * hK2

@[expose] def mkTrvGL {σ : K →+* K} (hσ : ∀ x, σ x = x ^ 2) (hK2 : (2 : K) = 0)
    {p : Fin 4 → K} (hp : U42Hermitian K p p = 0) : GL (Fin 4) K :=
  ⟨mkTrvMat σ p, mkTrvMat σ p, mkTrvMat_mul_self hσ hK2 hp, mkTrvMat_mul_self hσ hK2 hp⟩

theorem mkTrvGL_mem {σ : K →+* K} (hσ : ∀ x, σ x = x ^ 2) (hσσ : ∀ x, σ (σ x) = x)
    (hK2 : (2 : K) = 0) {p : Fin 4 → K} (hp : U42Hermitian K p p = 0) :
    mkTrvGL hσ hK2 hp ∈ StatedSU 4 2 K := by
  refine Subgroup.subset_closure ⟨mkTrvMat_det hσ hK2 hp, ?_⟩
  show ((mkTrvMat σ p).map (fun x => x ^ 2))ᵀ * mkTrvMat σ p = 1
  have h : (fun x : K => x ^ 2) = σ := funext fun x => (hσ x).symm
  rw [h, mkTrvMat_map_transpose hσσ, mkTrvMat_mul_self hσ hK2 hp]

theorem mkTrvMat_act (φ : K ≃+* F4) {σ : K →+* K} (hσ : ∀ x, σ x = x ^ 2) (p : Fin 4 → K)
    (w : Fin 4 → F4) :
    ((mkTrvMat σ p).map φ) *ᵥ w = tU (fun i => φ (p i)) w := by
  ext i
  fin_cases i <;>
  · simp [tU, hU, mkTrvMat, Matrix.mulVec, dotProduct, Fin.sum_univ_four, Matrix.one_apply,
      Matrix.vecMulVec_apply, hσ, map_pow, sq]
    try ring

@[expose] def mkXi (φ : K ≃+* F4) (j : Fin 45) : Fin 4 → K := fun i => φ.symm (uPt j i)

theorem mkXi_map (φ : K ≃+* F4) (j : Fin 45) : (fun i => φ (mkXi φ j i)) = uPt j := by
  funext i
  simp [mkXi]

theorem mkXi_iso (φ : K ≃+* F4) (j : Fin 45) : U42Hermitian K (mkXi φ j) (mkXi φ j) = 0 := by
  apply φ.injective
  rw [mk_hU_map, mkXi_map, map_zero]
  exact (uPt_spec j).2

theorem mk_exists_rho_tau (φ : K ≃+* F4) {σ : K →+* K} (hσ : ∀ x, σ x = x ^ 2)
    (hσσ : ∀ x, σ (σ x) = x) {G : Type} [Group G] (m : G ≃* StatedProj (StatedSU 4 2 K))
    (j : Fin 45) : ∃ g : G, mkRho φ m g = tauPerm j := by
  have hK2 := mk_K_two φ
  let M : ↥(StatedSU 4 2 K) :=
    ⟨mkTrvGL hσ hK2 (mkXi_iso φ j), mkTrvGL_mem hσ hσσ hK2 (mkXi_iso φ j)⟩
  refine ⟨m.symm (QuotientGroup.mk M), ?_⟩
  apply Equiv.ext
  intro k
  rw [mkRho_mk φ m _ M (by simp)]
  show _ = tauFun j k
  show uIdx (((mkTrvMat σ (mkXi φ j)).map φ) *ᵥ uPt k) = _
  rw [mkTrvMat_act φ hσ, mkXi_map]
  rfl

end Transport

theorem mk_range_eq {G : Type} [Group G] [Finite G]
    (hcard : Nat.card G = 25920) (ρ : G →* Equiv.Perm (Fin 45))
    (htau : ∀ j : Fin 45, ∃ g : G, ρ g = tauPerm j) :
    ρ.range = QP45.originalSubgroup ∧ Function.Injective ρ := by
  have hle : QP45.originalSubgroup ≤ ρ.range := by
    rw [QP45_closure, Subgroup.closure_le]
    have h1 : ∀ j, tauPerm j ∈ ρ.range := fun j => by
      obtain ⟨g, hg⟩ := htau j
      exact ⟨g, hg⟩
    rintro g (rfl | rfl)
    · exact h1 0
    · exact mul_mem (mul_mem (mul_mem (h1 31) (h1 5)) (h1 36)) (h1 44)
  have hsurj : Function.Surjective ρ.rangeRestrict := ρ.rangeRestrict_surjective
  have hcard2 : Nat.card ρ.range ≤ 25920 := by
    rw [← hcard]
    exact Nat.card_le_card_of_surjective _ hsurj
  have hP : Nat.card QP45.originalSubgroup = 25920 := mk_card_P
  have heq : QP45.originalSubgroup = ρ.range :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hP]; exact hcard2)
  refine ⟨heq.symm, ?_⟩
  have hc3 : Nat.card ρ.range = 25920 := by
    apply le_antisymm hcard2
    rw [← hP, heq]
  have hbij : Function.Bijective ρ.rangeRestrict :=
    hsurj.bijective_of_nat_card_le (by rw [hcard, hc3])
  intro a b hab
  exact hbij.1 (Subtype.ext hab)

theorem mk_aut_real :
    ∃ Ψ : MulAut ↥QP45.originalSubgroup ≃* ↥QA45.originalSubgroup,
      ∀ (α : MulAut ↥QP45.originalSubgroup) (z : ↥QP45.originalSubgroup),
        ((α z : ↥QP45.originalSubgroup) : Equiv.Perm (Fin 45)) =
          ((Ψ α : ↥QA45.originalSubgroup) : Equiv.Perm (Fin 45)) * (z : Equiv.Perm (Fin 45)) *
            ((Ψ α : ↥QA45.originalSubgroup) : Equiv.Perm (Fin 45))⁻¹ := by
  obtain ⟨⟨P', A', e', Φ, spec⟩, hP, hA⟩ :=
    exists_model (K := ↥QP45.originalSubgroup) (MulEquiv.refl _)
  dsimp only at hP hA
  subst hP hA
  refine ⟨(MulAut.congr e'.symm).trans Φ, fun α z => ?_⟩
  have h := spec (MulAut.congr e'.symm α) (e'.symm z)
  simpa [MulAut.congr_apply] using h

theorem mk_P_le_A : QP45.originalSubgroup ≤ QA45.originalSubgroup := by
  rw [QP45_closure, QA45_closure]
  exact Subgroup.closure_mono (by intro g hg; rcases hg with rfl | rfl <;> simp)

theorem mk_exists_theta {E : Type} [Group E] [Finite E]
    {Gp : Subgroup E} [Gp.Normal] (hcent : Subgroup.centralizer (Gp : Set E) = ⊥)
    (hne : Gp ≠ ⊤) (hGp : Nat.card Gp = 25920) (ψ : ↥Gp ≃* ↥QP45.originalSubgroup) :
    ∃ Θ : E ≃* ↥QA45.originalSubgroup,
      (∀ (x : E) (g : ↥Gp), ((Θ x : ↥QA45.originalSubgroup) : Equiv.Perm (Fin 45)) *
          ((ψ g : ↥QP45.originalSubgroup) : Equiv.Perm (Fin 45)) *
            ((Θ x : ↥QA45.originalSubgroup) : Equiv.Perm (Fin 45))⁻¹ =
          ((ψ (MulAut.conjNormal x g) : ↥QP45.originalSubgroup) : Equiv.Perm (Fin 45))) ∧
      (∀ g : ↥Gp, ((Θ (g : E) : ↥QA45.originalSubgroup) : Equiv.Perm (Fin 45)) =
          ((ψ g : ↥QP45.originalSubgroup) : Equiv.Perm (Fin 45))) ∧
      (∀ x : E, ((Θ x : ↥QA45.originalSubgroup) : Equiv.Perm (Fin 45)) ∈
          QP45.originalSubgroup ↔ x ∈ Gp) := by
  obtain ⟨Ψ, hΨ⟩ := mk_aut_real
  let Θ₀ : E →* ↥QA45.originalSubgroup :=
    Ψ.toMonoidHom.comp ((MulAut.congr ψ).toMonoidHom.comp MulAut.conjNormal)
  have hspec : ∀ (x : E) (g : ↥Gp), ((Θ₀ x : ↥QA45.originalSubgroup) : Equiv.Perm (Fin 45)) *
      ((ψ g : ↥QP45.originalSubgroup) : Equiv.Perm (Fin 45)) *
        ((Θ₀ x : ↥QA45.originalSubgroup) : Equiv.Perm (Fin 45))⁻¹ =
      ((ψ (MulAut.conjNormal x g) : ↥QP45.originalSubgroup) : Equiv.Perm (Fin 45)) := by
    intro x g
    have h := hΨ (MulAut.congr ψ (MulAut.conjNormal x)) (ψ g)
    simpa [Θ₀, MulAut.congr_apply] using h.symm
  have hinj : Function.Injective Θ₀ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hxc : x ∈ Subgroup.centralizer (Gp : Set E) := by
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      have h1 := hspec x ⟨g, hg⟩
      rw [hx] at h1
      have h2 : ψ ⟨g, hg⟩ = ψ (MulAut.conjNormal x ⟨g, hg⟩) := by
        apply Subtype.ext
        simpa using h1
      have h3 := congrArg Subtype.val (ψ.injective h2)
      rw [MulAut.conjNormal_apply] at h3
      have h4 : g * x = x * g := by
        calc g * x = (x * g * x⁻¹) * x := by rw [← h3]
          _ = x * g := by group
      exact h4
    rw [hcent] at hxc
    exact Subgroup.mem_bot.1 hxc
  have hE : 51840 ≤ Nat.card E := by
    have h1 := Subgroup.index_mul_card Gp
    have h2 : Gp.index ≠ 1 := fun h => hne (Subgroup.index_eq_one.1 h)
    have h3 : Gp.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    rw [hGp] at h1
    omega
  have hbij : Function.Bijective Θ₀ :=
    hinj.bijective_of_nat_card_le (by rw [mk_card_A]; exact hE)
  have hconj : ∀ (σ : ↥QA45.originalSubgroup) (z : ↥QP45.originalSubgroup),
      ((Ψ.symm σ z : ↥QP45.originalSubgroup) : Equiv.Perm (Fin 45)) =
        (σ : Equiv.Perm (Fin 45)) * (z : Equiv.Perm (Fin 45)) * (σ : Equiv.Perm (Fin 45))⁻¹ := by
    intro σ z
    have h := hΨ (Ψ.symm σ) z
    rw [MulEquiv.apply_symm_apply] at h
    exact h
  have hagree : ∀ g : ↥Gp, ((Θ₀ (g : E) : ↥QA45.originalSubgroup) : Equiv.Perm (Fin 45)) =
      ((ψ g : ↥QP45.originalSubgroup) : Equiv.Perm (Fin 45)) := by
    intro g₀
    have hψA : ((ψ g₀ : ↥QP45.originalSubgroup) : Equiv.Perm (Fin 45)) ∈
        QA45.originalSubgroup := mk_P_le_A (ψ g₀).2
    set σ : ↥QA45.originalSubgroup := ⟨_, hψA⟩ with hσ
    have hΘσ : Θ₀ (g₀ : E) = σ := by
      apply Ψ.symm.injective
      apply MulEquiv.ext
      intro z
      apply Subtype.ext
      rw [hconj, hconj]
      obtain ⟨g, rfl⟩ := ψ.surjective z
      have h1 := hspec (g₀ : E) g
      have h2 : MulAut.conjNormal (g₀ : E) g = g₀ * g * g₀⁻¹ := by
        apply Subtype.ext
        rw [MulAut.conjNormal_apply]
        simp
      rw [h1, h2]
      simp [hσ]
    rw [hΘσ]
  refine ⟨MulEquiv.ofBijective Θ₀ hbij, hspec, hagree, fun x => ?_⟩
  constructor
  · intro hx
    obtain ⟨g, hg⟩ := ψ.surjective ⟨((Θ₀ x : ↥QA45.originalSubgroup) : Equiv.Perm (Fin 45)), hx⟩
    have h1 := hagree g
    have h2 : Θ₀ (g : E) = Θ₀ x := by
      apply Subtype.ext
      rw [h1]
      exact congrArg Subtype.val hg
    have h3 := hinj h2
    rw [← h3]
    exact g.2
  · intro hx
    have h1 := hagree ⟨x, hx⟩
    show ((Θ₀ x : ↥QA45.originalSubgroup) : Equiv.Perm (Fin 45)) ∈ _
    rw [show ((Θ₀ x : ↥QA45.originalSubgroup) : Equiv.Perm (Fin 45)) =
      ((ψ ⟨x, hx⟩ : ↥QP45.originalSubgroup) : Equiv.Perm (Fin 45)) from h1]
    exact (ψ ⟨x, hx⟩).2

theorem mk_lnTab_lt : ∀ m : Fin 27, ∀ r : Fin 5, (lnTab.getD m []).getD r 0 < 45 := by
  decide +kernel

@[expose] def mkLn (m : Fin 27) (r : Fin 5) : Fin 45 :=
  ⟨(lnTab.getD m []).getD r 0, mk_lnTab_lt m r⟩

theorem mk_mem_line : ∀ m : Fin 27, ∀ j : Fin 45, j.val ∈ lnTab.getD m [] →
    ∃ r : Fin 5, mkLn m r = j := by
  decide +kernel

theorem mk_hU_tau {a b : Fin 45} (h : hU (uPt a) (uPt b) = 0) : mkTp a b = b := by
  have h1 : tauFun a b = b := by
    unfold tauFun tU
    rw [h, zero_smul, add_zero, mk_uIdx_uPt]
  have h2 := mk_tab a b
  rw [h1] at h2
  exact h2.symm

theorem mk_coll_line : ∀ a b : Fin 45, a ≠ b → mkTp a b = b →
    ∃ m : Fin 27, a.val ∈ lnTab.getD m [] ∧ b.val ∈ lnTab.getD m [] := by
  decide +kernel

theorem mk_add_sq : ∀ a b : F4, (a + b) ^ 2 = a ^ 2 + b ^ 2 := by decide +kernel

theorem mk_pow4 : ∀ t : F4, t ^ 4 = t := by decide +kernel

theorem mk_hU_swap (x y : Fin 4 → F4) : hU y x = (hU x y) ^ 2 := by
  simp only [hU]
  rw [mk_add_sq, mk_add_sq, mk_add_sq]
  have f0 := mk_pow4 (x 0)
  have f1 := mk_pow4 (x 1)
  have f2 := mk_pow4 (x 2)
  have f3 := mk_pow4 (x 3)
  linear_combination (-(y 0) ^ 2) * f0 + (-(y 1) ^ 2) * f1 + (-(y 2) ^ 2) * f2 +
    (-(y 3) ^ 2) * f3

theorem mk_hU_comb {u v : Fin 4 → F4} (huu : hU u u = 0) (hvv : hU v v = 0) (huv : hU u v = 0)
    (e : F4) : hU (u + e • v) (u + e • v) = 0 := by
  have hvu : hU v u = 0 := by
    rw [mk_hU_swap, huv]
    simp
  simp only [hU, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at huu hvv huv hvu ⊢
  linear_combination huu + 3 * e * huv + 3 * e ^ 2 * hvu + e ^ 3 * hvv

theorem mk_comb_ne {a b : Fin 45} (hab : a ≠ b) (e : F4) : uPt a + e • uPt b ≠ 0 := by
  intro h
  have h1 : uPt a = e • uPt b := by
    funext i
    have h2 := congrFun h i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h2 ⊢
    exact CharTwo.add_eq_zero.1 h2
  have he : e ≠ 0 := by
    rintro rfl
    simp only [zero_smul] at h1
    exact (uPt_spec a).1 h1
  apply hab
  have h2 := uIdx_smul_uPt b e he
  rw [← h1, mk_uIdx_uPt] at h2
  exact h2

theorem mk_comb_iso {a b : Fin 45} (hab : a ≠ b) (hort : hU (uPt a) (uPt b) = 0) (e : F4) :
    uPt a + e • uPt b ≠ 0 ∧ hU (uPt a + e • uPt b) (uPt a + e • uPt b) = 0 :=
  ⟨mk_comb_ne hab e, mk_hU_comb (uPt_spec a).2 (uPt_spec b).2 hort e⟩

theorem mk_line_sub : ∀ m : Fin 27, ∀ r s : Fin 5, r ≠ s → ∀ e : F4,
    (uIdx (uPt (mkLn m r) + e • uPt (mkLn m s))).val ∈ lnTab.getD m [] := by
  decide +kernel

theorem mk_line_sup : ∀ m : Fin 27, ∀ r s : Fin 5, r ≠ s → ∀ t : Fin 5,
    mkLn m t = mkLn m r ∨ mkLn m t = mkLn m s ∨
      ∃ e : F4, e ≠ 0 ∧ uIdx (uPt (mkLn m r) + e • uPt (mkLn m s)) = mkLn m t := by
  decide +kernel

theorem mk_line_set {a b : Fin 45} (hab : a ≠ b) (hort : hU (uPt a) (uPt b) = 0) :
    ∃ m : Fin 27, ∀ k : Fin 45,
      (∃ c d : F4, uPt k = c • uPt a + d • uPt b) ↔ k.val ∈ lnTab.getD m [] := by
  obtain ⟨m, ha, hb⟩ := mk_coll_line a b hab (mk_hU_tau hort)
  obtain ⟨r, hr⟩ := mk_mem_line m a ha
  obtain ⟨s, hs⟩ := mk_mem_line m b hb
  have hrs : r ≠ s := fun h => hab (by rw [← hr, ← hs, h])
  have hsub := fun e => mk_line_sub m r s hrs e
  have hsup := fun t => mk_line_sup m r s hrs t
  rw [hr, hs] at hsub hsup
  refine ⟨m, fun k => ⟨?_, ?_⟩⟩
  · rintro ⟨c, d, h⟩
    by_cases hd : d = 0
    · subst hd
      simp only [zero_smul, add_zero] at h
      have hc : c ≠ 0 := by
        rintro rfl
        simp only [zero_smul] at h
        exact (uPt_spec k).1 h
      have h1 : k = a := by
        have h2 := uIdx_smul_uPt a c hc
        rw [← h, mk_uIdx_uPt] at h2
        exact h2
      rwa [h1]
    by_cases hc : c = 0
    · subst hc
      simp only [zero_smul, zero_add] at h
      have h1 : k = b := by
        have h2 := uIdx_smul_uPt b d hd
        rw [← h, mk_uIdx_uPt] at h2
        exact h2
      rwa [h1]
    · have h1 : uPt k = c • (uPt a + (d / c) • uPt b) := by
        rw [h, smul_add, smul_smul, mul_div_cancel₀ _ hc]
      have hk : k = uIdx (uPt a + (d / c) • uPt b) := by
        have h2 : uPt a + (d / c) • uPt b = c⁻¹ • uPt k := by
          rw [h1, smul_smul, inv_mul_cancel₀ hc, one_smul]
        rw [h2, uIdx_smul_uPt k _ (inv_ne_zero hc)]
      rw [hk]
      exact hsub (d / c)
  · intro hk
    obtain ⟨t, ht⟩ := mk_mem_line m k hk
    have hsup' := hsup t
    rw [ht] at hsup'
    rcases hsup' with rfl | rfl | ⟨e, he0, he⟩
    · exact ⟨1, 0, by simp⟩
    · exact ⟨0, 1, by simp⟩
    · obtain ⟨hw0, hwiso⟩ := mk_comb_iso hab hort e
      obtain ⟨t', ht0, ht'⟩ := mk_exists_smul hw0 hwiso
      rw [he] at ht'
      refine ⟨t'⁻¹, t'⁻¹ * e, ?_⟩
      have h1 : uPt k = t'⁻¹ • (uPt a + e • uPt b) := by
        rw [ht', smul_smul, inv_mul_cancel₀ ht0, one_smul]
      rw [h1, smul_add, smul_smul]

theorem mk_mulVec_inj {R : Type} [Field R] {A : GL (Fin 4) R} {u v : Fin 4 → R}
    (h : (A : Matrix (Fin 4) (Fin 4) R) *ᵥ u = (A : Matrix (Fin 4) (Fin 4) R) *ᵥ v) : u = v := by
  have h2 := congrArg (fun x => ((A⁻¹ : GL (Fin 4) R) : Matrix (Fin 4) (Fin 4) R) *ᵥ x) h
  simpa [Matrix.mulVec_mulVec] using h2

theorem mk_stab {A : GL (Fin 4) F4} (hA : A ∈ StatedSU 4 2 F4) {V : Set (Fin 4 → F4)}
    (h0 : (0 : Fin 4 → F4) ∈ V) (hs : ∀ c : F4, c ≠ 0 → ∀ w ∈ V, c • w ∈ V)
    (hiso : ∀ w ∈ V, hU w w = 0) (π : Equiv.Perm (Fin 45))
    (hπ : ∀ j, π j = mkAct (A : Matrix (Fin 4) (Fin 4) F4) j) :
    (∀ w, (A : Matrix (Fin 4) (Fin 4) F4) *ᵥ w ∈ V ↔ w ∈ V) ↔
      (π '' {k | uPt k ∈ V} = {k | uPt k ∈ V}) := by
  have hvec : ∀ w ∈ V, w ≠ 0 → ∃ k : Fin 45, uPt k ∈ V ∧ ∃ t : F4, t ≠ 0 ∧ w = t • uPt k := by
    intro w hw hw0
    obtain ⟨t, ht0, ht⟩ := mk_exists_smul hw0 (hiso w hw)
    refine ⟨uIdx w, ?_, t, ht0, ht⟩
    have h1 : uPt (uIdx w) = t⁻¹ • w := by
      conv_rhs => rw [ht]
      rw [smul_smul, inv_mul_cancel₀ ht0, one_smul]
    rw [h1]
    exact hs _ (inv_ne_zero ht0) w hw
  have hspec : ∀ k, ∃ t : F4, t ≠ 0 ∧
      (A : Matrix (Fin 4) (Fin 4) F4) *ᵥ uPt k = t • uPt (π k) := by
    intro k
    obtain ⟨t, ht0, ht⟩ := mkAct_spec hA k
    exact ⟨t, ht0, by rw [hπ]; exact ht⟩
  constructor
  · intro hst
    ext k'
    constructor
    · rintro ⟨k, hk, rfl⟩
      obtain ⟨t, ht0, ht⟩ := hspec k
      have h1 := (hst _).2 hk
      rw [ht] at h1
      have h2 : uPt (π k) = t⁻¹ • (t • uPt (π k)) := by
        rw [smul_smul, inv_mul_cancel₀ ht0, one_smul]
      show uPt (π k) ∈ V
      rw [h2]
      exact hs _ (inv_ne_zero ht0) _ h1
    · intro hk'
      refine ⟨π.symm k', ?_, by simp⟩
      obtain ⟨t, ht0, ht⟩ := hspec (π.symm k')
      rw [Equiv.apply_symm_apply] at ht
      apply (hst _).1
      rw [ht]
      exact hs _ ht0 _ hk'
  · intro hset w
    constructor
    · intro hw
      by_cases hw0 : (A : Matrix (Fin 4) (Fin 4) F4) *ᵥ w = 0
      · have : w = 0 := mk_mulVec_inj (by rw [hw0, Matrix.mulVec_zero])
        rw [this]
        exact h0
      · obtain ⟨k', hk', t, ht0, ht⟩ := hvec _ hw hw0
        have hk'S : k' ∈ π '' {k | uPt k ∈ V} := by rw [hset]; exact hk'
        obtain ⟨k, hk, rfl⟩ := hk'S
        obtain ⟨s, hs0, hsk⟩ := hspec k
        have h1 : (A : Matrix (Fin 4) (Fin 4) F4) *ᵥ w =
            (A : Matrix (Fin 4) (Fin 4) F4) *ᵥ ((t * s⁻¹) • uPt k) := by
          rw [ht, Matrix.mulVec_smul, hsk, smul_smul, mul_assoc, inv_mul_cancel₀ hs0, mul_one]
        rw [mk_mulVec_inj h1]
        exact hs _ (mul_ne_zero ht0 (inv_ne_zero hs0)) _ hk
    · intro hw
      by_cases hw0 : w = 0
      · rw [hw0, Matrix.mulVec_zero]
        exact h0
      · obtain ⟨k, hk, t, ht0, rfl⟩ := hvec w hw hw0
        obtain ⟨s, hs0, hsk⟩ := hspec k
        rw [Matrix.mulVec_smul, hsk, smul_smul]
        have hk' : π k ∈ π '' {k | uPt k ∈ V} := ⟨k, hk, rfl⟩
        rw [hset] at hk'
        exact hs _ (mul_ne_zero ht0 hs0) _ hk'

section Subspaces

variable {K : Type} [Field K]

@[expose] def mkV (φ : K ≃+* F4) (W : Submodule K (Fin 4 → K)) : Set (Fin 4 → F4) :=
  {w | (fun i => φ.symm (w i)) ∈ W}

theorem mkV_zero (φ : K ≃+* F4) (W : Submodule K (Fin 4 → K)) : (0 : Fin 4 → F4) ∈ mkV φ W := by
  have : (fun i => φ.symm ((0 : Fin 4 → F4) i)) = 0 := by
    funext i
    simp
  show (fun i => φ.symm ((0 : Fin 4 → F4) i)) ∈ W
  rw [this]
  exact W.zero_mem

theorem mkV_smul (φ : K ≃+* F4) (W : Submodule K (Fin 4 → K)) (c : F4) {w : Fin 4 → F4}
    (hw : w ∈ mkV φ W) : c • w ∈ mkV φ W := by
  have : (fun i => φ.symm ((c • w) i)) = φ.symm c • (fun i => φ.symm (w i)) := by
    funext i
    simp
  show (fun i => φ.symm ((c • w) i)) ∈ W
  rw [this]
  exact W.smul_mem _ hw

theorem mkV_iso (φ : K ≃+* F4) (W : Submodule K (Fin 4 → K))
    (hiso : ∀ v ∈ W, U42Hermitian K v v = 0) {w : Fin 4 → F4} (hw : w ∈ mkV φ W) :
    hU w w = 0 := by
  have h := hiso _ hw
  have h2 := mk_hU_map φ (fun i => φ.symm (w i)) (fun i => φ.symm (w i))
  rw [h, map_zero] at h2
  simpa using h2.symm

theorem mk_point_set (φ : K ≃+* F4) {point : Submodule K (Fin 4 → K)}
    (hdim : Module.finrank K point = 1) (hiso : ∀ v ∈ point, U42Hermitian K v v = 0) :
    ∃ j : Fin 45, ∀ w : Fin 4 → F4, w ∈ mkV φ point ↔ ∃ c : F4, w = c • uPt j := by
  let b : Module.Basis (Fin 1) K point := Module.finBasisOfFinrankEq K point hdim
  obtain ⟨p₁, hp₁⟩ : ∃ p₁ : Fin 4 → K, p₁ = ((b 0 : point) : Fin 4 → K) := ⟨_, rfl⟩
  have hp₁mem : p₁ ∈ point := by rw [hp₁]; exact (b 0).2
  have hp₁ne : p₁ ≠ 0 := fun h => b.ne_zero 0 (Subtype.ext (by rw [← hp₁]; exact h))
  have hspan : ∀ v ∈ point, ∃ s : K, v = s • p₁ := by
    intro v hv
    have h1 := b.sum_repr ⟨v, hv⟩
    rw [Fin.sum_univ_one] at h1
    refine ⟨b.repr ⟨v, hv⟩ 0, ?_⟩
    have h2 := congrArg Subtype.val h1
    rw [hp₁]
    simpa using h2.symm
  obtain ⟨P₁, hP₁⟩ : ∃ P₁ : Fin 4 → F4, P₁ = fun i => φ (p₁ i) := ⟨_, rfl⟩
  have hP₁ne : P₁ ≠ 0 := by
    intro h
    apply hp₁ne
    funext i
    have h2 := congrFun h i
    rw [hP₁] at h2
    simpa using h2
  have hP₁iso : hU P₁ P₁ = 0 := by
    have h := mk_hU_map φ p₁ p₁
    rw [hiso p₁ hp₁mem, map_zero] at h
    rw [hP₁]
    exact h.symm
  have hP₁mem : P₁ ∈ mkV φ point := by
    show (fun i => φ.symm (P₁ i)) ∈ point
    have : (fun i => φ.symm (P₁ i)) = p₁ := by
      funext i
      simp [hP₁]
    rw [this]
    exact hp₁mem
  obtain ⟨t, ht0, ht⟩ := mk_exists_smul hP₁ne hP₁iso
  generalize uIdx P₁ = j at ht
  refine ⟨j, fun w => ⟨?_, ?_⟩⟩
  · intro hw
    obtain ⟨s, hs⟩ := hspan _ hw
    refine ⟨φ s * t, ?_⟩
    have h1 : w = φ s • P₁ := by
      funext i
      have h2 := congrFun hs i
      have h3 : w i = φ (s * p₁ i) := by
        have h4 := congrArg φ h2
        simpa using h4
      rw [h3]
      simp [hP₁]
    rw [h1, ht, smul_smul]
  · rintro ⟨c, rfl⟩
    have h1 : uPt j = t⁻¹ • P₁ := by
      rw [ht, smul_smul, inv_mul_cancel₀ ht0, one_smul]
    rw [h1, smul_smul]
    exact mkV_smul φ point _ hP₁mem

theorem mkV_add (φ : K ≃+* F4) (W : Submodule K (Fin 4 → K)) {w w' : Fin 4 → F4}
    (hw : w ∈ mkV φ W) (hw' : w' ∈ mkV φ W) : w + w' ∈ mkV φ W := by
  have : (fun i => φ.symm ((w + w') i)) =
      (fun i => φ.symm (w i)) + (fun i => φ.symm (w' i)) := by
    funext i
    simp
  show (fun i => φ.symm ((w + w') i)) ∈ W
  rw [this]
  exact W.add_mem hw hw'

theorem mk_hU_smul (c d : F4) (x y : Fin 4 → F4) :
    hU (c • x) (d • y) = c * c * d * hU x y := by
  simp only [hU, Pi.smul_apply, smul_eq_mul]
  ring

theorem mk_plane_set (φ : K ≃+* F4) {plane : Submodule K (Fin 4 → K)}
    (hdim : Module.finrank K plane = 2)
    (hiso : ∀ v ∈ plane, ∀ w ∈ plane, U42Hermitian K v w = 0) :
    ∃ a b : Fin 45, a ≠ b ∧ hU (uPt a) (uPt b) = 0 ∧
      ∀ w : Fin 4 → F4, w ∈ mkV φ plane ↔ ∃ c d : F4, w = c • uPt a + d • uPt b := by
  let bs : Module.Basis (Fin 2) K plane := Module.finBasisOfFinrankEq K plane hdim
  obtain ⟨e₀, he₀⟩ : ∃ e : Fin 4 → K, e = ((bs 0 : plane) : Fin 4 → K) := ⟨_, rfl⟩
  obtain ⟨e₁, he₁⟩ : ∃ e : Fin 4 → K, e = ((bs 1 : plane) : Fin 4 → K) := ⟨_, rfl⟩
  have he₀mem : e₀ ∈ plane := by rw [he₀]; exact (bs 0).2
  have he₁mem : e₁ ∈ plane := by rw [he₁]; exact (bs 1).2
  have hspan : ∀ v ∈ plane, ∃ s t : K, v = s • e₀ + t • e₁ := by
    intro v hv
    have h1 := bs.sum_repr ⟨v, hv⟩
    rw [Fin.sum_univ_two] at h1
    refine ⟨bs.repr ⟨v, hv⟩ 0, bs.repr ⟨v, hv⟩ 1, ?_⟩
    have h2 := congrArg Subtype.val h1
    rw [he₀, he₁]
    simpa using h2.symm
  have hindep : ∀ s t : K, s • e₀ + t • e₁ = 0 → s = 0 ∧ t = 0 := by
    intro s t hst
    have hli := bs.linearIndependent
    rw [Fintype.linearIndependent_iff] at hli
    have h1 := hli ![s, t] (by
      rw [Fin.sum_univ_two]
      apply Subtype.ext
      simpa [he₀, he₁] using hst)
    exact ⟨by simpa using h1 0, by simpa using h1 1⟩
  obtain ⟨E₀, hE₀⟩ : ∃ E : Fin 4 → F4, E = fun i => φ (e₀ i) := ⟨_, rfl⟩
  obtain ⟨E₁, hE₁⟩ : ∃ E : Fin 4 → F4, E = fun i => φ (e₁ i) := ⟨_, rfl⟩
  have hE₀ne : E₀ ≠ 0 := by
    intro h
    have h1 : e₀ = 0 := by
      funext i
      have h2 := congrFun h i
      rw [hE₀] at h2
      simpa using h2
    have := hindep 1 0 (by rw [h1]; simp)
    exact one_ne_zero this.1
  have hE₁ne : E₁ ≠ 0 := by
    intro h
    have h1 : e₁ = 0 := by
      funext i
      have h2 := congrFun h i
      rw [hE₁] at h2
      simpa using h2
    have := hindep 0 1 (by rw [h1]; simp)
    exact one_ne_zero this.2
  have hE₀iso : hU E₀ E₀ = 0 := by
    have h := mk_hU_map φ e₀ e₀
    rw [hiso e₀ he₀mem e₀ he₀mem, map_zero] at h
    rw [hE₀]
    exact h.symm
  have hE₁iso : hU E₁ E₁ = 0 := by
    have h := mk_hU_map φ e₁ e₁
    rw [hiso e₁ he₁mem e₁ he₁mem, map_zero] at h
    rw [hE₁]
    exact h.symm
  have hE₀₁ : hU E₀ E₁ = 0 := by
    have h := mk_hU_map φ e₀ e₁
    rw [hiso e₀ he₀mem e₁ he₁mem, map_zero] at h
    rw [hE₀, hE₁]
    exact h.symm
  have hE₀mem : E₀ ∈ mkV φ plane := by
    show (fun i => φ.symm (E₀ i)) ∈ plane
    have : (fun i => φ.symm (E₀ i)) = e₀ := by
      funext i
      simp [hE₀]
    rw [this]
    exact he₀mem
  have hE₁mem : E₁ ∈ mkV φ plane := by
    show (fun i => φ.symm (E₁ i)) ∈ plane
    have : (fun i => φ.symm (E₁ i)) = e₁ := by
      funext i
      simp [hE₁]
    rw [this]
    exact he₁mem
  obtain ⟨t₀, ht₀, h0⟩ := mk_exists_smul hE₀ne hE₀iso
  obtain ⟨t₁, ht₁, h1⟩ := mk_exists_smul hE₁ne hE₁iso
  generalize uIdx E₀ = a at h0
  generalize uIdx E₁ = b at h1
  have hab : a ≠ b := by
    rintro rfl
    have h2 : E₁ = (t₁ * t₀⁻¹) • E₀ := by
      rw [h0, h1, smul_smul, mul_assoc, inv_mul_cancel₀ ht₀, mul_one]
    have h3 : e₁ = φ.symm (t₁ * t₀⁻¹) • e₀ := by
      funext i
      apply φ.injective
      have h4 := congrFun h2 i
      rw [hE₁, hE₀] at h4
      simpa using h4
    have h5 := hindep (φ.symm (t₁ * t₀⁻¹)) (-1) (by rw [h3]; simp)
    simp at h5
  have hort : hU (uPt a) (uPt b) = 0 := by
    have h2 : hU E₀ E₁ = t₀ * t₀ * t₁ * hU (uPt a) (uPt b) := by
      rw [h0, h1, mk_hU_smul]
    rw [hE₀₁] at h2
    rcases mul_eq_zero.1 h2.symm with h3 | h3
    · exact absurd h3 (mul_ne_zero (mul_ne_zero ht₀ ht₀) ht₁)
    · exact h3
  refine ⟨a, b, hab, hort, fun w => ⟨?_, ?_⟩⟩
  · intro hw
    obtain ⟨s, t, hst⟩ := hspan _ hw
    refine ⟨φ s * t₀, φ t * t₁, ?_⟩
    have h2 : w = φ s • E₀ + φ t • E₁ := by
      funext i
      have h3 := congrFun hst i
      have h4 := congrArg φ h3
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul,
        RingEquiv.apply_symm_apply] at h4
      rw [h4, hE₀, hE₁]
      simp
    rw [h2, h0, h1, smul_smul, smul_smul]
  · rintro ⟨c, d, rfl⟩
    have h2 : c • uPt a + d • uPt b = (c * t₀⁻¹) • E₀ + (d * t₁⁻¹) • E₁ := by
      rw [h0, h1, smul_smul, smul_smul, mul_assoc, mul_assoc, inv_mul_cancel₀ ht₀,
        inv_mul_cancel₀ ht₁, mul_one, mul_one]
    rw [h2]
    exact mkV_add φ plane (mkV_smul φ plane _ hE₀mem) (mkV_smul φ plane _ hE₁mem)

end Subspaces

theorem mk_flag_chk : ∀ m : Fin 27, ∀ r : Fin 5,
    (evalW ((flagDat.getD (5 * m.val + r.val) (0, [])).2 ++
      DW.getD (flagDat.getD (5 * m.val + r.val) (0, [])).1 [])).getD 0 0 =
        (lnTab.getD m []).getD r 0 ∧
    sameSet (imgSet (evalW ((flagDat.getD (5 * m.val + r.val) (0, [])).2 ++
      DW.getD (flagDat.getD (5 * m.val + r.val) (0, [])).1 [])) L0) (lnTab.getD m []) = true := by
  decide +kernel

theorem mk_L0_lt : ∀ p ∈ L0, p < 45 := by decide +kernel

open CFSG.Quasithin.H13.F431.U42 (wordP repL_wordP image_lineSet lineSet_eq_of_sameSet wordP_mem
  Xs_eq lineSet L0S)

theorem mk_flag_move (m : Fin 27) (r : Fin 5) :
    ∃ δ ∈ QP45.originalSubgroup,
      (δ : Equiv.Perm (Fin 45)) 0 = mkLn m r ∧
      (δ : Equiv.Perm (Fin 45)) '' L0S = lineSet (lnTab.getD m []) := by
  obtain ⟨h1, h2⟩ := mk_flag_chk m r
  refine ⟨wordP ((flagDat.getD (5 * m.val + r.val) (0, [])).2 ++
      DW.getD (flagDat.getD (5 * m.val + r.val) (0, [])).1 []), ?_, ?_, ?_⟩
  · rw [← Xs_eq]
    exact wordP_mem _
  · apply Fin.ext
    have h3 := (repL_wordP ((flagDat.getD (5 * m.val + r.val) (0, [])).2 ++
      DW.getD (flagDat.getD (5 * m.val + r.val) (0, [])).1 [])).2 0
    rw [← h3]
    exact h1
  · rw [L0S, image_lineSet (repL_wordP _) mk_L0_lt, lineSet_eq_of_sameSet h2]

section Cocycle

variable {K : Type} [Field K]

@[expose] def mkJ (K : Type) [Field K] : Matrix (Fin 4) (Fin 4) K :=
  Matrix.of (fun row column : Fin 4 =>
    if (row.val, column.val) = (0, 2) ∨ (row.val, column.val) = (1, 3) ∨
      (row.val, column.val) = (2, 0) ∨ (row.val, column.val) = (3, 1) then 1 else 0)

theorem mkJ_symm : (mkJ K)ᵀ = mkJ K := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mkJ]

theorem mk_u_J_u (hK2 : (2 : K) = 0) (u : Fin 4 → K) : u ⬝ᵥ (mkJ K *ᵥ u) = 0 := by
  simp only [mkJ, Matrix.mulVec, dotProduct, Fin.sum_univ_four, Matrix.of_apply]
  simp
  linear_combination (u 0 * u 2 + u 1 * u 3) * hK2

theorem mk_dot_mulVec (M : Matrix (Fin 4) (Fin 4) K) (a b : Fin 4 → K) :
    (M *ᵥ a) ⬝ᵥ b = a ⬝ᵥ (Mᵀ *ᵥ b) := by
  rw [dotProduct_comm, Matrix.dotProduct_mulVec, dotProduct_comm, Matrix.mulVec_transpose]

theorem mkTrvMat_map {σ : K →+* K} (hσσ : ∀ x, σ (σ x) = x) (p : Fin 4 → K) :
    (mkTrvMat σ p).map σ = 1 + Matrix.vecMulVec (σ ∘ p) p := by
  ext i j
  by_cases h : i = j
  · subst h
    simp [mkTrvMat, Matrix.vecMulVec_apply, hσσ]
  · simp [mkTrvMat, Matrix.vecMulVec_apply, hσσ, h]

theorem mk_sigma_mulVec {σ : K →+* K} (M : Matrix (Fin 4) (Fin 4) K) (u : Fin 4 → K)
    (hu : ∀ i, σ (u i) = u i) : σ ∘ (M *ᵥ u) = (M.map σ) *ᵥ u := by
  funext i
  have h := RingHom.map_mulVec σ M u i
  have hu' : σ ∘ u = u := funext hu
  rw [hu'] at h
  exact h

theorem mk_iso_of_fixed {σ : K →+* K} (hσ : ∀ x, σ x = x ^ 2) (hK2 : (2 : K) = 0)
    (C : GL (Fin 4) K)
    (hC : ((C : Matrix (Fin 4) (Fin 4) K).map σ)ᵀ * (C : Matrix (Fin 4) (Fin 4) K) = mkJ K)
    (u : Fin 4 → K) (hu : ∀ i, σ (u i) = u i) :
    U42Hermitian K ((C : Matrix (Fin 4) (Fin 4) K) *ᵥ u)
      ((C : Matrix (Fin 4) (Fin 4) K) *ᵥ u) = 0 := by
  rw [← mk_dot_eq hσ, mk_sigma_mulVec _ u hu, mk_dot_mulVec, Matrix.mulVec_mulVec, hC]
  exact mk_u_J_u hK2 u

theorem mk_cocycle_alg {σ : K →+* K} (hσ : ∀ x, σ x = x ^ 2) (hσσ : ∀ x, σ (σ x) = x)
    (hK2 : (2 : K) = 0) (C : GL (Fin 4) K)
    (hC : ((C : Matrix (Fin 4) (Fin 4) K).map σ)ᵀ * (C : Matrix (Fin 4) (Fin 4) K) = mkJ K)
    (u : Fin 4 → K) (hu : ∀ i, σ (u i) = u i)
    (hp : U42Hermitian K ((C : Matrix (Fin 4) (Fin 4) K) *ᵥ u)
      ((C : Matrix (Fin 4) (Fin 4) K) *ᵥ u) = 0) :
    ((C * (Matrix.GeneralLinearGroup.map σ C)⁻¹ *
        Matrix.GeneralLinearGroup.map σ (mkTrvGL hσ hK2 hp) *
          Matrix.GeneralLinearGroup.map σ C * C⁻¹ : GL (Fin 4) K) :
        Matrix (Fin 4) (Fin 4) K) =
      mkTrvMat σ ((C : Matrix (Fin 4) (Fin 4) K) *ᵥ u) := by
  set Cm : Matrix (Fin 4) (Fin 4) K := (C : Matrix (Fin 4) (Fin 4) K) with hCm
  set Cs : Matrix (Fin 4) (Fin 4) K := Cm.map σ with hCs
  set Cis : Matrix (Fin 4) (Fin 4) K :=
    (((Matrix.GeneralLinearGroup.map σ C)⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)
    with hCis
  set Ci : Matrix (Fin 4) (Fin 4) K := ((C⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) with hCi
  have h1 : Cm * Ci = 1 := Units.mul_inv C
  have h2 : Cis * Cs = 1 := Units.inv_mul (Matrix.GeneralLinearGroup.map σ C)
  have hGLs : ((Matrix.GeneralLinearGroup.map σ C : GL (Fin 4) K) :
      Matrix (Fin 4) (Fin 4) K) = Cs := rfl
  have hGLT : ((Matrix.GeneralLinearGroup.map σ (mkTrvGL hσ hK2 hp) : GL (Fin 4) K) :
      Matrix (Fin 4) (Fin 4) K) = (mkTrvMat σ (Cm *ᵥ u)).map σ := rfl
  have hq : σ ∘ (Cm *ᵥ u) = Cs *ᵥ u := mk_sigma_mulVec Cm u hu
  have hCmCs : Cmᵀ * Cs = mkJ K := by
    have h3 := congrArg Matrix.transpose hC
    rwa [Matrix.transpose_mul, Matrix.transpose_transpose, mkJ_symm] at h3
  have e1 : (Cm * Cis) *ᵥ (σ ∘ (Cm *ᵥ u)) = Cm *ᵥ u := by
    rw [hq, Matrix.mulVec_mulVec, Matrix.mul_assoc, h2, Matrix.mul_one]
  have e2 : (Cm *ᵥ u) ᵥ* (Cs * Ci) = σ ∘ (Cm *ᵥ u) := by
    rw [hq, ← Matrix.vecMul_vecMul, ← Matrix.vecMul_transpose Cm u,
      Matrix.vecMul_vecMul u Cmᵀ Cs, hCmCs, Matrix.vecMul_vecMul]
    have h4 : mkJ K * Ci = Csᵀ := by
      rw [← hC, Matrix.mul_assoc, h1, Matrix.mul_one]
    rw [h4, Matrix.vecMul_transpose]
  simp only [Units.val_mul]
  rw [hGLs, hGLT, mkTrvMat_map hσσ]
  calc Cm * Cis * (1 + Matrix.vecMulVec (σ ∘ (Cm *ᵥ u)) (Cm *ᵥ u)) * Cs * Ci
      = Cm * (Cis * Cs) * Ci +
        (Cm * Cis) * Matrix.vecMulVec (σ ∘ (Cm *ᵥ u)) (Cm *ᵥ u) * (Cs * Ci) := by noncomm_ring
    _ = 1 + Matrix.vecMulVec ((Cm * Cis) *ᵥ (σ ∘ (Cm *ᵥ u))) ((Cm *ᵥ u) ᵥ* (Cs * Ci)) := by
      rw [h2, Matrix.mul_one, h1, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul]
    _ = mkTrvMat σ (Cm *ᵥ u) := by rw [e1, e2]; rfl

@[expose] def mkBitVec (K : Type) [Field K] (b : Fin 4 → Bool) : Fin 4 → K :=
  fun i => if b i then 1 else 0

theorem mkBitVec_fixed (σ : K →+* K) (b : Fin 4 → Bool) (i : Fin 4) :
    σ (mkBitVec K b i) = mkBitVec K b i := by
  unfold mkBitVec
  split_ifs <;> simp

theorem mkBitVec_ne_zero {b : Fin 4 → Bool} (hb : b ≠ fun _ => false) :
    mkBitVec K b ≠ 0 := by
  intro h
  apply hb
  funext i
  have h2 := congrFun h i
  unfold mkBitVec at h2
  by_contra hbi
  have : b i = true := by simpa using hbi
  simp [this] at h2

theorem mk_fixed_vec_ok (φ : K ≃+* F4) {σ : K →+* K} (hσ : ∀ x, σ x = x ^ 2)
    (hK2 : (2 : K) = 0) (C : GL (Fin 4) K)
    (hC : ((C : Matrix (Fin 4) (Fin 4) K).map σ)ᵀ * (C : Matrix (Fin 4) (Fin 4) K) = mkJ K)
    {c : Fin 4 → Bool} (hc : c ≠ fun _ => false) :
    (fun i => φ (((C : Matrix (Fin 4) (Fin 4) K) *ᵥ mkBitVec K c) i)) ≠ 0 ∧
      hU (fun i => φ (((C : Matrix (Fin 4) (Fin 4) K) *ᵥ mkBitVec K c) i))
        (fun i => φ (((C : Matrix (Fin 4) (Fin 4) K) *ᵥ mkBitVec K c) i)) = 0 := by
  refine ⟨?_, ?_⟩
  · intro h0
    apply mkBitVec_ne_zero (K := K) hc
    refine mk_mulVec_inj (R := K) (A := C) (u := mkBitVec K c) (v := 0) ?_
    rw [Matrix.mulVec_zero]
    funext i
    have h1 := congrFun h0 i
    simpa using h1
  · rw [← mk_hU_map, mk_iso_of_fixed hσ hK2 C hC _ (mkBitVec_fixed σ c), map_zero]

theorem mk_fixed_inj (φ : K ≃+* F4) {σ : K →+* K} (hσ : ∀ x, σ x = x ^ 2) (hK2 : (2 : K) = 0)
    (C : GL (Fin 4) K)
    (hC : ((C : Matrix (Fin 4) (Fin 4) K).map σ)ᵀ * (C : Matrix (Fin 4) (Fin 4) K) = mkJ K)
    {b b' : Fin 4 → Bool} (hb : b ≠ fun _ => false) (hb' : b' ≠ fun _ => false)
    (h : uIdx (fun i => φ (((C : Matrix (Fin 4) (Fin 4) K) *ᵥ mkBitVec K b) i)) =
      uIdx (fun i => φ (((C : Matrix (Fin 4) (Fin 4) K) *ᵥ mkBitVec K b') i))) : b = b' := by
  have hmem := fun c (hc : c ≠ fun _ => false) => mk_fixed_vec_ok φ hσ hK2 C hC hc
  obtain ⟨t, ht0, ht⟩ := mk_exists_smul (hmem b hb).1 (hmem b hb).2
  obtain ⟨t', ht0', ht'⟩ := mk_exists_smul (hmem b' hb').1 (hmem b' hb').2
  rw [h] at ht
  generalize uIdx (fun i => φ (((C : Matrix (Fin 4) (Fin 4) K) *ᵥ mkBitVec K b') i)) = j at ht ht'
  have h1 : (C : Matrix (Fin 4) (Fin 4) K) *ᵥ mkBitVec K b =
      (C : Matrix (Fin 4) (Fin 4) K) *ᵥ (φ.symm (t * t'⁻¹) • mkBitVec K b') := by
    rw [Matrix.mulVec_smul]
    funext i
    apply φ.injective
    have h2 := congrFun ht i
    have h3 := congrFun ht' i
    simp only [Pi.smul_apply, smul_eq_mul] at h2 h3 ⊢
    rw [map_mul, RingEquiv.apply_symm_apply, h2, h3]
    have : (t * t'⁻¹ * (t' * uPt j i)) = t * uPt j i := by
      field_simp
    exact this.symm ▸ rfl
  have h2 := mk_mulVec_inj h1
  have hs0 : φ.symm (t * t'⁻¹) ≠ 0 := by
    intro h0
    have := φ.symm.injective (h0.trans (map_zero φ.symm).symm)
    exact mul_ne_zero ht0 (inv_ne_zero ht0') this
  obtain ⟨i₀, hi₀⟩ : ∃ i, b' i = true := by
    by_contra hcon
    apply hb'
    funext i
    by_contra hne
    exact hcon ⟨i, by simpa using hne⟩
  have h3 := congrFun h2 i₀
  simp only [mkBitVec, Pi.smul_apply, smul_eq_mul, hi₀, if_true, mul_one] at h3
  have hs1 : φ.symm (t * t'⁻¹) = 1 := by
    by_cases hbi : b i₀ = true
    · rw [if_pos hbi] at h3
      exact h3.symm
    · rw [if_neg hbi] at h3
      exact absurd h3.symm hs0
  funext i
  have h4 := congrFun h2 i
  simp only [mkBitVec, Pi.smul_apply, smul_eq_mul, hs1, one_mul] at h4
  by_cases hbi : b i = true
  · by_cases hbi' : b' i = true
    · rw [hbi, hbi']
    · simp [hbi, hbi'] at h4
  · by_cases hbi' : b' i = true
    · simp [hbi, hbi'] at h4
    · simp at hbi hbi'
      rw [hbi, hbi']

theorem mk_fixed_one (φ : K ≃+* F4) {σ : K →+* K} (hσ : ∀ x, σ x = x ^ 2)
    (hσσ : ∀ x, σ (σ x) = x) (C : GL (Fin 4) K)
    (hC : ((C : Matrix (Fin 4) (Fin 4) K).map σ)ᵀ * (C : Matrix (Fin 4) (Fin 4) K) = mkJ K)
    {E : Type} [Group E] {Gp : Subgroup E} (m : ↥Gp ≃* StatedProj (StatedSU 4 2 K)) (fb : E)
    (hcoc : ∀ element : ↥Gp, ∃ conjugate : ↥Gp,
      (conjugate : E) = fb * (element : E) * fb⁻¹ ∧
      ∀ matrix : ↥(StatedSU 4 2 K),
        m element = (QuotientGroup.mk matrix : StatedProj (StatedSU 4 2 K)) →
          ∃ image : ↥(StatedSU 4 2 K),
            m conjugate = (QuotientGroup.mk image : StatedProj (StatedSU 4 2 K)) ∧
            (image : GL (Fin 4) K) = C * (Matrix.GeneralLinearGroup.map σ C)⁻¹ *
              Matrix.GeneralLinearGroup.map σ (matrix : GL (Fin 4) K) *
                Matrix.GeneralLinearGroup.map σ C * C⁻¹)
    {b : Fin 4 → Bool} (hb : b ≠ fun _ => false) :
    ∃ g : ↥Gp, mkRho φ m g =
        tauPerm (uIdx (fun i => φ (((C : Matrix (Fin 4) (Fin 4) K) *ᵥ mkBitVec K b) i))) ∧
      fb * (g : E) * fb⁻¹ = (g : E) := by
  have hK2 := mk_K_two φ
  have hu : ∀ i, σ (mkBitVec K b i) = mkBitVec K b i := mkBitVec_fixed σ b
  have hp := mk_iso_of_fixed hσ hK2 C hC (mkBitVec K b) hu
  obtain ⟨hq0, hqiso⟩ := mk_fixed_vec_ok φ hσ hK2 C hC hb
  let M : ↥(StatedSU 4 2 K) := ⟨mkTrvGL hσ hK2 hp, mkTrvGL_mem hσ hσσ hK2 hp⟩
  refine ⟨m.symm (QuotientGroup.mk M), ?_, ?_⟩
  · apply Equiv.ext
    intro k
    rw [mkRho_mk φ m _ M (by simp)]
    show _ = tauFun _ k
    show uIdx (((mkTrvMat σ _).map φ) *ᵥ uPt k) = _
    rw [mkTrvMat_act φ hσ]
    exact mk_tU_idx hq0 hqiso k
  · obtain ⟨conj, hconj1, hconj2⟩ := hcoc (m.symm (QuotientGroup.mk M))
    obtain ⟨image, himage1, himage2⟩ := hconj2 M (by simp)
    have himg : image = M := by
      apply Subtype.ext
      apply Units.ext
      rw [himage2]
      exact mk_cocycle_alg hσ hσσ hK2 C hC (mkBitVec K b) hu hp
    have hconjeq : conj = m.symm (QuotientGroup.mk M) := by
      apply m.injective
      rw [himage1, himg, MulEquiv.apply_symm_apply]
    rw [← hconj1, hconjeq]

end Cocycle

section Parabolics

variable {K : Type} [Field K]

theorem mk_map_mulVec_symm (φ : K ≃+* F4) (M : Matrix (Fin 4) (Fin 4) K) (w : Fin 4 → F4) :
    (fun i => φ.symm ((M.map φ *ᵥ w) i)) = M *ᵥ (fun i => φ.symm (w i)) := by
  funext i
  apply φ.injective
  simp [Matrix.mulVec, dotProduct, map_sum]

theorem mk_par_equiv (φ : K ≃+* F4) {E : Type} [Group E] {Gp : Subgroup E}
    (m : ↥Gp ≃* StatedProj (StatedSU 4 2 K)) (W : Submodule K (Fin 4 → K))
    (hiso : ∀ v ∈ W, U42Hermitian K v v = 0) (g : ↥Gp) (M : ↥(StatedSU 4 2 K))
    (hM : m g = QuotientGroup.mk M) :
    (∀ v : Fin 4 → K, ((M : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).mulVec v ∈ W ↔ v ∈ W) ↔
      ((mkRho φ m g : Equiv.Perm (Fin 45)) '' {k | uPt k ∈ mkV φ W} =
        {k | uPt k ∈ mkV φ W}) := by
  have hA := (CFSG.Open.StatedSUFieldChange.statedSUEquiv φ 4 2 M).2
  have key := mk_stab hA (V := mkV φ W) (mkV_zero φ W)
    (fun c _ w hw => mkV_smul φ W c hw) (fun w hw => mkV_iso φ W hiso hw) (mkRho φ m g)
    (fun j => by
      rw [mkRho_mk φ m g M hM j]
      rfl)
  rw [← key]
  constructor
  · intro h w
    have h1 := h (fun i => φ.symm (w i))
    show (fun i => φ.symm ((((M : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map φ *ᵥ w) i)) ∈ W ↔
      (fun i => φ.symm (w i)) ∈ W
    rw [mk_map_mulVec_symm]
    exact h1
  · intro h v
    have h1 := h (fun i => φ (v i))
    have h2 : (fun i => φ.symm ((fun i => φ (v i)) i)) = v := by
      funext i
      simp
    have h3 : mkV φ W = {w | (fun i => φ.symm (w i)) ∈ W} := rfl
    have h4 : (((M : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).mulVec v) =
        (fun i => φ.symm ((((M : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map φ *ᵥ
          (fun i => φ (v i))) i)) := by
      rw [mk_map_mulVec_symm, h2]
    rw [h4]
    conv_rhs => rw [← h2]
    exact h1

theorem mk_S_point (φ : K ≃+* F4) {point : Submodule K (Fin 4 → K)} {j₀ : Fin 45}
    (hj₀ : ∀ w : Fin 4 → F4, w ∈ mkV φ point ↔ ∃ c : F4, w = c • uPt j₀) :
    {k | uPt k ∈ mkV φ point} = {j₀} := by
  ext k
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  rw [hj₀]
  constructor
  · rintro ⟨c, hc⟩
    have hc0 : c ≠ 0 := by
      rintro rfl
      simp only [zero_smul] at hc
      exact (uPt_spec k).1 hc
    have h1 := uIdx_smul_uPt j₀ c hc0
    rw [← hc, mk_uIdx_uPt] at h1
    exact h1
  · rintro rfl
    exact ⟨1, by simp⟩

end Parabolics

theorem mk_smul_set_eq (a : CFSG.Quasithin.H13.F431.U42Aut.Ah) (S : Set (Fin 45)) :
    a • S = (a : Equiv.Perm (Fin 45)) '' S := (Set.image_smul (a := a) (t := S)).symm

theorem exists_markIso {E : Type} [Group E]
    {Gp M₁ M₂ : Subgroup E} {fb : E} (hA : F5Amalgam Gp M₁ M₂ fb) :
    ∃ Θ : E ≃* CFSG.Quasithin.H13.F431.U42Aut.Ah,
      (∀ x : E, Θ x ∈ CFSG.Quasithin.H13.F431.U42Aut.Yh ↔ x ∈ Gp) ∧
      (∀ x : E, x ∈ Gp → (Θ x ∈ CFSG.Quasithin.H13.F431.U42Aut.P1h ↔ x ∈ M₁)) ∧
      (∀ x : E, x ∈ Gp → (Θ x ∈ CFSG.Quasithin.H13.F431.U42Aut.P2h ↔ x ∈ M₂)) ∧
      15 ≤ (Finset.univ.filter fun ℓ : Fin 45 =>
        ((Θ fb : CFSG.Quasithin.H13.F431.U42Aut.Ah) : Equiv.Perm (Fin 45)) ℓ = ℓ).card := by
  classical
  haveI : Finite E := hA.finite
  haveI : Gp.Normal := hA.normal
  obtain ⟨hfbGp, -, K, instK, instFin, hKcard, σ, C, hσ, hC, m, point, plane, hp1, hp2, hpp,
    hiso, hpar1, hpar2, hcoc⟩ := hA.native
  haveI : Fintype K := Fintype.ofFinite K
  have hcardK : Fintype.card K = Fintype.card F4 := by
    rw [← Nat.card_eq_fintype_card, hKcard, F4.card]
  let φ : K ≃+* F4 := FiniteField.ringEquivOfCardEq hcardK
  have hσσ : ∀ x, σ (σ x) = x := fun x => by rw [hσ, hσ]; exact mk_K_sq_sq φ x
  have hC' : ((C : Matrix (Fin 4) (Fin 4) K).map σ)ᵀ * (C : Matrix (Fin 4) (Fin 4) K) = mkJ K :=
    hC
  have hGp : Nat.card ↥Gp = 25920 := by
    have h := CFSG.ComponentClassification.UnbalancingLocal.card_psu_four_two (K := K)
      (by rw [hKcard]; norm_num)
    rw [Nat.card_congr m.toEquiv]
    exact h
  have htau := mk_exists_rho_tau φ hσ hσσ m
  obtain ⟨hρrange, hρinj⟩ := mk_range_eq hGp (mkRho φ m) htau
  let ρ₀ : ↥Gp ≃* ↥QP45.originalSubgroup :=
    (MonoidHom.ofInjective hρinj).trans (MulEquiv.subgroupCongr hρrange)
  have hisopt : ∀ v ∈ point, U42Hermitian K v v = 0 := fun v hv => hiso v (hpp hv) v (hpp hv)
  obtain ⟨j₀, hj₀⟩ := mk_point_set φ hp1 hisopt
  obtain ⟨a, b, hab, hort, hplane⟩ := mk_plane_set φ hp2 hiso
  obtain ⟨m₀, hm₀⟩ := mk_line_set hab hort
  have hSpoint := mk_S_point φ hj₀
  have hSplane : {k : Fin 45 | uPt k ∈ mkV φ plane} = lineSet (lnTab.getD m₀ []) := by
    ext k
    exact (hplane (uPt k)).trans (hm₀ k)
  have hj₀line : j₀.val ∈ lnTab.getD m₀ [] := by
    have h1 : j₀ ∈ {k : Fin 45 | uPt k ∈ mkV φ plane} := hpp ((hj₀ _).2 ⟨1, by simp⟩)
    rw [hSplane] at h1
    exact h1
  obtain ⟨r, hr⟩ := mk_mem_line m₀ j₀ hj₀line
  obtain ⟨δ, hδP, hδ0, hδL⟩ := mk_flag_move m₀ r
  have hδj : (δ : Equiv.Perm (Fin 45)) 0 = j₀ := by
    rw [hδ0]
    exact hr
  have hδL' : ((δ⁻¹ : Equiv.Perm (Fin 45)) : Fin 45 → Fin 45) '' lineSet (lnTab.getD m₀ []) =
      L0S := by
    rw [← hδL, ← Set.image_comp]
    have h1 : ((δ⁻¹ : Equiv.Perm (Fin 45)) : Fin 45 → Fin 45) ∘ (δ : Fin 45 → Fin 45) = id := by
      funext x
      simp
    rw [h1, Set.image_id]
  have hδinvP : δ⁻¹ ∈ QP45.originalSubgroup := QP45.originalSubgroup.inv_mem hδP
  let y : ↥QP45.originalSubgroup := ⟨δ⁻¹, hδinvP⟩
  let ψ : ↥Gp ≃* ↥QP45.originalSubgroup := ρ₀.trans (MulAut.conj y)
  have hψ : ∀ g : ↥Gp, ((ψ g : ↥QP45.originalSubgroup) : Equiv.Perm (Fin 45)) =
      δ⁻¹ * mkRho φ m g * δ⁻¹⁻¹ := fun g => rfl
  have hne : Gp ≠ ⊤ := fun h => hfbGp (h ▸ Subgroup.mem_top fb)
  obtain ⟨Θ, -, hΘagree, hΘP⟩ := mk_exists_theta hA.centralizer_trivial hne hGp ψ
  refine ⟨Θ, fun x => (Subgroup.mem_subgroupOf).trans (hΘP x), ?_, ?_, ?_⟩
  ·
    intro x hx
    have hg := hΘagree ⟨x, hx⟩
    have h1 : x ∈ M₁ ↔ mkRho φ m ⟨x, hx⟩ j₀ = j₀ := by
      have h2 := hpar1.2 ⟨x, hx⟩
      have h3 : x ∈ M₁ ↔ x ∈ Gp ⊓ M₁ := ⟨fun h => ⟨hx, h⟩, fun h => h.2⟩
      refine h3.trans (h2.trans ?_)
      obtain ⟨M₀, hM₀⟩ := QuotientGroup.mk_surjective (m ⟨x, hx⟩)
      constructor
      · rintro ⟨M, hM, hst⟩
        have h4 := (mk_par_equiv φ m point hisopt ⟨x, hx⟩ M hM).1 hst
        rw [hSpoint] at h4
        simpa using h4
      · intro h
        refine ⟨M₀, hM₀.symm, ?_⟩
        apply (mk_par_equiv φ m point hisopt ⟨x, hx⟩ M₀ hM₀.symm).2
        rw [hSpoint]
        simpa using h
    have h2 : Θ x ∈ CFSG.Quasithin.H13.F431.U42Aut.P1h ↔
        ((Θ x : CFSG.Quasithin.H13.F431.U42Aut.Ah) : Equiv.Perm (Fin 45)) 0 = 0 :=
      MulAction.mem_stabilizer_iff
    rw [h2, h1, hg, hψ]
    have hδinv : δ⁻¹ j₀ = 0 := Equiv.Perm.inv_eq_iff_eq.2 hδj.symm
    have h3 : δ⁻¹⁻¹ 0 = j₀ := by rw [inv_inv]; exact hδj
    show δ⁻¹ ((mkRho φ m ⟨x, hx⟩) (δ⁻¹⁻¹ 0)) = 0 ↔ _
    rw [h3]
    constructor
    · intro h
      exact δ⁻¹.injective (h.trans hδinv.symm)
    · intro h
      rw [h]
      exact hδinv
  ·
    intro x hx
    have hg := hΘagree ⟨x, hx⟩
    have hisop : ∀ v ∈ plane, U42Hermitian K v v = 0 := fun v hv => hiso v hv v hv
    have h1 : x ∈ M₂ ↔ (mkRho φ m ⟨x, hx⟩ : Equiv.Perm (Fin 45)) ''
        lineSet (lnTab.getD m₀ []) = lineSet (lnTab.getD m₀ []) := by
      have h2 := hpar2.2 ⟨x, hx⟩
      have h3 : x ∈ M₂ ↔ x ∈ Gp ⊓ M₂ := ⟨fun h => ⟨hx, h⟩, fun h => h.2⟩
      refine h3.trans (h2.trans ?_)
      obtain ⟨M₀, hM₀⟩ := QuotientGroup.mk_surjective (m ⟨x, hx⟩)
      constructor
      · rintro ⟨M, hM, hst⟩
        have h4 := (mk_par_equiv φ m plane hisop ⟨x, hx⟩ M hM).1 hst
        rw [hSplane] at h4
        exact h4
      · intro h
        refine ⟨M₀, hM₀.symm, ?_⟩
        apply (mk_par_equiv φ m plane hisop ⟨x, hx⟩ M₀ hM₀.symm).2
        rw [hSplane]
        exact h
    have h2 : Θ x ∈ CFSG.Quasithin.H13.F431.U42Aut.P2h ↔
        ((Θ x : CFSG.Quasithin.H13.F431.U42Aut.Ah) : Equiv.Perm (Fin 45)) '' L0S = L0S :=
      MulAction.mem_stabilizer_iff.trans (by rw [mk_smul_set_eq])
    rw [h2, h1, hg, hψ]
    have h3 : (δ⁻¹⁻¹ : Equiv.Perm (Fin 45)) '' L0S = lineSet (lnTab.getD m₀ []) := by
      rw [inv_inv]
      exact hδL
    simp only [Equiv.Perm.coe_mul, Set.image_comp]
    rw [h3, ← hδL']
    exact Set.image_eq_image δ⁻¹.injective
  ·
    have hfixex : ∀ b : Fin 4 → Bool, b ≠ (fun _ => false) →
        ∃ g : ↥Gp, mkRho φ m g = tauPerm (uIdx (fun i =>
            φ (((C : Matrix (Fin 4) (Fin 4) K) *ᵥ mkBitVec K b) i))) ∧
          fb * (g : E) * fb⁻¹ = (g : E) := fun b hb =>
      mk_fixed_one φ hσ hσσ C hC' m fb hcoc hb
    choose! g hg1 hg2 using hfixex
    have hmem : ∀ b ∈ Finset.univ.filter (fun b : Fin 4 → Bool => b ≠ fun _ => false),
        (δ⁻¹ : Equiv.Perm (Fin 45)) (uIdx (fun i =>
          φ (((C : Matrix (Fin 4) (Fin 4) K) *ᵥ mkBitVec K b) i))) ∈
        Finset.univ.filter (fun ℓ : Fin 45 =>
          ((Θ fb : CFSG.Quasithin.H13.F431.U42Aut.Ah) : Equiv.Perm (Fin 45)) ℓ = ℓ) := by
      intro b hb
      have hb' : b ≠ fun _ => false := (Finset.mem_filter.1 hb).2
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      set l₀ := uIdx (fun i => φ (((C : Matrix (Fin 4) (Fin 4) K) *ᵥ mkBitVec K b) i))
      have hΘg : ((Θ (g b : E) : CFSG.Quasithin.H13.F431.U42Aut.Ah) : Equiv.Perm (Fin 45)) =
          tauPerm (δ⁻¹ l₀) := by
        rw [hΘagree, hψ, hg1 b hb']
        exact mk_conj_tau (mkQ_of_mem (mk_P_le_A hδinvP)) l₀
      have hcomm : ((Θ fb : CFSG.Quasithin.H13.F431.U42Aut.Ah) : Equiv.Perm (Fin 45)) *
          ((Θ (g b : E) : CFSG.Quasithin.H13.F431.U42Aut.Ah) : Equiv.Perm (Fin 45)) *
            ((Θ fb : CFSG.Quasithin.H13.F431.U42Aut.Ah) : Equiv.Perm (Fin 45))⁻¹ =
          ((Θ (g b : E) : CFSG.Quasithin.H13.F431.U42Aut.Ah) : Equiv.Perm (Fin 45)) := by
        have h := congrArg (fun z : E =>
          ((Θ z : CFSG.Quasithin.H13.F431.U42Aut.Ah) : Equiv.Perm (Fin 45))) (hg2 b hb')
        simpa [map_mul, map_inv] using h
      rw [hΘg, mk_conj_tau (mkQ_of_mem (Θ fb).2) (δ⁻¹ l₀)] at hcomm
      exact mk_tauPerm_inj hcomm
    have hinj : Set.InjOn (fun b : Fin 4 → Bool => (δ⁻¹ : Equiv.Perm (Fin 45)) (uIdx (fun i =>
          φ (((C : Matrix (Fin 4) (Fin 4) K) *ᵥ mkBitVec K b) i))))
        ↑(Finset.univ.filter (fun b : Fin 4 → Bool => b ≠ fun _ => false)) := by
      intro b hb b' hb' h
      have hb1 : b ≠ fun _ => false := (Finset.mem_filter.1 (Finset.mem_coe.1 hb)).2
      have hb2 : b' ≠ fun _ => false := (Finset.mem_filter.1 (Finset.mem_coe.1 hb')).2
      exact mk_fixed_inj φ hσ (mk_K_two φ) C hC' hb1 hb2 (δ⁻¹.injective h)
    have hcard : (Finset.univ.filter (fun b : Fin 4 → Bool => b ≠ fun _ => false)).card = 15 := by
      decide +kernel
    calc 15 = (Finset.univ.filter (fun b : Fin 4 → Bool => b ≠ fun _ => false)).card :=
          hcard.symm
      _ ≤ _ := Finset.card_le_card_of_injOn _ hmem hinj

end CFSG.Quasithin.SimsF5
