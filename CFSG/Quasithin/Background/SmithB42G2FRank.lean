module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bInvol
public import CFSG.Quasithin.Background.SmithB42G2TenProd
public import CFSG.Quasithin.Background.SmithB42G2Rank

public section

namespace CFSG.Quasithin.B42G2F

open Matrix CFSG.QuasithinUnique.Setup.X7 CFSG.QuasithinUnique.Setup.X7b
open CFSG.QuasithinUnique.Setup.X7a (kron kron_apply kron_mul kron_one)
open scoped Kronecker

section Sub

variable {k V W : Type*} [Field k] [AddCommGroup V] [Module k V] [FiniteDimensional k V]
  [AddCommGroup W] [Module k W]

theorem finrank_map_le_add (f : V →ₗ[k] W) {S T : Submodule k V} (hST : S ≤ T) :
    Module.finrank k (T.map f) + Module.finrank k S ≤
      Module.finrank k (S.map f) + Module.finrank k T := by
  obtain ⟨C₀, hC₀⟩ := Submodule.exists_isCompl S
  set C := C₀ ⊓ T with hC
  have hsup : S ⊔ C = T := by
    rw [hC, ← sup_inf_assoc_of_le C₀ hST, hC₀.sup_eq_top, top_inf_eq]
  have hinf : S ⊓ C = ⊥ := by
    rw [eq_bot_iff, hC]
    exact (inf_le_inf_left S inf_le_left).trans hC₀.inf_eq_bot.le
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq S C
  rw [hsup, hinf, finrank_bot] at h1
  have h2 : T.map f ≤ S.map f ⊔ C.map f := by
    rw [← hsup, Submodule.map_sup]
  have h3 := Submodule.finrank_mono h2
  have h4 := Submodule.finrank_add_le_finrank_add_finrank (S.map f) (C.map f)
  have h5 := Submodule.finrank_map_le f C
  omega

end Sub

section KronDep

variable {k : Type*} [Field k] {ι : Type*} [Fintype ι] [DecidableEq ι] {κ : ι → Type*}
  [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]

omit [DecidableEq ι] [∀ i, Fintype (κ i)] in
theorem kron_permMat_dep (σ : ∀ i, Equiv.Perm (κ i)) :
    kron (fun i => permMat k (σ i)) = permMat k (Equiv.piCongrRight σ) := by
  ext y x
  rw [kron_apply]
  simp only [permMat, Matrix.of_apply]
  rw [Finset.prod_boole]
  simp [funext_iff]

theorem rank_kron_sub_one_dep [CharP k 2] [∀ i, Nonempty (κ i)]
    (z : ∀ i, Matrix (κ i) (κ i) k) (hz : ∀ i, z i * z i = 1) :
    (kron z - 1).rank * 2 + ∏ i, (Fintype.card (κ i) - 2 * (z i - 1).rank) =
      ∏ i, Fintype.card (κ i) := by
  classical
  choose σ P Q hσ hPQ hQP hzP using fun i => exists_perm_conj (hz i)
  have hz' : ∀ i, z i - 1 = P i * (permMat k (σ i) - 1) * Q i := fun i => by
    have h1 : z i = P i * permMat k (σ i) * Q i := by
      calc z i = z i * (P i * Q i) := by rw [hPQ, Matrix.mul_one]
        _ = (z i * P i) * Q i := by rw [Matrix.mul_assoc]
        _ = P i * permMat k (σ i) * Q i := by rw [hzP]
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hPQ, ← h1]
  have hfix : ∀ i, Fintype.card {y // σ i y = y} =
      Fintype.card (κ i) - 2 * (z i - 1).rank := fun i => by
    have h1 := rank_permMat_sub_one (k := k) (σ i) (hσ i)
    rw [hz' i, rank_conj_eq _ _ _ (hQP i)]
    omega
  have hPk : kron P * kron Q = 1 := by rw [← kron_mul]; simp only [hPQ]; exact kron_one
  have hQk : kron Q * kron P = 1 := by rw [← kron_mul]; simp only [hQP]; exact kron_one
  have hzk : kron z * kron P = kron P * permMat k (Equiv.piCongrRight σ) := by
    rw [← kron_permMat_dep, ← kron_mul, ← kron_mul]
    congr 1
    funext i
    exact hzP i
  have hz'' : kron z - 1 = kron P * (permMat k (Equiv.piCongrRight σ) - 1) * kron Q := by
    have h1 : kron z = kron P * permMat k (Equiv.piCongrRight σ) * kron Q := by
      calc kron z = kron z * (kron P * kron Q) := by rw [hPk, Matrix.mul_one]
        _ = (kron z * kron P) * kron Q := by rw [Matrix.mul_assoc]
        _ = kron P * permMat k (Equiv.piCongrRight σ) * kron Q := by rw [hzk]
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hPk, ← h1]
  have hσk : Equiv.piCongrRight σ * Equiv.piCongrRight σ = 1 := by
    ext x i
    simp only [Equiv.Perm.mul_apply, Equiv.Perm.one_apply, Equiv.piCongrRight_apply]
    have := congrArg (fun p : Equiv.Perm (κ i) => p (x i)) (hσ i)
    simpa [Equiv.Perm.mul_apply] using this
  have h2 := rank_permMat_sub_one (k := k) (Equiv.piCongrRight σ) hσk
  rw [hz'', rank_conj_eq _ _ _ hQk]
  have hcardfix : Fintype.card {x : (∀ i, κ i) // Equiv.piCongrRight σ x = x} =
      ∏ i, Fintype.card {y // σ i y = y} := by
    rw [← Fintype.card_pi]
    refine Fintype.card_congr ?_
    refine (Equiv.subtypeEquivRight fun x => ?_).trans
      (Equiv.subtypePiEquivPi (p := fun i y => σ i y = y))
    simp [funext_iff]
  rw [hcardfix] at h2
  simp only [hfix] at h2
  simpa [Fintype.card_pi] using h2

end KronDep

section Kron2

variable {k : Type*} [Field k] {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n]
  [DecidableEq n]

omit [Fintype m] [Fintype n] in
theorem kronecker_permMat (σ : Equiv.Perm m) (τ : Equiv.Perm n) :
    permMat k σ ⊗ₖ permMat k τ = permMat k (σ.prodCongr τ) := by
  ext ⟨a, b⟩ ⟨c, d⟩
  simp only [Matrix.kroneckerMap_apply, permMat, Matrix.of_apply, Equiv.prodCongr_apply,
    Prod.map_apply, Prod.mk.injEq]
  by_cases h1 : σ c = a <;> by_cases h2 : τ d = b <;> simp [h1, h2]

theorem sub_one_eq_conj (X R R' S₀ : Matrix m m k) (hRR : R * R' = 1) (hXR : X * R = R * S₀) :
    X - 1 = R * (S₀ - 1) * R' := by
  have h1 : X = R * S₀ * R' := by
    calc X = X * (R * R') := by rw [hRR, Matrix.mul_one]
      _ = (X * R) * R' := by rw [Matrix.mul_assoc]
      _ = R * S₀ * R' := by rw [hXR]
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hRR, ← h1]

theorem card_fix_eq_of_conj (X R R' : Matrix m m k) (ρ : Equiv.Perm m) (hρ : ρ * ρ = 1)
    (hRR : R * R' = 1) (hR'R : R' * R = 1) (hXR : X * R = R * permMat k ρ) :
    Fintype.card {y // ρ y = y} = Fintype.card m - 2 * (X - 1).rank := by
  have h1 := rank_permMat_sub_one (k := k) ρ hρ
  rw [sub_one_eq_conj X R R' _ hRR hXR, rank_conj_eq _ _ _ hR'R]
  omega

theorem rank_kronecker_sub_one [CharP k 2] [Nonempty m] [Nonempty n] (A : Matrix m m k)
    (B : Matrix n n k) (hA : A * A = 1) (hB : B * B = 1) :
    (A ⊗ₖ B - 1).rank * 2 +
        (Fintype.card m - 2 * (A - 1).rank) * (Fintype.card n - 2 * (B - 1).rank) =
      Fintype.card m * Fintype.card n := by
  classical
  obtain ⟨σ, P, P', hσ, hPP, hP'P, hAP⟩ := exists_perm_conj hA
  obtain ⟨τ, Q, Q', hτ, hQQ, hQ'Q, hBQ⟩ := exists_perm_conj hB
  have hPQk : (P ⊗ₖ Q) * (P' ⊗ₖ Q') = 1 := by
    rw [← Matrix.mul_kronecker_mul, hPP, hQQ, Matrix.one_kronecker_one]
  have hPQk' : (P' ⊗ₖ Q') * (P ⊗ₖ Q) = 1 := by
    rw [← Matrix.mul_kronecker_mul, hP'P, hQ'Q, Matrix.one_kronecker_one]
  have hABk : (A ⊗ₖ B) * (P ⊗ₖ Q) = (P ⊗ₖ Q) * permMat k (σ.prodCongr τ) := by
    rw [← kronecker_permMat, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, hAP, hBQ]
  have hστ : σ.prodCongr τ * σ.prodCongr τ = 1 := by
    ext ⟨a, b⟩
    · have := congrArg (fun p : Equiv.Perm m => p a) hσ
      simpa [Equiv.Perm.mul_apply] using this
    · have := congrArg (fun p : Equiv.Perm n => p b) hτ
      simpa [Equiv.Perm.mul_apply] using this
  have h1 := rank_permMat_sub_one (k := k) (σ.prodCongr τ) hστ
  rw [← rank_conj_eq _ _ _ hPQk', ← sub_one_eq_conj _ _ _ _ hPQk hABk] at h1
  have hfix2 : Fintype.card {x : m × n // σ.prodCongr τ x = x} =
      Fintype.card {y // σ y = y} * Fintype.card {y // τ y = y} := by
    rw [← Fintype.card_prod]
    refine Fintype.card_congr
      { toFun := fun x => (⟨x.1.1, congrArg Prod.fst x.2⟩, ⟨x.1.2, congrArg Prod.snd x.2⟩)
        invFun := fun y => ⟨(y.1.1, y.2.1), by simp [Equiv.prodCongr_apply, y.1.2, y.2.2]⟩
        left_inv := fun x => rfl
        right_inv := fun y => rfl }
  rw [hfix2, card_fix_eq_of_conj A P P' σ hσ hPP hP'P hAP,
    card_fix_eq_of_conj B Q Q' τ hτ hQQ hQ'Q hBQ, Fintype.card_prod] at h1
  exact h1

end Kron2

section General

variable {k : Type*} [Field k]

theorem rank_fromBlocks_one_zero' (r s : ℕ) :
    (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) k) 0 0
      (0 : Matrix (Fin s) (Fin s) k)).rank = r := by
  classical
  have h : (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) k) 0 0
      (0 : Matrix (Fin s) (Fin s) k)) =
      Matrix.diagonal (Sum.elim (fun _ : Fin r => (1 : k)) (fun _ : Fin s => (0 : k))) := by
    rw [← Matrix.fromBlocks_diagonal, Matrix.diagonal_one, Matrix.diagonal_zero]
  rw [h, Matrix.rank_diagonal, Fintype.card_subtype, Finset.card_filter, Fintype.sum_sum_type]
  simp

theorem rank_map_ringHom {L : Type*} [Field L] (φ : k →+* L) {m : Type*} [Fintype m]
    [DecidableEq m] (A : Matrix m m k) : (A.map φ).rank = A.rank := by
  classical
  obtain ⟨V, U, e, hV, hU, h⟩ := Matrix.exists_rank_normal_form A
  have hVf : IsUnit (V.map φ).det := (Matrix.isUnit_iff_isUnit_det _).mp (hV.map φ.mapMatrix)
  have hUf : IsUnit (U.map φ).det := (Matrix.isUnit_iff_isUnit_det _).mp (hU.map φ.mapMatrix)
  have hE : (A.map φ).rank = ((V.map φ) * (A.map φ) * (U.map φ)).rank := by
    rw [Matrix.rank_mul_eq_left_of_isUnit_det _ _ hUf,
      Matrix.rank_mul_eq_right_of_isUnit_det _ _ hVf]
  have h1 : (V * A * U).map φ = ((Matrix.fromBlocks (1 : Matrix (Fin A.rank) (Fin A.rank) k) 0 0
      (0 : Matrix (Fin (Fintype.card m - A.rank)) (Fin (Fintype.card m - A.rank)) k)).submatrix
        e e).map φ := by rw [h]
  simp only [Matrix.map_mul, ← Matrix.submatrix_map, Matrix.fromBlocks_map,
    Matrix.map_one _ (map_zero φ) (map_one φ), Matrix.map_zero _ (map_zero φ)] at h1
  rw [hE, h1, Matrix.rank_submatrix, rank_fromBlocks_one_zero']

theorem rank_map_sub_one {L : Type*} [Field L] (φ : k →+* L) {m : Type*} [Fintype m]
    [DecidableEq m] (A : Matrix m m k) : (A.map φ - 1).rank = (A - 1).rank := by
  rw [← rank_map_ringHom φ (A - 1), Matrix.map_sub _ (fun a b => map_sub φ a b),
    Matrix.map_one _ (map_zero φ) (map_one φ)]

variable {G : Type*} [Group G] {κ ν : Type*} [Fintype κ] [DecidableEq κ] [Fintype ν]
  [DecidableEq ν] {R : G →* Matrix κ κ k} {ι : ν → κ} {S : Matrix κ ν k}

open CFSG.Quasithin.B42G2Ten in
theorem finrank_map_le_rank_pivotRep (h : IsPivot R ι S) (g : G) (V : Submodule k (κ → k))
    (hV : ∀ w ∈ V, ∃ x, S.mulVec x = w) :
    Module.finrank k (V.map (R g - 1).mulVecLin) ≤ (pivotRep h g - 1).rank := by
  have hle : V.map (R g - 1).mulVecLin ≤
      (LinearMap.range (pivotRep h g - 1).mulVecLin).map S.mulVecLin := by
    rintro _ ⟨w, hw, rfl⟩
    obtain ⟨x, rfl⟩ := hV w hw
    refine ⟨(pivotRep h g - 1).mulVec x, ⟨x, rfl⟩, ?_⟩
    simp only [Matrix.mulVecLin_apply, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_sub,
      sec_mulVec_pivotRep]
  exact (Submodule.finrank_mono hle).trans (Submodule.finrank_map_le _ _)

end General

section Letters

open CFSG.Open CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.B42G2Ten
  CFSG.Quasithin.Vol2.Ch11.G2Q8

variable {F : Type} [Field F] [CharP F 2]

theorem card_Ix3 : Fintype.card Ix3 = 6 := rfl

theorem card_LIdx : Fintype.card LIdx = 14 := rfl

theorem repQ_mul_self {z : ↥(cayleyGroup F)} (hz : z * z = 1) : repQ z * repQ z = 1 := by
  rw [← map_mul, hz, map_one]

theorem repLie_mul_self {z : ↥(cayleyGroup F)} (hz : z * z = 1) : repLie z * repLie z = 1 := by
  rw [← map_mul, hz, map_one]

theorem repSt_mul_self {z : ↥(cayleyGroup F)} (hz : z * z = 1) : repSt z * repSt z = 1 := by
  rw [← map_mul, hz, map_one]

theorem two_le_rank_repQ [Finite F] {z : ↥(cayleyGroup F)} (hz : z * z = 1) (hz1 : z ≠ 1) :
    2 ≤ (repQ z - 1).rank := by
  have hcard := CFSG.Quasithin.B42G2.card_fixQ_le hz hz1
  set N := (repQ z - 1).mulVecLin with hN
  have hker : Nat.card (fixQ z) = Nat.card (LinearMap.ker N) :=
    Nat.card_congr (Equiv.subtypeEquivRight fun w => by
      rw [mem_fixQ, LinearMap.mem_ker, hN, Matrix.mulVecLin_apply, Matrix.sub_mulVec,
        Matrix.one_mulVec, sub_eq_zero, repQ_mulVec])
  have hpow : Nat.card (LinearMap.ker N) = Nat.card F ^ Module.finrank F (LinearMap.ker N) :=
    Module.natCard_eq_pow_finrank
  have hrn := LinearMap.finrank_range_add_finrank_ker N
  rw [Module.finrank_fintype_fun_eq_card, card_Ix3] at hrn
  have hq : 1 < Nat.card F := Finite.one_lt_card
  have hle : Module.finrank F (LinearMap.ker N) ≤ 4 := by
    rw [hker, hpow] at hcard
    exact (Nat.pow_le_pow_iff_right hq).mp hcard
  change 2 ≤ Module.finrank F (LinearMap.range N)
  omega

theorem rank_repQ_le {z : ↥(cayleyGroup F)} (hz : z * z = 1) : (repQ z - 1).rank ≤ 3 := by
  have := two_mul_rank_le (repQ z) (repQ_mul_self hz)
  rw [card_Ix3] at this
  omega

variable (F) in
@[expose] def altSub : Submodule F (Ix3 × Ix3 → F) where
  carrier := {T | (∀ i j, T (i, j) = T (j, i)) ∧ ∀ i, T (i, i) = 0}
  add_mem' {T T'} hT hT' := ⟨fun i j => by simp only [Pi.add_apply, hT.1 i j, hT'.1 i j],
    fun i => by simp only [Pi.add_apply, hT.2 i, hT'.2 i, add_zero]⟩
  zero_mem' := ⟨fun _ _ => rfl, fun _ => rfl⟩
  smul_mem' c T hT := ⟨fun i j => by simp only [Pi.smul_apply, hT.1 i j],
    fun i => by simp only [Pi.smul_apply, hT.2 i, smul_zero]⟩

omit [CharP F 2] in
theorem lieSub_le_altSub : lieSub F ≤ altSub F := fun _ hT => ⟨hT.1, hT.2.1⟩

variable (F) in
@[expose] def contr : (Ix3 × Ix3 → F) →ₗ[F] F where
  toFun T := T (.inl 0, .inr 0) + T (.inl 1, .inr 1) + T (.inl 2, .inr 2)
  map_add' T T' := by simp only [Pi.add_apply]; ring
  map_smul' c T := by simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

omit [CharP F 2] in
theorem lieSub_eq_inf : lieSub F = altSub F ⊓ LinearMap.ker (contr F) := by
  ext T
  simp only [Submodule.mem_inf, LinearMap.mem_ker]
  exact ⟨fun h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩, fun h => ⟨h.1.1, h.1.2, h.2⟩⟩

omit [CharP F 2] in
theorem finrank_altSub_le : Module.finrank F (altSub F) ≤ Module.finrank F (lieSub F) + 1 := by
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq (altSub F) (LinearMap.ker (contr F))
  rw [← lieSub_eq_inf] at h1
  have h2 := LinearMap.finrank_range_add_finrank_ker (contr F)
  have h3 : Module.finrank F (LinearMap.range (contr F)) ≤ 1 := by
    have := Submodule.finrank_le (LinearMap.range (contr F))
    rwa [Module.finrank_self] at this
  have h4 := Submodule.finrank_le (altSub F ⊔ LinearMap.ker (contr F))
  omega

omit [CharP F 2] in
theorem toM_kronecker (R : Matrix Ix3 Ix3 F) (T : Ix3 × Ix3 → F) :
    toM ((R ⊗ₖ R).mulVec T) = R * toM T * Rᵀ := by
  ext i j
  simp only [toM_apply, Matrix.mulVec, dotProduct, Matrix.kroneckerMap_apply,
    Fintype.sum_prod_type, Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
  ring

theorem kronecker_mem_altSub (R : Matrix Ix3 Ix3 F) {T : Ix3 × Ix3 → F} (hT : T ∈ altSub F) :
    (R ⊗ₖ R).mulVec T ∈ altSub F := by
  have h := isAltM_conj R (X := toM T) ⟨fun i j => hT.1 i j, fun i => hT.2 i⟩
  rw [← toM_kronecker] at h
  exact ⟨fun i j => h.1 i j, fun i => h.2 i⟩

omit [CharP F 2] in
theorem permMat_kronecker_mulVec (σ : Equiv.Perm Ix3) (hσ : ∀ x, σ (σ x) = x)
    (T : Ix3 × Ix3 → F) (q : Ix3 × Ix3) :
    (permMat F σ ⊗ₖ permMat F σ).mulVec T q = T (σ q.1, σ q.2) := by
  rw [kronecker_permMat, permMat_mulVec_apply]
  have hs : ∀ x, σ.symm x = σ x := fun x => by
    rw [Equiv.symm_apply_eq, hσ]
  rw [Equiv.prodCongr_symm]
  obtain ⟨a, b⟩ := q
  change T (σ.symm a, σ.symm b) = T (σ a, σ b)
  rw [hs, hs]

omit [CharP F 2] in
theorem permMat_kronecker_wedgeT (σ : Equiv.Perm Ix3) (hσ : ∀ x, σ (σ x) = x) (a b : Ix3) :
    (permMat F σ ⊗ₖ permMat F σ).mulVec (wedgeT a b) = wedgeT (σ a) (σ b) := by
  funext q
  rw [permMat_kronecker_mulVec σ hσ, wedgeT_apply, wedgeT_apply]
  obtain ⟨c, d⟩ := q
  have e : ∀ x y : Ix3, (σ x = y ↔ x = σ y) := fun x y =>
    ⟨fun h => by rw [← h, hσ], fun h => by rw [h, hσ]⟩
  simp only [Prod.mk.injEq, e]

omit [CharP F 2] in
theorem wedgeT_mem_altSub {a b : Ix3} (hab : a ≠ b) : wedgeT a b ∈ altSub F := by
  refine ⟨fun i j => ?_, fun i => ?_⟩
  · simp only [wedgeT_apply, Prod.mk.injEq]
    rw [add_comm]
    congr 1 <;> simp only [and_comm]
  · simp only [wedgeT_apply, Prod.mk.injEq]
    have h1 : ¬ (i = a ∧ i = b) := fun h => hab (h.1.symm.trans h.2)
    have h2 : ¬ (i = b ∧ i = a) := fun h => hab (h.2.symm.trans h.1)
    simp [h1, h2]

omit [CharP F 2] in
theorem wedgeT_pt (a b c d : Ix3) :
    wedgeT a b (c, d) = (if c = a ∧ d = b then (1 : F) else 0) +
      (if c = b ∧ d = a then 1 else 0) := by
  simp only [wedgeT_apply, Prod.mk.injEq]

omit [CharP F 2] in
theorem card_ne_ne (a b : Ix3) (hab : a ≠ b) :
    Fintype.card {w : Ix3 // w ≠ a ∧ w ≠ b} = 4 := by
  classical
  rw [Fintype.card_subtype]
  have e : (Finset.univ.filter fun w : Ix3 => w ≠ a ∧ w ≠ b) = (Finset.univ.erase a).erase b := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
    tauto
  rw [e, Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hab.symm, Finset.mem_univ _⟩),
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, card_Ix3]

omit [CharP F 2] in
theorem card_ne_ne_ne_ne (a b c d : Ix3) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c)
    (hbd : b ≠ d) (hcd : c ≠ d) :
    Fintype.card {w : Ix3 // w ≠ a ∧ w ≠ b ∧ w ≠ c ∧ w ≠ d} = 2 := by
  classical
  rw [Fintype.card_subtype]
  have e : (Finset.univ.filter fun w : Ix3 => w ≠ a ∧ w ≠ b ∧ w ≠ c ∧ w ≠ d) =
      (((Finset.univ.erase a).erase b).erase c).erase d := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
    tauto
  rw [e, Finset.card_erase_of_mem, Finset.card_erase_of_mem, Finset.card_erase_of_mem,
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, card_Ix3]
  · exact Finset.mem_erase.mpr ⟨hab.symm, Finset.mem_univ _⟩
  · exact Finset.mem_erase.mpr ⟨hbc.symm, Finset.mem_erase.mpr ⟨hac.symm, Finset.mem_univ _⟩⟩
  · exact Finset.mem_erase.mpr ⟨hcd.symm, Finset.mem_erase.mpr ⟨hbd.symm,
      Finset.mem_erase.mpr ⟨had.symm, Finset.mem_univ _⟩⟩⟩

omit [CharP F 2] in
theorem wedgeT_sub_pt_zero (σ : Equiv.Perm Ix3) (a b c d : Ix3)
    (h1 : ¬ (c = σ a ∧ d = σ b)) (h2 : ¬ (c = σ b ∧ d = σ a)) (h3 : ¬ (c = a ∧ d = b))
    (h4 : ¬ (c = b ∧ d = a)) : (wedgeT (σ a) (σ b) - wedgeT a b : Ix3 × Ix3 → F) (c, d) = 0 := by
  rw [Pi.sub_apply, wedgeT_pt, wedgeT_pt, ite_eq_right h1, ite_eq_right h2, ite_eq_right h3,
    ite_eq_right h4]
  simp

omit [CharP F 2] in
theorem wedgeT_sub_pt_self (σ : Equiv.Perm Ix3) (a b d : Ix3) (h1 : a ≠ σ a) (h2 : d ≠ σ a)
    (h3 : a ≠ b) : (wedgeT (σ a) (σ b) - wedgeT a b : Ix3 × Ix3 → F) (a, d) =
      -(if d = b then 1 else 0) := by
  rw [Pi.sub_apply, wedgeT_pt, wedgeT_pt,
    ite_eq_right (show ¬ (a = σ a ∧ d = σ b) from fun h => h1 h.1),
    ite_eq_right (show ¬ (a = σ b ∧ d = σ a) from fun h => h2 h.2),
    ite_eq_right (show ¬ (a = b ∧ d = a) from fun h => h3 h.1)]
  simp

omit [CharP F 2] in
theorem six_le_finrank_altSub_map_perm (σ : Equiv.Perm Ix3) (hσ : ∀ x, σ (σ x) = x)
    (hmov : 4 ≤ (Finset.univ.filter fun x => σ x ≠ x).card) :
    6 ≤ Module.finrank F ((altSub F).map (permMat F σ ⊗ₖ permMat F σ - 1).mulVecLin) := by
  classical
  set Mv := Finset.univ.filter fun x : Ix3 => σ x ≠ x with hMv
  have hmemMv : ∀ x, x ∈ Mv ↔ σ x ≠ x := fun x => by simp [hMv]
  obtain ⟨x₁, hx₁⟩ : Mv.Nonempty := Finset.card_pos.mp (by omega)
  have d1 : x₁ ≠ σ x₁ := ((hmemMv x₁).mp hx₁).symm
  have hy₁M : σ x₁ ∈ Mv.erase x₁ := Finset.mem_erase.mpr ⟨d1.symm, (hmemMv _).mpr (by
    rw [hσ]; exact d1)⟩
  have hne2 : ((Mv.erase x₁).erase (σ x₁)).Nonempty := by
    have h1 := Finset.card_erase_of_mem hx₁
    have h2 := Finset.card_erase_of_mem hy₁M
    exact Finset.card_pos.mp (by omega)
  obtain ⟨x₂, hx₂⟩ := hne2
  obtain ⟨hx₂y₁, hx₂'⟩ := Finset.mem_erase.mp hx₂
  obtain ⟨hx₂x₁, hx₂M⟩ := Finset.mem_erase.mp hx₂'
  have d2 : x₁ ≠ x₂ := hx₂x₁.symm
  have d3 : x₁ ≠ σ x₂ := fun h => hx₂y₁ (by rw [h, hσ])
  have d4 : σ x₁ ≠ x₂ := hx₂y₁.symm
  have d5 : σ x₁ ≠ σ x₂ := fun h => hx₂x₁ (by
    have := congrArg σ h
    rwa [hσ, hσ, eq_comm] at this)
  have d6 : x₂ ≠ σ x₂ := ((hmemMv x₂).mp hx₂M).symm
  set N := permMat F σ ⊗ₖ permMat F σ - 1 with hN
  have hNw : ∀ a b, N.mulVec (wedgeT a b) = wedgeT (σ a) (σ b) - wedgeT a b := fun a b => by
    rw [hN, Matrix.sub_mulVec, Matrix.one_mulVec, permMat_kronecker_wedgeT σ hσ]
  let I := {w : Ix3 // w ≠ x₁ ∧ w ≠ σ x₁} ⊕
    {w : Ix3 // w ≠ x₁ ∧ w ≠ σ x₁ ∧ w ≠ x₂ ∧ w ≠ σ x₂}
  let a₀ : I → Ix3 := Sum.elim (fun _ => x₁) (fun _ => x₂)
  let b₀ : I → Ix3 := Sum.elim (fun w => w.1) (fun w => w.1)
  have hab₀ : ∀ i, a₀ i ≠ b₀ i := by
    rintro (w | w)
    · exact fun h => w.2.1 h.symm
    · exact fun h => w.2.2.2.1 h.symm
  let v : I → (Ix3 × Ix3 → F) := fun i => N.mulVec (wedgeT (a₀ i) (b₀ i))
  have hσw : ∀ w : {w : Ix3 // w ≠ x₁ ∧ w ≠ σ x₁ ∧ w ≠ x₂ ∧ w ≠ σ x₂},
      σ w.1 ≠ x₁ ∧ σ w.1 ≠ x₂ := fun w => by
    obtain ⟨w, h1, h2, h3, h4⟩ := w
    refine ⟨fun h => h2 ?_, fun h => h4 ?_⟩
    · rw [← h, hσ]
    · rw [← h, hσ]
  have heval : ∀ i j : I, v i (a₀ j, b₀ j) = if i = j then -1 else 0 := by
    rintro (w | w) (w' | w')
    · change (N.mulVec (wedgeT x₁ w.1)) (x₁, w'.1) = _
      rw [hNw, wedgeT_sub_pt_self σ x₁ w.1 w'.1 d1 w'.2.2 (fun h => w.2.1 h.symm)]
      by_cases hww : w = w'
      · subst hww
        simp
      · rw [ite_eq_right (fun h => hww (Subtype.ext h.symm)),
          ite_eq_right (fun h => hww (Sum.inl_injective h))]
        simp
    · change (N.mulVec (wedgeT x₁ w.1)) (x₂, w'.1) = _
      rw [hNw, wedgeT_sub_pt_zero σ x₁ w.1 x₂ w'.1 (fun h => d4 h.1.symm)
        (fun h => w'.2.2.1 h.2) (fun h => d2 h.1.symm) (fun h => w'.2.1 h.2),
        ite_eq_right (fun h => by cases h)]
    · change (N.mulVec (wedgeT x₂ w.1)) (x₁, w'.1) = _
      rw [hNw, wedgeT_sub_pt_zero σ x₂ w.1 x₁ w'.1 (fun h => d3 h.1)
        (fun h => (hσw w).1 h.1.symm) (fun h => d2 h.1) (fun h => w.2.1 h.1.symm),
        ite_eq_right (fun h => by cases h)]
    · change (N.mulVec (wedgeT x₂ w.1)) (x₂, w'.1) = _
      rw [hNw, wedgeT_sub_pt_self σ x₂ w.1 w'.1 d6 w'.2.2.2.2 (fun h => w.2.2.2.1 h.symm)]
      by_cases hww : w = w'
      · subst hww
        simp
      · rw [ite_eq_right (fun h => hww (Subtype.ext h.symm)),
          ite_eq_right (fun h => hww (Sum.inr_injective h))]
        simp
  have hli : LinearIndependent F v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg j
    have h1 := congrFun hg (a₀ j, b₀ j)
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, heval, Pi.zero_apply,
      mul_ite, mul_neg, mul_one, mul_zero] at h1
    rw [Finset.sum_ite_eq'] at h1
    simpa using h1
  have hv : ∀ i, v i ∈ (altSub F).map N.mulVecLin := fun i =>
    ⟨wedgeT (a₀ i) (b₀ i), wedgeT_mem_altSub (hab₀ i), rfl⟩
  let v' : I → ↥((altSub F).map N.mulVecLin) := fun i => ⟨v i, hv i⟩
  have hli' : LinearIndependent F v' :=
    LinearIndependent.of_comp (Submodule.subtype _) hli
  have hcard : Fintype.card I = 6 := by
    rw [Fintype.card_sum, card_ne_ne x₁ (σ x₁) d1,
      card_ne_ne_ne_ne x₁ (σ x₁) x₂ (σ x₂) d1 d2 d3 d4 d5 d6]
  have := hli'.fintype_card_le_finrank
  rwa [hcard] at this

theorem six_le_finrank_altSub_map (P : Matrix Ix3 Ix3 F) (hP : P * P = 1)
    (h2 : 2 ≤ (P - 1).rank) :
    6 ≤ Module.finrank F ((altSub F).map (P ⊗ₖ P - 1).mulVecLin) := by
  classical
  obtain ⟨σ, R, R', hσ, hRR, hR'R, hPR⟩ := exists_perm_conj hP
  have hσσ : ∀ x, σ (σ x) = x := fun x => by
    have := congrArg (fun p : Equiv.Perm Ix3 => p x) hσ
    simpa [Equiv.Perm.mul_apply] using this
  have hrk : (permMat F σ - 1).rank = (P - 1).rank := by
    rw [sub_one_eq_conj P R R' _ hRR hPR, rank_conj_eq _ _ _ hR'R]
  have hfix := rank_permMat_sub_one (k := F) σ hσ
  have hmov : 4 ≤ (Finset.univ.filter fun x => σ x ≠ x).card := by
    have h3 := Finset.card_filter_add_card_filter_not (s := Finset.univ)
      (fun x : Ix3 => σ x = x)
    rw [Fintype.card_subtype] at hfix
    rw [Finset.card_univ, card_Ix3] at h3
    rw [card_Ix3] at hfix
    simp only [ne_eq]
    omega
  have hperm := six_le_finrank_altSub_map_perm (F := F) σ hσσ hmov
  have hRk : (R ⊗ₖ R) * (R' ⊗ₖ R') = 1 := by
    rw [← Matrix.mul_kronecker_mul, hRR, Matrix.one_kronecker_one]
  have hR'k : (R' ⊗ₖ R') * (R ⊗ₖ R) = 1 := by
    rw [← Matrix.mul_kronecker_mul, hR'R, Matrix.one_kronecker_one]
  have hPk : (P ⊗ₖ P) * (R ⊗ₖ R) = (R ⊗ₖ R) * (permMat F σ ⊗ₖ permMat F σ) := by
    rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, hPR]
  have hconj := sub_one_eq_conj _ _ _ _ hRk hPk
  have halt : (altSub F).map (R' ⊗ₖ R').mulVecLin = altSub F := by
    apply le_antisymm
    · rintro _ ⟨T, hT, rfl⟩
      exact kronecker_mem_altSub R' hT
    · intro T hT
      refine ⟨(R ⊗ₖ R).mulVec T, kronecker_mem_altSub R hT, ?_⟩
      rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hR'k, Matrix.one_mulVec]
  have hmap : (altSub F).map (P ⊗ₖ P - 1).mulVecLin =
      ((altSub F).map (permMat F σ ⊗ₖ permMat F σ - 1).mulVecLin).map (R ⊗ₖ R).mulVecLin := by
    rw [hconj, Matrix.mulVecLin_mul, Matrix.mulVecLin_mul, Submodule.map_comp,
      Submodule.map_comp, halt]
  rw [hmap]
  set Y := (altSub F).map (permMat F σ ⊗ₖ permMat F σ - 1).mulVecLin
  have hY : (Y.map (R ⊗ₖ R).mulVecLin).map (R' ⊗ₖ R').mulVecLin = Y := by
    rw [← Submodule.map_comp, ← Matrix.mulVecLin_mul, hR'k, Matrix.mulVecLin_one,
      Submodule.map_id]
  have h4 := Submodule.finrank_map_le (R' ⊗ₖ R').mulVecLin (Y.map (R ⊗ₖ R).mulVecLin)
  rw [hY] at h4
  omega

theorem secL_restrict {w : Ix3 × Ix3 → F} (hw : w ∈ lieSub F) :
    (secL F).mulVec (fun p => w (lP p)) = w := by
  have h := eq_zero_of_lP (z := (secL F).mulVec (fun p => w (lP p)) - w)
    (sub_mem (secL_mulVec_mem _) hw) fun p => by
      rw [Pi.sub_apply, sec_mulVec_restrict isPivot_lie, sub_self]
  exact sub_eq_zero.mp h

theorem five_le_rank_repLie [Finite F] {z : ↥(cayleyGroup F)} (hz : z * z = 1) (hz1 : z ≠ 1) :
    5 ≤ (repLie z - 1).rank := by
  have hA := six_le_finrank_altSub_map (repQ z) (repQ_mul_self hz) (two_le_rank_repQ hz hz1)
  have hle := finrank_map_le_add (repQ z ⊗ₖ repQ z - 1).mulVecLin (lieSub_le_altSub (F := F))
  have hcod := finrank_altSub_le (F := F)
  have hpiv := finrank_map_le_rank_pivotRep isPivot_lie z (lieSub F)
    (fun w hw => ⟨fun p => w (lP p), secL_restrict hw⟩)
  have e : rep2 z = repQ z ⊗ₖ repQ z := rfl
  rw [e] at hpiv
  have : (repLie z - 1) = (pivotRep isPivot_lie z - 1) := rfl
  rw [this]
  omega

theorem eight_le_rank_repSt [Finite F] {z : ↥(cayleyGroup F)} (hz : z * z = 1) (hz1 : z ≠ 1) :
    8 ≤ (repSt z - 1).rank := by
  have h1 := rank_kronecker_sub_one (repQ z) (repLie z) (repQ_mul_self hz) (repLie_mul_self hz)
  rw [card_Ix3, card_LIdx] at h1
  have ha := two_le_rank_repQ hz hz1
  have hb := two_mul_rank_le (repLie z) (repLie_mul_self hz)
  rw [card_LIdx] at hb
  have hprod : (6 - 2 * (repQ z - 1).rank) * (14 - 2 * (repLie z - 1).rank) ≤ 2 * 14 :=
    Nat.mul_le_mul (by omega) (by omega)
  have hQL : 28 ≤ (repQ z ⊗ₖ repLie z - 1).rank := by omega
  have hle := finrank_map_le_add (repQ z ⊗ₖ repLie z - 1).mulVecLin
    (le_top : stSub F ≤ ⊤)
  have htop : Module.finrank F (⊤ : Submodule F (Ix3 × LIdx → F)) = 84 := by
    rw [finrank_top, Module.finrank_fintype_fun_eq_card]
    rfl
  have hmtop : Module.finrank F ((⊤ : Submodule F (Ix3 × LIdx → F)).map
      (repQ z ⊗ₖ repLie z - 1).mulVecLin) = (repQ z ⊗ₖ repLie z - 1).rank := by
    rw [Submodule.map_top]
    rfl
  have hpiv := finrank_map_le_rank_pivotRep isPivot_st z (stSub F)
    (fun w hw => ⟨fun π => w π.1, secSt_restrict hw⟩)
  have e : repQL z = repQ z ⊗ₖ repLie z := rfl
  rw [e] at hpiv
  have : (repSt z - 1) = (pivotRep isPivot_st z - 1) := rfl
  rw [this]
  rw [htop, hmtop, finrank_stSub] at hle
  omega

end Letters

section Numerics

theorem prod_sub_two_add_le {ι : Type*} (S : Finset ι) (n : ι → ℕ) (hn : ∀ j ∈ S, 6 ≤ n j) :
    ∏ j ∈ S, (n j - 2) + 6 ^ S.card ≤ ∏ j ∈ S, n j + 4 ^ S.card ∧
      4 ^ S.card ≤ ∏ j ∈ S, (n j - 2) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih =>
    obtain ⟨ih1, ih2⟩ := ih fun j hj => hn j (Finset.mem_insert_of_mem hj)
    have hna := hn a (Finset.mem_insert_self a S)
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.card_insert_of_notMem ha, pow_succ,
      pow_succ]
    set A := ∏ j ∈ S, n j
    set B := ∏ j ∈ S, (n j - 2)
    have h46 : 4 ^ S.card ≤ 6 ^ S.card := Nat.pow_le_pow_left (by norm_num) _
    obtain ⟨x, hx⟩ : ∃ x, A = B + x := ⟨A - B, by omega⟩
    obtain ⟨y, hy⟩ : ∃ y, n a = y + 6 := ⟨n a - 6, by omega⟩
    have hx' : 6 ^ S.card ≤ x + 4 ^ S.card := by omega
    rw [hx, hy]
    simp only [show y + 6 - 2 = y + 4 by omega]
    constructor
    · nlinarith
    · nlinarith

theorem six_mul_add_four_le {s : ℕ} (hs : 2 ≤ s) : 6 * s + 4 + 4 ^ s ≤ 6 ^ s := by
  induction s, hs using Nat.le_induction with
  | base => norm_num
  | succ s hs ih =>
    rw [pow_succ, pow_succ]
    generalize 4 ^ s = a at ih ⊢
    generalize 6 ^ s = b at ih ⊢
    omega

end Numerics

section Tensor

open CFSG.Open CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.B42G2Ten
open CFSG.QuasithinUnique.Setup.X7a (frK)

variable {F : Type} [Field F] [CharP F 2] (k : Type) [Field k] [Algebra F k] [CharP k 2] {f : ℕ}

instance (l : G2L) : Nonempty l.idx := by
  cases l
  · exact ⟨()⟩
  · exact ⟨.inl 0⟩
  · exact ⟨(0 : Fin 14)⟩
  · exact ⟨hwS⟩

theorem rep_mul_self (l : G2L) {z : ↥(cayleyGroup F)} (hz : z * z = 1) :
    l.rep z * l.rep z = 1 := by
  rw [← map_mul, hz, map_one]

theorem rank_tRep_sub_one (lab : Fin f → G2L) {z : ↥(cayleyGroup F)} (hz : z * z = 1) :
    (tRep F k lab z - 1).rank * 2 +
        ∏ j, (Fintype.card (lab j).idx - 2 * ((lab j).rep z - 1).rank) =
      ∏ j, Fintype.card (lab j).idx := by
  have e : tRep F k lab z = kron fun j => ((lab j).rep z).map (frK k (j : ℕ)) := rfl
  have h := rank_kron_sub_one_dep (k := k) (fun j => ((lab j).rep (F := F) z).map (frK k (j : ℕ)))
    (fun j => by
      rw [← Matrix.map_mul, rep_mul_self (lab j) hz, Matrix.map_one _ (map_zero _) (map_one _)])
  simp only [rank_map_sub_one] at h
  rw [e]
  exact h

theorem letter_bounds [Finite F] {z : ↥(cayleyGroup F)} (hz : z * z = 1) (hz1 : z ≠ 1)
    (l : G2L) (hl : l ≠ .one) :
    6 ≤ Fintype.card l.idx ∧ 1 ≤ (l.rep z - 1).rank ∧
      2 * (l.rep z - 1).rank ≤ Fintype.card l.idx := by
  refine ⟨?_, ?_, two_mul_rank_le _ (rep_mul_self l hz)⟩
  · cases l
    · exact absurd rfl hl
    · exact le_of_eq rfl
    · exact (by decide : 6 ≤ 14)
    · rw [show Fintype.card G2L.st.idx = 64 from card_SIdx]
      norm_num
  · cases l
    · exact absurd rfl hl
    · exact le_trans (by norm_num) (two_le_rank_repQ hz hz1)
    · exact le_trans (by norm_num) (five_le_rank_repLie hz hz1)
    · exact le_trans (by norm_num) (eight_le_rank_repSt hz hz1)

theorem card_idx_one : Fintype.card G2L.one.idx = 1 := rfl

theorem rank_one_sub_one {z : ↥(cayleyGroup F)} : (G2L.one.rep z - 1).rank = 0 := by
  have : G2L.one.rep z = (1 : Matrix G2L.one.idx G2L.one.idx F) := rfl
  rw [this, sub_self, Matrix.rank_zero]

theorem letter_one (l : G2L) (hl : l = .one) (z : ↥(cayleyGroup F)) :
    Fintype.card l.idx = 1 ∧ (l.rep z - 1).rank = 0 := by
  subst hl
  exact ⟨card_idx_one, rank_one_sub_one⟩

theorem rank_tRep_ge [Finite F] (lab : Fin f → G2L) {z : ↥(cayleyGroup F)} (hz : z * z = 1)
    (hz1 : z ≠ 1) (hs : 2 ≤ (Finset.univ.filter fun j => lab j ≠ .one).card) :
    3 * (Finset.univ.filter fun j => lab j ≠ .one).card + 2 ≤ (tRep F k lab z - 1).rank := by
  classical
  set S := Finset.univ.filter fun j => lab j ≠ .one with hS
  have h := rank_tRep_sub_one k lab hz
  set n : Fin f → ℕ := fun j => Fintype.card (lab j).idx
  set m : Fin f → ℕ := fun j => Fintype.card (lab j).idx - 2 * ((lab j).rep z - 1).rank
  have hout : ∀ j ∉ S, n j = 1 ∧ m j = 1 := fun j hj => by
    have hj' : lab j = .one := by simpa [hS] using hj
    obtain ⟨h1, h2⟩ := letter_one (lab j) hj' z
    simp only [n, m, h1, h2]
    norm_num
  have hin : ∀ j ∈ S, 6 ≤ n j ∧ m j ≤ n j - 2 := fun j hj => by
    have hj' : lab j ≠ .one := by simpa [hS] using hj
    obtain ⟨h6, h1, -⟩ := letter_bounds hz hz1 (lab j) hj'
    exact ⟨h6, by simp only [m, n]; omega⟩
  have hprodn : ∏ j, n j = ∏ j ∈ S, n j :=
    (Finset.prod_subset (Finset.subset_univ S) fun j _ hj => (hout j hj).1).symm
  have hprodm : ∏ j, m j = ∏ j ∈ S, m j :=
    (Finset.prod_subset (Finset.subset_univ S) fun j _ hj => (hout j hj).2).symm
  have hmle : ∏ j ∈ S, m j ≤ ∏ j ∈ S, (n j - 2) :=
    Finset.prod_le_prod fun j hj => (hin j hj).2
  obtain ⟨h1, -⟩ := prod_sub_two_add_le S n fun j hj => (hin j hj).1
  have h2 := six_mul_add_four_le hs
  change (tRep F k lab z - 1).rank * 2 + ∏ j, m j = ∏ j, n j at h
  rw [hprodn, hprodm] at h
  omega

theorem rank_tRep_single (lab : Fin f → G2L) (j₀ : Fin f) (hlab : ∀ j ≠ j₀, lab j = .one)
    {z : ↥(cayleyGroup F)} (hz : z * z = 1) :
    (tRep F k lab z - 1).rank = ((lab j₀).rep z - 1).rank := by
  classical
  have h := rank_tRep_sub_one k lab hz
  have hn : ∏ j, Fintype.card (lab j).idx = Fintype.card (lab j₀).idx := by
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ j₀), Finset.prod_eq_one, one_mul]
    intro j hj
    exact (letter_one (lab j) (hlab j (Finset.ne_of_mem_erase hj)) z).1
  have hm : ∏ j, (Fintype.card (lab j).idx - 2 * ((lab j).rep z - 1).rank) =
      Fintype.card (lab j₀).idx - 2 * ((lab j₀).rep z - 1).rank := by
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ j₀), Finset.prod_eq_one, one_mul]
    intro j hj
    obtain ⟨h1, h2⟩ := letter_one (lab j) (hlab j (Finset.ne_of_mem_erase hj)) z
    rw [h1, h2]
    rfl
  have hle := two_mul_rank_le _ (rep_mul_self (lab j₀) hz)
  rw [hn, hm] at h
  omega

end Tensor

end CFSG.Quasithin.B42G2F
