module

public import Certificates.Certificate715001
public import Certificates.Data.E6WeylDivisors
public import CFSG.RankThree.E6.RootLatticeTools
public import CFSG.LieType.SeitzGeneration.ExcTorusCount
public import CFSG.HardMathSupport.Timmesfeld.Steinberg.ThreeChar
public import CFSG.LieType.Chevalley.SimplyLacedCommutation
public import CFSG.LieType.Chevalley.LangRootArithmeticDet
public import CFSG.Blueprint.ChevalleyRootArtifact

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6
  CFSG.LieType.SeitzGeneration CFSG.HardMathSupport.Timmesfeld.Steinberg Certificates.E6WeylDivisors
  Certificates.E6WeylMinors
open scoped Matrix

theorem rckE6_gcdSearch_false {α : Type} (m : α → ℕ) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ∀ (l : List α) (g : ℕ), gcdSearch m l g = true → p ∣ g → (∀ x ∈ l, p ∣ m x) → False
  | [], g, h, hg, _ => by
    simp only [gcdSearch, decide_eq_true_eq] at h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hg.trans h))
  | x :: l, g, h, hg, hl => by
    have hg' : p ∣ Nat.gcd g (m x) := Nat.dvd_gcd hg (hl x List.mem_cons_self)
    simp only [gcdSearch, Bool.or_eq_true, decide_eq_true_eq] at h
    rcases h with h | h
    · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hg'.trans h))
    · exact rckE6_gcdSearch_false m hp hp2 l _ h hg'
        (fun y hy => hl y (List.mem_cons_of_mem x hy))

theorem rckE6_natCard_ker {K : Type*} [Field K] [Fintype K] {n : ℕ} (N : Matrix (Fin n) (Fin n) K) :
    Nat.card {z : Fin n → K // N *ᵥ z = 0} = Nat.card K ^ (n - N.rank) := by
  have e : {z : Fin n → K // N *ᵥ z = 0} ≃ ↥(LinearMap.ker N.mulVecLin) :=
    Equiv.subtypeEquivRight fun z => by simp [LinearMap.mem_ker, Matrix.mulVecLin_apply]
  rw [Nat.card_congr e, Module.natCard_eq_pow_finrank (K := K)]
  have h := LinearMap.finrank_range_add_finrank_ker N.mulVecLin
  rw [Module.finrank_fin_fun] at h
  have hr : N.rank = Module.finrank K (LinearMap.range N.mulVecLin) := rfl
  congr 1
  omega

theorem rckE6_natCard_eigen {K : Type*} [Field K] [Fintype K] {n : ℕ} (A : Matrix (Fin n) (Fin n) K)
    (c : K) :
    Nat.card {z : Fin n → K // Aᵀ *ᵥ z = c • z} = Nat.card K ^ (n - (A - c • 1).rank) := by
  have e : {z : Fin n → K // Aᵀ *ᵥ z = c • z} ≃ {z : Fin n → K // (A - c • 1)ᵀ *ᵥ z = 0} :=
    Equiv.subtypeEquivRight fun z => by
      rw [Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_one, Matrix.sub_mulVec,
        Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero]
  rw [Nat.card_congr e, rckE6_natCard_ker, Matrix.rank_transpose]

theorem rckE6_minor3_dvd_of_rank_le {p : ℕ} (hp : p.Prime) (N : Matrix (Fin Tag.E6.rank) (Fin Tag.E6.rank) ℤ)
    (hrank : (N.map (Int.castRingHom (ZMod p))).rank ≤ 2) (a b c x y z : Fin Tag.E6.rank) :
    (p : ℤ) ∣ det3 N a b c x y z := by
  haveI : Fact p.Prime := ⟨hp⟩
  set Nb := N.map (Int.castRingHom (ZMod p)) with hNb
  have hsub : (Nb.submatrix ![a, b, c] ![x, y, z]).rank ≤ 2 :=
    (Matrix.rank_submatrix_le Nb ![a, b, c] ![x, y, z]).trans hrank
  have hdet : (Nb.submatrix ![a, b, c] ![x, y, z]).det = 0 := by
    by_contra hne
    have hu : IsUnit (Nb.submatrix ![a, b, c] ![x, y, z]) :=
      (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hne)
    have h3 : (Nb.submatrix ![a, b, c] ![x, y, z]).rank = 3 := by
      simpa using Matrix.rank_of_isUnit _ hu
    omega
  rw [Matrix.det_fin_three] at hdet
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  simp only [det3]
  push_cast
  simp [hNb, Matrix.submatrix_apply, Matrix.map_apply, Matrix.vecHead, Matrix.vecTail] at hdet
  linear_combination hdet

theorem rckE6_rank_ge_three {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (N : Matrix (Fin Tag.E6.rank) (Fin Tag.E6.rank) ℤ) (hN : gcdSearch3 N = true) :
    3 ≤ (N.map (Int.castRingHom (ZMod p))).rank := by
  by_contra h
  have hrank : (N.map (Int.castRingHom (ZMod p))).rank ≤ 2 := by omega
  exact rckE6_gcdSearch_false _ hp hp2 minorIdx3 0 hN (dvd_zero p) fun x _ =>
    Int.natCast_dvd.1 (rckE6_minor3_dvd_of_rank_le hp N hrank _ _ _ _ _ _)

theorem rckE6_minor2_dvd_of_rank_le {p : ℕ} (hp : p.Prime) (N : Matrix (Fin Tag.E6.rank) (Fin Tag.E6.rank) ℤ)
    (hrank : (N.map (Int.castRingHom (ZMod p))).rank ≤ 1) (a b x y : Fin Tag.E6.rank) :
    (p : ℤ) ∣ det2 N a b x y := by
  haveI : Fact p.Prime := ⟨hp⟩
  set Nb := N.map (Int.castRingHom (ZMod p)) with hNb
  have hsub : (Nb.submatrix ![a, b] ![x, y]).rank ≤ 1 :=
    (Matrix.rank_submatrix_le Nb ![a, b] ![x, y]).trans hrank
  have hdet : (Nb.submatrix ![a, b] ![x, y]).det = 0 := by
    by_contra hne
    have hu : IsUnit (Nb.submatrix ![a, b] ![x, y]) :=
      (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hne)
    have h2 : (Nb.submatrix ![a, b] ![x, y]).rank = 2 := by
      simpa using Matrix.rank_of_isUnit _ hu
    omega
  rw [Matrix.det_fin_two] at hdet
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  simp only [det2]
  push_cast
  simp [hNb, Matrix.submatrix_apply, Matrix.map_apply, Matrix.vecHead, Matrix.vecTail] at hdet
  linear_combination hdet

theorem rckE6_rank_ge_two {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (N : Matrix (Fin Tag.E6.rank) (Fin Tag.E6.rank) ℤ) (hN : gcdSearch2 N = true) :
    2 ≤ (N.map (Int.castRingHom (ZMod p))).rank := by
  by_contra h
  have hrank : (N.map (Int.castRingHom (ZMod p))).rank ≤ 1 := by omega
  exact rckE6_gcdSearch_false _ hp hp2 minorIdx2 0 hN (dvd_zero p) fun x _ =>
    Int.natCast_dvd.1 (rckE6_minor2_dvd_of_rank_le hp N hrank _ _ _ _)

theorem rckE6_gcdSearch_of_mem {α : Type} (m : α → ℕ) :
    ∀ (l : List α) (g : ℕ) {x : α}, x ∈ l → m x ∣ 2 → gcdSearch m l g = true
  | [], _, _, hx, _ => by simp at hx
  | y :: l, g, x, hx, h2 => by
    simp only [gcdSearch, Bool.or_eq_true, decide_eq_true_eq]
    rcases List.mem_cons.1 hx with rfl | hx
    · exact Or.inl ((Nat.gcd_dvd_right _ _).trans h2)
    · exact Or.inr (rckE6_gcdSearch_of_mem m l _ hx h2)

theorem rckE6_mem_triples6 :
    ∀ a b c : Fin Tag.E6.rank, a < b → b < c → (a, b, c) ∈ triples6 := by
  decide

theorem rckE6_mem_pairs6 : ∀ a b : Fin Tag.E6.rank, a < b → (a, b) ∈ pairs6 := by
  decide

theorem rckE6_natAbs_dvd_two {d : ℤ} (hd : d ∈ ({1, -1, 2, -2} : Finset ℤ)) : d.natAbs ∣ 2 := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hd
  rcases hd with rfl | rfl | rfl | rfl <;> decide

theorem rckE6_gcdSearch3_of_smallMinor {A : Matrix (Fin Tag.E6.rank) (Fin Tag.E6.rank) ℤ}
    (h : SmallMinor 3 A) : gcdSearch3 A = true := by
  obtain ⟨R, C, hR, hC, hd⟩ := h
  refine rckE6_gcdSearch_of_mem _ minorIdx3 0 (x := ((R 0, R 1, R 2), (C 0, C 1, C 2))) ?_ ?_
  · simp only [minorIdx3, List.mem_flatMap, List.mem_map]
    exact ⟨_, rckE6_mem_triples6 _ _ _ (hR (by decide)) (hR (by decide)), _,
      rckE6_mem_triples6 _ _ _ (hC (by decide)) (hC (by decide)), rfl⟩
  · have he : det3 A (R 0) (R 1) (R 2) (C 0) (C 1) (C 2) = (A.submatrix R C).det := by
      rw [Matrix.det_fin_three]
      simp only [Matrix.submatrix_apply, det3]
      ring
    change (det3 A (R 0) (R 1) (R 2) (C 0) (C 1) (C 2)).natAbs ∣ 2
    rw [he]
    exact rckE6_natAbs_dvd_two hd

theorem rckE6_gcdSearch2_of_smallMinor {A : Matrix (Fin Tag.E6.rank) (Fin Tag.E6.rank) ℤ}
    (h : SmallMinor 2 A) : gcdSearch2 A = true := by
  obtain ⟨R, C, hR, hC, hd⟩ := h
  refine rckE6_gcdSearch_of_mem _ minorIdx2 0 (x := ((R 0, R 1), (C 0, C 1))) ?_ ?_
  · simp only [minorIdx2, List.mem_flatMap, List.mem_map]
    exact ⟨_, rckE6_mem_pairs6 _ _ (hR (by decide)), _, rckE6_mem_pairs6 _ _ (hC (by decide)), rfl⟩
  · have he : det2 A (R 0) (R 1) (C 0) (C 1) = (A.submatrix R C).det := by
      rw [Matrix.det_fin_two]
      simp only [Matrix.submatrix_apply, det2]
    change (det2 A (R 0) (R 1) (C 0) (C 1)).natAbs ∣ 2
    rw [he]
    exact rckE6_natAbs_dvd_two hd

theorem rckE6_weyl_matrixCheck
    (w : WeylGroup Tag.E6) :
    matrixCheck (weylMatrix w) 1 = true ∧ matrixCheck (weylMatrix w * rhoMatrix) (-1) = true := by
  obtain ⟨h1, h2⟩ := Certificates.certificate715001 w
  have hone : ((1 : ℤ) • 1 : Matrix (Fin Tag.E6.rank) (Fin Tag.E6.rank) ℤ) = 1 := one_smul ℤ 1
  have hneg : ((-1 : ℤ) • 1 : Matrix (Fin Tag.E6.rank) (Fin Tag.E6.rank) ℤ) = -1 := neg_one_smul ℤ 1
  simp only [matrixCheck, hone, hneg, sub_neg_eq_add, ← sub_eq_add_neg, Bool.or_eq_true,
    Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨h1.imp id fun h => ⟨rckE6_gcdSearch3_of_smallMinor h.1, rckE6_gcdSearch2_of_smallMinor h.2⟩,
    h2.imp id fun h => ⟨rckE6_gcdSearch3_of_smallMinor h.1, rckE6_gcdSearch2_of_smallMinor h.2⟩⟩

theorem rckE6_map_add_smul_one {p : ℕ} (N : Matrix (Fin Tag.E6.rank) (Fin Tag.E6.rank) ℤ) (a : ℤ)
    {c : ZMod p} (hc : c = -(a : ZMod p)) :
    (N + a • 1).map (Int.castRingHom (ZMod p)) = modMat p N - c • 1 := by
  subst hc
  ext i j
  by_cases hij : i = j <;> simp [modMat, Matrix.one_apply, Matrix.intCast_apply, hij] <;> ring

theorem rckE6_card_eigen_lt_four {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (N : Matrix (Fin Tag.E6.rank) (Fin Tag.E6.rank) ℤ) (a : ℤ) (hN : gcdSearch3 (N + a • 1) = true)
    {c : ZMod p} (hc : c = -(a : ZMod p)) :
    Nat.card {z : Fin Tag.E6.rank → ZMod p // (modMat p N)ᵀ *ᵥ z = c • z} < p ^ 4 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hrk := rckE6_rank_ge_three hp hp2 (N + a • 1) hN
  rw [rckE6_map_add_smul_one N a hc] at hrk
  rw [rckE6_natCard_eigen, Nat.card_zmod]
  have h6 : Tag.E6.rank = 6 := rfl
  have hle : p ^ (Tag.E6.rank - (modMat p N - c • 1).rank) ≤ p ^ 3 :=
    Nat.pow_le_pow_right hp.pos (by omega)
  have h43 : p ^ 3 < p ^ 4 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
  omega

theorem rckE6_map_sub_smul_one {p : ℕ} (N : Matrix (Fin Tag.E6.rank) (Fin Tag.E6.rank) ℤ) (a : ℤ)
    {c : ZMod p} (hc : c = (a : ZMod p)) :
    (N - a • 1).map (Int.castRingHom (ZMod p)) = modMat p N - c • 1 := by
  subst hc
  ext i j
  by_cases hij : i = j <;> simp [modMat, Matrix.one_apply, Matrix.intCast_apply, hij] <;> ring

theorem rckE6_card_eigen_lt_five {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (N : Matrix (Fin Tag.E6.rank) (Fin Tag.E6.rank) ℤ) (a : ℤ) (hN : gcdSearch2 (N - a • 1) = true)
    {c : ZMod p} (hc : c = (a : ZMod p)) :
    Nat.card {z : Fin Tag.E6.rank → ZMod p // (modMat p N)ᵀ *ᵥ z = c • z} < p ^ 5 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hrk := rckE6_rank_ge_two hp hp2 (N - a • 1) hN
  rw [rckE6_map_sub_smul_one N a hc] at hrk
  rw [rckE6_natCard_eigen, Nat.card_zmod]
  have h6 : Tag.E6.rank = 6 := rfl
  have hle : p ^ (Tag.E6.rank - (modMat p N - c • 1).rank) ≤ p ^ 4 :=
    Nat.pow_le_pow_right hp.pos (by omega)
  have h54 : p ^ 4 < p ^ 5 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
  omega

theorem rckE6_matrix_sq_of_eigen_neg {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (N : Matrix (Fin Tag.E6.rank) (Fin Tag.E6.rank) ℤ) (a : ℤ) (hN : matrixCheck N a = true)
    {c : ZMod p} (hc : c = -(a : ZMod p))
    (h : p ^ 4 ≤ Nat.card {z : Fin Tag.E6.rank → ZMod p // (modMat p N)ᵀ *ᵥ z = c • z}) :
    N * N = 1 := by
  by_contra hNN
  simp only [matrixCheck, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true] at hN
  rcases hN with h1 | ⟨h3, -⟩
  · exact hNN h1
  · exact absurd h (not_le.2 (rckE6_card_eigen_lt_four hp hp2 N a h3 hc))

theorem rckE6_matrix_sq_of_eigen_pos {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (N : Matrix (Fin Tag.E6.rank) (Fin Tag.E6.rank) ℤ) (a : ℤ) (hN : matrixCheck N a = true)
    {c : ZMod p} (hc : c = (a : ZMod p))
    (h : p ^ 5 ≤ Nat.card {z : Fin Tag.E6.rank → ZMod p // (modMat p N)ᵀ *ᵥ z = c • z}) :
    N * N = 1 := by
  by_contra hNN
  simp only [matrixCheck, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true] at hN
  rcases hN with h1 | ⟨-, h2⟩
  · exact hNN h1
  · exact absurd h (not_le.2 (rckE6_card_eigen_lt_five hp hp2 N a h2 hc))

theorem rckE6_mulVec_dotProduct {R : Type*} [CommSemiring R] {n : Type*} [Fintype n]
    (M : Matrix n n R) (x v : n → R) : (M *ᵥ x) ⬝ᵥ v = x ⬝ᵥ (Mᵀ *ᵥ v) := by
  rw [Matrix.dotProduct_mulVec x Mᵀ, Matrix.vecMul_transpose]

theorem rckE6_isotropic_finrank_le {K : Type*} [Field K] (B : Matrix (Fin 6) (Fin 6) K)
    (hB : B.det ≠ 0) (W : Submodule K (Fin 6 → K))
    (hW : ∀ x ∈ W, ∀ y ∈ W, x ⬝ᵥ (B *ᵥ y) = 0) : Module.finrank K W ≤ 3 := by
  have hnd : (Matrix.toBilin' B).Nondegenerate :=
    LinearMap.BilinForm.nondegenerate_toBilin'_of_det_ne_zero' B hB
  have hle : W ≤ (Matrix.toBilin' B).orthogonal W := by
    intro y hy x hx
    rw [Matrix.toBilin'_apply']
    exact hW x hx y hy
  have h1 := LinearMap.BilinForm.finrank_orthogonal hnd W
  have h2 := Submodule.finrank_mono hle
  rw [Module.finrank_fin_fun] at h1
  omega

theorem rckE6_rank_ge_three_of_isometry {K : Type*} [Field K] (B M : Matrix (Fin 6) (Fin 6) K)
    (hB : B.det ≠ 0) (hMB : Mᵀ * B * M = B) {c : K} (hc : c ^ 2 ≠ 1) :
    3 ≤ (M - c • 1).rank := by
  obtain ⟨W, hWdef⟩ : ∃ W : Submodule K (Fin 6 → K), W = LinearMap.ker (M - c • 1).mulVecLin :=
    ⟨_, rfl⟩
  have hmem : ∀ x ∈ W, M *ᵥ x = c • x := fun x hx => by
    rw [hWdef] at hx
    have := LinearMap.mem_ker.1 hx
    simpa [Matrix.mulVecLin_apply, Matrix.sub_mulVec, sub_eq_zero] using this
  have hW : ∀ x ∈ W, ∀ y ∈ W, x ⬝ᵥ (B *ᵥ y) = 0 := by
    intro x hx y hy
    have key : (M *ᵥ x) ⬝ᵥ (B *ᵥ (M *ᵥ y)) = x ⬝ᵥ (B *ᵥ y) := by
      rw [rckE6_mulVec_dotProduct, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hMB]
    rw [hmem x hx, hmem y hy, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul] at key
    have h2 : (c ^ 2 - 1) * (x ⬝ᵥ (B *ᵥ y)) = 0 := by
      simp only [smul_eq_mul] at key
      linear_combination key
    rcases mul_eq_zero.1 h2 with h | h
    · exact absurd (sub_eq_zero.1 h) hc
    · exact h
  have hfr := rckE6_isotropic_finrank_le B hB W hW
  have h := LinearMap.finrank_range_add_finrank_ker (M - c • 1).mulVecLin
  rw [Module.finrank_fin_fun, ← hWdef] at h
  have hr : (M - c • 1).rank = Module.finrank K (LinearMap.range (M - c • 1).mulVecLin) := rfl
  omega

theorem rckE6_weylMatrix_pres_form
    (w : WeylGroup Tag.E6) :
    (weylMatrix w)ᵀ * Tag.E6.symmetrizedCartan * weylMatrix w = Tag.E6.symmetrizedCartan := by
  ext i j
  have key : ∀ X : Matrix (Fin Tag.E6.rank) (Fin Tag.E6.rank) ℤ,
      (Pi.single i 1 : Fin Tag.E6.rank → ℤ) ⬝ᵥ (X *ᵥ Pi.single j 1) = X i j := fun X => by
    rw [single_dotProduct, one_mul, Matrix.mulVec_single_one]
    rfl
  have h := rootForm_smul w (Pi.single i 1) (Pi.single j 1)
  rw [← weylMatrix_mulVec, ← weylMatrix_mulVec, key Tag.E6.symmetrizedCartan,
    rckE6_mulVec_dotProduct, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    key ((weylMatrix w)ᵀ * Tag.E6.symmetrizedCartan * weylMatrix w)] at h
  exact h

theorem rckE6_card_eigen_lt_of_isometry {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (N : Matrix (Fin Tag.E6.rank) (Fin Tag.E6.rank) ℤ)
    (hNB : Nᵀ * Tag.E6.symmetrizedCartan * N = Tag.E6.symmetrizedCartan)
    {c : ZMod p} (hc1 : c ≠ 1) (hc2 : c ≠ -1) :
    Nat.card {z : Fin Tag.E6.rank → ZMod p // (modMat p N)ᵀ *ᵥ z = c • z} < p ^ 4 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h3 : (3 : ZMod p) ≠ 0 := by
    intro h
    have h' : ((3 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h'
    exact absurd (Nat.le_of_dvd (by norm_num) h') (by omega)
  have hsc : Tag.E6.symmetrizedCartan = Tag.E6.cartan := by
    rw [Tag.symmetrizedCartan, Tag.symmetrizer, one_mul]
  have hB : (Tag.E6.symmetrizedCartan.map (Int.castRingHom (ZMod p))).det ≠ 0 := by
    have h := RingHom.map_det (Int.castRingHom (ZMod p)) Tag.E6.symmetrizedCartan
    rw [hsc, CFSG.LieType.Chevalley.det_cartan_E6] at h
    rw [← hsc] at h
    have h' : (Tag.E6.symmetrizedCartan.map (Int.castRingHom (ZMod p))).det = 3 := by
      rw [← RingHom.mapMatrix_apply, ← h]
      simp
    rw [h']
    exact h3
  have hMB : (modMat p N)ᵀ * Tag.E6.symmetrizedCartan.map (Int.castRingHom (ZMod p)) *
      modMat p N = Tag.E6.symmetrizedCartan.map (Int.castRingHom (ZMod p)) := by
    have h := congrArg (RingHom.mapMatrix (Int.castRingHom (ZMod p))) hNB
    simp only [map_mul, RingHom.mapMatrix_apply] at h
    rw [Matrix.transpose_map] at h
    exact h
  have hc : c ^ 2 ≠ 1 := fun h => by
    have h2 : (c - 1) * (c + 1) = 0 := by linear_combination h
    rcases mul_eq_zero.1 h2 with h4 | h4
    · exact hc1 (sub_eq_zero.1 h4)
    · exact hc2 (eq_neg_of_add_eq_zero_left h4)
  have hrk : 3 ≤ (modMat p N - c • 1).rank :=
    rckE6_rank_ge_three_of_isometry _ _ hB hMB hc
  rw [rckE6_natCard_eigen, Nat.card_zmod]
  have h6 : Tag.E6.rank = 6 := rfl
  have hle : p ^ (Tag.E6.rank - (modMat p N - c • 1).rank) ≤ p ^ 3 :=
    Nat.pow_le_pow_right hp.pos (by omega)
  have h43 : p ^ 3 < p ^ 4 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
  omega

theorem rckE6_matrix_sq_core {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (N : Matrix (Fin Tag.E6.rank) (Fin Tag.E6.rank) ℤ) (a : ℤ) (ha : a = 1 ∨ a = -1)
    (hN : matrixCheck N a = true)
    (hNB : Nᵀ * Tag.E6.symmetrizedCartan * N = Tag.E6.symmetrizedCartan)
    {c : ZMod p} (hc0 : c ≠ 0)
    (h4 : p ^ 4 ≤ Nat.card {z : Fin Tag.E6.rank → ZMod p // (modMat p N)ᵀ *ᵥ z = c • z})
    (h5 : c = (a : ZMod p) →
      p ^ 5 ≤ Nat.card {z : Fin Tag.E6.rank → ZMod p // (modMat p N)ᵀ *ᵥ z = c • z}) :
    N * N = 1 := by
  by_cases hneg : c = -(a : ZMod p)
  · exact rckE6_matrix_sq_of_eigen_neg hp hp2 N a hN hneg h4
  by_cases hpos : c = (a : ZMod p)
  · exact rckE6_matrix_sq_of_eigen_pos hp hp2 N a hN hpos (h5 hpos)
  exfalso
  have hc1 : c ≠ 1 := by
    rcases ha with rfl | rfl
    · simpa using hpos
    · intro h
      apply hneg
      simp [h]
  have hc2 : c ≠ -1 := by
    rcases ha with rfl | rfl
    · intro h
      apply hneg
      simp [h]
    · simpa using hpos
  have hp5 : 5 ≤ p := by
    by_contra hlt
    have hp3 : p = 3 := by
      have := hp.two_le
      interval_cases p
      · exact absurd rfl hp2
      · rfl
      · exact absurd hp (by norm_num)
    subst hp3
    have hall : ∀ c : ZMod 3, c ≠ 0 → c = 1 ∨ c = -1 := by decide
    rcases hall c hc0 with h | h
    · exact hc1 h
    · exact hc2 h
  haveI : Fact p.Prime := ⟨hp⟩
  exact absurd h4 (not_le.2 (rckE6_card_eigen_lt_of_isometry hp hp5 N hNB hc1 hc2))

theorem rckE6_rhoMatrix_pres_form :
    rhoMatrixᵀ * Tag.E6.symmetrizedCartan * rhoMatrix = Tag.E6.symmetrizedCartan := by
  decide +kernel

theorem rckE6_twistMatrix_pres_form
    (w : WeylGroup Tag.E6) :
    (weylMatrix w * rhoMatrix)ᵀ * Tag.E6.symmetrizedCartan * (weylMatrix w * rhoMatrix) =
      Tag.E6.symmetrizedCartan := by
  calc (weylMatrix w * rhoMatrix)ᵀ * Tag.E6.symmetrizedCartan * (weylMatrix w * rhoMatrix)
      = rhoMatrixᵀ * ((weylMatrix w)ᵀ * Tag.E6.symmetrizedCartan * weylMatrix w) * rhoMatrix := by
        simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    _ = rhoMatrixᵀ * Tag.E6.symmetrizedCartan * rhoMatrix := by
        rw [rckE6_weylMatrix_pres_form w]
    _ = Tag.E6.symmetrizedCartan := rckE6_rhoMatrix_pres_form

theorem rckE6_rho_sq_core {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (N : Matrix (Fin Tag.E6.rank) (Fin Tag.E6.rank) ℤ) (a : ℤ) (ha : a = 1 ∨ a = -1)
    (hN : matrixCheck N a = true)
    (hNB : Nᵀ * Tag.E6.symmetrizedCartan * N = Tag.E6.symmetrizedCartan)
    {ρ : Equiv.Perm (Fin Tag.E6.rank → ℤ)} (hρN : ∀ γ, IsRoot Tag.E6 γ → ρ γ = N *ᵥ γ)
    (hρroot : ∀ γ, IsRoot Tag.E6 γ → IsRoot Tag.E6 (ρ γ)) {m : ℕ} (hm4 : p ^ 4 ≤ m)
    (hm : m ≤ Nat.card {z : Fin Tag.E6.rank → ZMod p //
      (modMat p N)ᵀ *ᵥ z = ((2 ^ f : ℕ) : ZMod p) • z})
    (hm5 : ((2 ^ f : ℕ) : ZMod p) = (a : ZMod p) → p ^ 5 ≤ m) :
    ∀ γ, IsRoot Tag.E6 γ → ρ (ρ γ) = γ := by
  have hc0 : ((2 ^ f : ℕ) : ZMod p) ≠ 0 := by
    intro h
    rw [ZMod.natCast_eq_zero_iff] at h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h))
  have hNN : N * N = 1 := rckE6_matrix_sq_core hp hp2 N a ha hN hNB hc0 (hm4.trans hm)
    (fun hc => (hm5 hc).trans hm)
  intro γ hγ
  rw [hρN (ρ γ) (hρroot γ hγ), hρN γ hγ, Matrix.mulVec_mulVec, hNN, Matrix.one_mulVec]

end CFSG.StandardType.RCKRP

end
