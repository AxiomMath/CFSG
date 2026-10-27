module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328.Matrix

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328

open CFSG.Open
open scoped Matrix commutatorElement

private theorem k328r2c_scalars {F : Type} [Field F] [Fintype F] (hF : Fintype.card F = 4)
    {ω : F} (hω : ω ^ 2 + ω + 1 = 0) :
    (1 : F) + 1 = 0 ∧ ω ^ 3 = 1 ∧ orderOf ω = 3 ∧ ω ≠ ω ^ 2 ∧ ω * ω ≠ 1 ∧ ω ^ 2 * ω ^ 2 ≠ 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := 2) (by rw [hF]; norm_num)
  have h2 : (1 : F) + 1 = 0 := CharTwo.add_self_eq_zero 1
  have h3 : ω ^ 3 = 1 := by linear_combination (ω - 1) * hω
  have h1 : ω ≠ 1 := fun h => by
    rw [h] at hω
    exact one_ne_zero (by linear_combination hω - h2 : (1 : F) = 0)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine ⟨h2, h3, orderOf_eq_prime h3 h1, fun h => ?_, fun h => h1 ?_, fun h => h1 ?_⟩
  · have h2' : ω + ω = 0 := CharTwo.add_self_eq_zero ω
    exact one_ne_zero (by linear_combination hω + h - h2' : (1 : F) = 0)
  · linear_combination h3 - ω * h
  · linear_combination h - ω * h3

private theorem k328r2c_eig {F : Type} [Field F] {ι : Type} [Fintype ι] [DecidableEq ι]
    {Z P : Matrix ι ι F} {l : F} (h3 : Z * (Z * Z) = 1) (hl : l ^ 3 = 1)
    (hP : P = l • (Z * Z) + l ^ 2 • Z + 1) : Z * P = l • P := by
  rw [hP, mul_add, mul_add, mul_smul_comm, mul_smul_comm, mul_one, h3]
  match_scalars
  · rfl
  · ring
  · linear_combination (-1 : F) * hl

private theorem k328r2c_range {F : Type} [Field F] {ι : Type} [Fintype ι] [DecidableEq ι]
    {Z P : Matrix ι ι F} {l : F} (h : Z * P = l • P) :
    ∀ v ∈ LinearMap.range P.mulVecLin, Z *ᵥ v = l • v := by
  rintro v ⟨w, rfl⟩
  rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, h, Matrix.smul_mulVec]

private theorem k328r2c_adj_left {F : Type} [Field F] {ι : Type} [Fintype ι] [DecidableEq ι]
    {Z J : Matrix ι ι F} (h3 : Z * (Z * Z) = 1) (hJ : Zᵀ * J * Z = J) :
    Zᵀ * J = J * (Z * Z) ∧ (Z * Z)ᵀ * J = J * Z := by
  have h1 : Zᵀ * J = J * (Z * Z) := by
    calc Zᵀ * J = Zᵀ * J * (Z * (Z * Z)) := by rw [h3, mul_one]
      _ = (Zᵀ * J * Z) * (Z * Z) := by simp only [mul_assoc]
      _ = J * (Z * Z) := by rw [hJ]
  refine ⟨h1, ?_⟩
  calc (Z * Z)ᵀ * J = Zᵀ * (Zᵀ * J) := by rw [Matrix.transpose_mul, mul_assoc]
    _ = J * (Z * Z) * (Z * Z) := by rw [h1, ← mul_assoc, h1, ← mul_assoc]
    _ = J * Z := by
        calc J * (Z * Z) * (Z * Z) = J * (Z * (Z * Z)) * Z := by simp only [mul_assoc]
          _ = J * Z := by rw [h3, mul_one]

private theorem k328r2c_adj {F : Type} [Field F] {ι : Type} [Fintype ι] [DecidableEq ι]
    {Z P Q J : Matrix ι ι F} {l : F} (h3 : Z * (Z * Z) = 1) (hJ : Zᵀ * J * Z = J)
    (hP : P = l • (Z * Z) + l ^ 2 • Z + 1) (hQ : Q = l ^ 2 • (Z * Z) + l • Z + 1) :
    Pᵀ * J = J * Q := by
  obtain ⟨h1, h2⟩ := k328r2c_adj_left h3 hJ
  simp only [hP, hQ, Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_one, add_mul,
    smul_mul_assoc, one_mul, mul_add, mul_smul_comm, mul_one, h1, h2]
  abel

private theorem k328r2c_iso {F : Type} [Field F] {ι κ κ' : Type} [Fintype ι] [DecidableEq ι]
    {Z J : Matrix ι ι F} (hJ : Zᵀ * J * Z = J) {A : Matrix ι κ F} {B : Matrix ι κ' F} {l m : F}
    (hA : Z * A = l • A) (hB : Z * B = m • B) (hlm : l * m ≠ 1) : Aᵀ * J * B = 0 := by
  have h : Aᵀ * J * B = (l * m) • (Aᵀ * J * B) := by
    calc Aᵀ * J * B = Aᵀ * (Zᵀ * J * Z) * B := by rw [hJ]
      _ = (Z * A)ᵀ * J * (Z * B) := by simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = (l * m) • (Aᵀ * J * B) := by
        rw [hA, hB, Matrix.transpose_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul,
          smul_smul]
  have h' : (1 - l * m) • (Aᵀ * J * B) = 0 := by rw [sub_smul, one_smul, ← h, sub_self]
  exact (smul_eq_zero.mp h').resolve_left (sub_ne_zero.mpr (Ne.symm hlm))

private theorem k328r2c_dot {F : Type} [Field F] {ι κ : Type} [Fintype ι] [Fintype κ]
    (A : Matrix ι κ F) (d : κ → F) (w : ι → F) : (A *ᵥ d) ⬝ᵥ w = d ⬝ᵥ (Aᵀ *ᵥ w) := by
  rw [dotProduct_comm, Matrix.dotProduct_mulVec, Matrix.mulVec_transpose, dotProduct_comm]

private theorem k328r2c_gram {F : Type} [Field F] {ι : Type} [Fintype ι] [DecidableEq ι] {k : ℕ}
    {J : Matrix ι ι F} (hJ : Jᵀ * J = 1) {V U : Matrix ι (Fin k) F}
    (hU : Function.Injective U.mulVec) (hspan : ∀ x : ι → F, ∃ d e, x = V *ᵥ d + U *ᵥ e)
    (hUU : Uᵀ * J * U = 0) : ∃ G : Matrix (Fin k) (Fin k) F, Vᵀ * J * (U * G) = 1 := by
  have hdet : (Vᵀ * J * U).det ≠ 0 := by
    intro h0
    obtain ⟨c, hc0, hc⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    apply hc0
    have hx : ∀ x : ι → F, x ⬝ᵥ (J *ᵥ (U *ᵥ c)) = 0 := by
      intro x
      obtain ⟨d, e, rfl⟩ := hspan x
      simp only [add_dotProduct, k328r2c_dot, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hc, hUU,
        Matrix.zero_mulVec, dotProduct_zero, add_zero]
    have hJy : J *ᵥ (U *ᵥ c) = 0 := by
      ext a
      simpa using hx (Pi.single a 1)
    have hy : U *ᵥ c = 0 := by
      have := congrArg Jᵀ.mulVec hJy
      rwa [Matrix.mulVec_mulVec, hJ, Matrix.one_mulVec, Matrix.mulVec_zero] at this
    exact hU (hy.trans (Matrix.mulVec_zero U).symm)
  exact ⟨(Vᵀ * J * U)⁻¹, by
    rw [← Matrix.mul_assoc]; exact Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet)⟩

private theorem k328r2c_frame {F : Type} [Field F] {ι : Type} [Fintype ι] [DecidableEq ι] {k : ℕ}
    (N : Submodule F (ι → F)) (hN : Module.finrank F N = k) {Z : Matrix ι ι F} {l : F}
    (hZ : ∀ v ∈ N, Z *ᵥ v = l • v) :
    ∃ A : Matrix ι (Fin k) F, Function.Injective A.mulVec ∧
      (∀ v, v ∈ N ↔ ∃ d, A *ᵥ d = v) ∧ Z * A = l • A := by
  let e : N ≃ₗ[F] (Fin k → F) := LinearEquiv.ofFinrankEq N (Fin k → F) (by simp [hN])
  let T : (Fin k → F) →ₗ[F] (ι → F) := N.subtype ∘ₗ e.symm.toLinearMap
  have hT : ∀ d, LinearMap.toMatrix' T *ᵥ d = (e.symm d : ι → F) := fun d => by
    rw [LinearMap.toMatrix'_mulVec]; rfl
  have hmem : ∀ d, LinearMap.toMatrix' T *ᵥ d ∈ N := fun d => by rw [hT]; exact (e.symm d).2
  refine ⟨LinearMap.toMatrix' T, ?_, ?_, ?_⟩
  · intro d d' h
    rw [hT, hT] at h
    exact e.symm.injective (Subtype.ext h)
  · intro v
    refine ⟨fun hv => ⟨e ⟨v, hv⟩, ?_⟩, fun ⟨d, hd⟩ => hd ▸ hmem d⟩
    rw [hT]; simp
  · apply Matrix.toLin'.injective
    refine LinearMap.ext fun d => ?_
    simp only [Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, Matrix.smul_mulVec]
    exact hZ _ (hmem d)

private theorem k328r2c_det {F : Type} [Field F] {ι : Type} [Fintype ι] [DecidableEq ι]
    (X : Subgroup (GL ι F)) (N : Submodule F (ι → F))
    (hN : ∀ x ∈ X, ∀ v ∈ N, (x : Matrix ι ι F) *ᵥ v ∈ N) :
    ∃ δ : X →* F, ∀ (x : X) (c : F),
      (∀ v ∈ N, ((x : GL ι F) : Matrix ι ι F) *ᵥ v = c • v) →
        δ x = c ^ Module.finrank F N := by
  have hr : ∀ x : X, ∃ r : N →ₗ[F] N, ∀ v : N,
      ((r v : N) : ι → F) = ((x : GL ι F) : Matrix ι ι F) *ᵥ (v : ι → F) := fun x =>
    ⟨(Matrix.toLin' ((x : GL ι F) : Matrix ι ι F)).restrict
      (fun v hv => by rw [Matrix.toLin'_apply]; exact hN x x.2 v hv),
      fun v => by simp [Matrix.toLin'_apply]⟩
  choose r hr using hr
  have hr1 : r 1 = LinearMap.id := LinearMap.ext fun v => Subtype.ext (by simp [hr])
  have hrm : ∀ x y, r (x * y) = r x ∘ₗ r y := fun x y =>
    LinearMap.ext fun v => Subtype.ext (by simp [hr, Matrix.mulVec_mulVec])
  refine ⟨{ toFun := fun x => LinearMap.det (r x), map_one' := ?_, map_mul' := ?_ }, ?_⟩
  · simp [hr1]
  · intro x y
    simp [hrm, LinearMap.det_comp]
  · intro x c hx
    have : r x = c • LinearMap.id := LinearMap.ext fun v => Subtype.ext (by
      rw [hr]; exact hx _ v.2)
    simp [this, LinearMap.det_smul]

private theorem k328r2c_perfect {G : Type} [Group G] {X : Subgroup G} (hX : ⁅X, X⁆ = X)
    {F : Type} [Field F] (δ : X →* F) {z : G} (hz : z ∈ X) : δ ⟨z, hz⟩ = 1 := by
  have hle : ⁅X, X⁆ ≤ (δ.toHomUnits.ker).map X.subtype := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    exact ⟨⁅(⟨a, ha⟩ : X), (⟨b, hb⟩ : X)⁆, Abelianization.commutator_subset_ker δ.toHomUnits
      (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)), rfl⟩
  rw [hX] at hle
  obtain ⟨y, hy, hyz⟩ := hle hz
  obtain rfl : y = ⟨z, hz⟩ := Subtype.ext hyz
  simpa using congrArg Units.val (MonoidHom.mem_ker.mp hy)

private theorem k328r2c_one {F : Type} [Field F] {ι : Type} [Fintype ι] [DecidableEq ι]
    {Z P Q : Matrix ι ι F} {ω : F} (h2 : (1 : F) + 1 = 0) (hω : ω ^ 2 + ω + 1 = 0)
    (h3 : Z * (Z * Z) = 1) (hP : P = ω • (Z * Z) + ω ^ 2 • Z + 1)
    (hQ : Q = ω ^ 2 • (Z * Z) + ω • Z + 1) (hP0 : P = 0) (hQ0 : Q = 0) : Z = 1 := by
  have hs : Z * Z + Z = 0 := by
    have : P + Q = Z * Z + Z := by
      rw [hP, hQ]
      match_scalars
      · linear_combination hω - h2
      · linear_combination hω - h2
      · exact h2
    rw [← this, hP0, hQ0, add_zero]
  have hZ2 : Z + Z = 0 := by
    have := congrArg (fun s : F => s • Z) h2
    simpa [add_smul] using this
  have hZZ : Z * Z = Z := by
    calc Z * Z = Z * Z + (Z + Z) := by rw [hZ2, add_zero]
      _ = (Z * Z + Z) + Z := by rw [add_assoc]
      _ = Z := by rw [hs, zero_add]
  rw [hZZ, hZZ] at h3
  exact h3

private theorem k328r2c_dims {F : Type} [Field F] {ι : Type} [Fintype ι] [DecidableEq ι]
    (hcard : Fintype.card ι = 6) {Z J P Q : Matrix ι ι F} {ω : F}
    (h2 : (1 : F) + 1 = 0) (hω : ω ^ 2 + ω + 1 = 0) (hω2 : ω ≠ ω ^ 2)
    (h3 : Z * (Z * Z) = 1) (hZ1 : Z ≠ 1) (hJ : Zᵀ * J * Z = J) (hJJ : Jᵀ * J = 1)
    (hJJ' : J * Jᵀ = 1) (hP : P = ω • (Z * Z) + ω ^ 2 • Z + 1)
    (hQ : Q = ω ^ 2 • (Z * Z) + ω • Z + 1) (eP : Z * P = ω • P) (eQ : Z * Q = ω ^ 2 • Q)
    (hdiv : 3 ∣ P.rank) :
    P.rank = 3 ∧ Q.rank = 3 ∧ LinearMap.range P.mulVecLin ⊔ LinearMap.range Q.mulVecLin = ⊤ := by
  have hQP : Q = Jᵀ * (Pᵀ * J) := by
    rw [k328r2c_adj h3 hJ hP hQ, ← Matrix.mul_assoc, hJJ, Matrix.one_mul]
  have hrank : Q.rank = P.rank := by
    rw [hQP, Matrix.rank_mul_eq_right_of_isUnit_det _ _ (Matrix.isUnit_det_of_right_inverse hJJ),
      Matrix.rank_mul_eq_left_of_isUnit_det _ _ (Matrix.isUnit_det_of_right_inverse hJJ'),
      Matrix.rank_transpose]
  have hN := k328r2c_range eP
  have hN' := k328r2c_range eQ
  have hdis : Disjoint (LinearMap.range P.mulVecLin) (LinearMap.range Q.mulVecLin) := by
    rw [Submodule.disjoint_def]
    intro v hv hv'
    have h := (hN v hv).symm.trans (hN' v hv')
    exact (smul_eq_zero.mp (by rw [sub_smul, h, sub_self] : (ω - ω ^ 2) • v = 0)).resolve_left
      (sub_ne_zero.mpr hω2)
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.range P.mulVecLin)
    (LinearMap.range Q.mulVecLin)
  rw [disjoint_iff.mp hdis, finrank_bot, add_zero] at hsum
  have hle := Submodule.finrank_le (LinearMap.range P.mulVecLin ⊔ LinearMap.range Q.mulVecLin)
  rw [Module.finrank_fintype_fun_eq_card, hcard] at hle
  have hPQ : P.rank + Q.rank ≤ 6 := hsum ▸ hle
  have hne : P.rank ≠ 0 := by
    intro h0
    have hQ0 : Q.rank = 0 := hrank.trans h0
    have hz : ∀ R : Matrix ι ι F, R.rank = 0 → R = 0 := fun R hR => by
      have := LinearMap.range_eq_bot.mp (Submodule.finrank_eq_zero.mp hR)
      exact Matrix.toLin'.injective (by rw [Matrix.toLin'_apply', this, map_zero])
    exact hZ1 (k328r2c_one h2 hω h3 hP hQ (hz P h0) (hz Q hQ0))
  have h33 : P.rank = 3 := by
    obtain ⟨m, hm⟩ := hdiv
    omega
  refine ⟨h33, hrank.trans h33, Submodule.eq_top_of_finrank_eq ?_⟩
  rw [hsum, Module.finrank_fintype_fun_eq_card, hcard]
  exact (by omega : P.rank + Q.rank = 6)

private theorem k328r2c_JT {F : Type} [Field F] {J : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F}
    (hJ : J = Matrix.fromBlocks 0 1 (-1) 0) : Jᵀ = -J ∧ Jᵀ * J = 1 ∧ J * Jᵀ = 1 := by
  subst hJ
  refine ⟨?_, ?_, ?_⟩
  · simp [Matrix.fromBlocks_transpose, Matrix.fromBlocks_neg]
  · simp [Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply]
  · simp [Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply]

private theorem k328r2c_symp {F : Type} [Field F] {J : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F}
    (hJ : J = Matrix.fromBlocks 0 1 (-1) 0) {V W : Matrix (Fin 3 ⊕ Fin 3) (Fin 3) F}
    (hVV : Vᵀ * J * V = 0) (hWW : Wᵀ * J * W = 0) (hVW : Vᵀ * J * W = 1) :
    (Matrix.fromCols V W)ᵀ * J * Matrix.fromCols V W = J := by
  obtain ⟨hT, -, -⟩ := k328r2c_JT hJ
  have hWV : Wᵀ * J * V = -1 := by
    have := congrArg Matrix.transpose hVW
    rw [Matrix.transpose_mul, Matrix.transpose_mul, hT, Matrix.transpose_transpose,
      Matrix.transpose_one, Matrix.neg_mul, Matrix.mul_neg, ← Matrix.mul_assoc] at this
    rw [← neg_eq_iff_eq_neg.mp (by simpa [Matrix.mul_assoc] using this : -(Wᵀ * J * V) = 1)]
  rw [Matrix.transpose_fromCols, Matrix.fromRows_mul, Matrix.fromRows_mul_fromCols, hVV, hWW,
    hVW, hWV, hJ]

private theorem k328r2c_mem {F : Type} [Field F] {J h : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F}
    (hJ : J = Matrix.fromBlocks 0 1 (-1) 0) (hh : hᵀ * J * h = J) :
    ∃ g : GL (Fin 3 ⊕ Fin 3) F, (g : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) = h ∧
      g ∈ StatedSp 3 F := by
  obtain ⟨-, hJJ, -⟩ := k328r2c_JT hJ
  have h1 : (Jᵀ * (hᵀ * J)) * h = 1 := by rw [Matrix.mul_assoc, hh, hJJ]
  have h2 : h * (Jᵀ * (hᵀ * J)) = 1 := mul_eq_one_comm.mp h1
  refine ⟨⟨h, Jᵀ * (hᵀ * J), h2, h1⟩, rfl, ?_⟩
  rw [StatedAPI.mem_statedSp_iff]
  show hᵀ * Matrix.fromBlocks 0 1 (-1) 0 * h = Matrix.fromBlocks 0 1 (-1) 0
  rw [← hJ]
  exact hh

private theorem k328r2c_diag {F : Type} [Field F] {ω : F}
    {Z : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F} {V W : Matrix (Fin 3 ⊕ Fin 3) (Fin 3) F}
    (hV : Z * V = ω • V) (hW : Z * W = ω ^ 2 • W) :
    Z * Matrix.fromCols V W =
      Matrix.fromCols V W * Matrix.diagonal (Sum.elim ![ω, ω, ω] ![ω ^ 2, ω ^ 2, ω ^ 2]) := by
  have e1 : (Matrix.diagonal ![ω, ω, ω] : Matrix (Fin 3) (Fin 3) F) = ω • 1 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp
  have e2 : (Matrix.diagonal ![ω ^ 2, ω ^ 2, ω ^ 2] : Matrix (Fin 3) (Fin 3) F) = ω ^ 2 • 1 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp
  rw [← Matrix.fromBlocks_diagonal, Matrix.mul_fromCols, Matrix.fromCols_mul_fromBlocks, hV, hW,
    e1, e2]
  simp

private theorem k328r2c_build {F : Type} [Field F] {ω : F}
    {Z J : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F} (hJ : J = Matrix.fromBlocks 0 1 (-1) 0)
    (hJZ : Zᵀ * J * Z = J) (hω1 : ω * ω ≠ 1) (hω2 : ω ^ 2 * ω ^ 2 ≠ 1)
    {V U : Matrix (Fin 3 ⊕ Fin 3) (Fin 3) F} (hZV : Z * V = ω • V) (hZU : Z * U = ω ^ 2 • U)
    (hU : Function.Injective U.mulVec) (hspan : ∀ x, ∃ d e, x = V *ᵥ d + U *ᵥ e) :
    ∃ g : GL (Fin 3 ⊕ Fin 3) F, g ∈ StatedSp 3 F ∧
      Z * (g : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) = (g : Matrix (Fin 3 ⊕ Fin 3)
        (Fin 3 ⊕ Fin 3) F) *
          Matrix.diagonal (Sum.elim ![ω, ω, ω] ![ω ^ 2, ω ^ 2, ω ^ 2]) := by
  obtain ⟨-, hJJ, -⟩ := k328r2c_JT hJ
  have hUU : Uᵀ * J * U = 0 := k328r2c_iso hJZ hZU hZU hω2
  have hVV : Vᵀ * J * V = 0 := k328r2c_iso hJZ hZV hZV hω1
  obtain ⟨G, hG⟩ := k328r2c_gram hJJ hU hspan hUU
  have hZW : Z * (U * G) = ω ^ 2 • (U * G) := by
    rw [← Matrix.mul_assoc, hZU, Matrix.smul_mul]
  have hWW : (U * G)ᵀ * J * (U * G) = 0 := by
    calc (U * G)ᵀ * J * (U * G) = Gᵀ * (Uᵀ * J * U) * G := by
          simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = 0 := by rw [hUU, Matrix.mul_zero, Matrix.zero_mul]
  obtain ⟨g, hg, hgH⟩ := k328r2c_mem hJ (k328r2c_symp hJ hVV hWW hG)
  exact ⟨g, hgH, by rw [hg]; exact k328r2c_diag hZV hZW⟩

private theorem k328r2c_comm {F : Type} [Field F] {ι : Type} [Fintype ι] [DecidableEq ι]
    {Z x P : Matrix ι ι F} {l : F} (hx : x * Z = Z * x)
    (hP : P = l • (Z * Z) + l ^ 2 • Z + 1) : x * P = P * x := by
  have hxZZ : x * (Z * Z) = (Z * Z) * x := by
    rw [← Matrix.mul_assoc, hx, Matrix.mul_assoc, hx, ← Matrix.mul_assoc]
  rw [hP, mul_add, mul_add, add_mul, add_mul, mul_smul_comm, mul_smul_comm, smul_mul_assoc,
    smul_mul_assoc, hxZZ, hx, mul_one, one_mul]

private theorem k328r2c_div {F : Type} [Field F] {ι : Type} [Fintype ι] [DecidableEq ι]
    {ω : F} (hωo : orderOf ω = 3) {z : GL ι F} {Z P : Matrix ι ι F}
    (hZ : (z : Matrix ι ι F) = Z) (hP : P = ω • (Z * Z) + ω ^ 2 • Z + 1)
    (eP : Z * P = ω • P) {X : Subgroup (GL ι F)} (hzX : z ∈ X)
    (hXC : X ≤ Subgroup.centralizer {z}) (hXp : ⁅X, X⁆ = X) : 3 ∣ P.rank := by
  have hXN : ∀ x ∈ X, ∀ v ∈ LinearMap.range P.mulVecLin,
      (x : Matrix ι ι F) *ᵥ v ∈ LinearMap.range P.mulVecLin := by
    intro x hx v hv
    have hxz : z * x = x * z := Subgroup.mem_centralizer_iff.mp (hXC hx) z (Set.mem_singleton z)
    have hxZ : (x : Matrix ι ι F) * Z = Z * x := by
      have := congrArg Units.val hxz
      rwa [Units.val_mul, Units.val_mul, hZ, eq_comm] at this
    obtain ⟨w, rfl⟩ := hv
    refine ⟨(x : Matrix ι ι F) *ᵥ w, ?_⟩
    rw [Matrix.mulVecLin_apply, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec, k328r2c_comm hxZ hP]
  obtain ⟨δ, hδ⟩ := k328r2c_det X (LinearMap.range P.mulVecLin) hXN
  have h1 : ω ^ P.rank = 1 :=
    (hδ ⟨z, hzX⟩ ω (fun v hv => by rw [hZ]; exact k328r2c_range eP v hv)).symm.trans
      (k328r2c_perfect hXp δ hzX)
  simpa [hωo] using orderOf_dvd_of_pow_eq_one h1

private theorem k328r2c_conj {F : Type} [Field F] {ω : F}
    {Z J P Q : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F} (h2 : (1 : F) + 1 = 0)
    (hω : ω ^ 2 + ω + 1 = 0) (hω3 : ω ^ 3 = 1) (hωω : ω ≠ ω ^ 2) (hωa : ω * ω ≠ 1)
    (hωb : ω ^ 2 * ω ^ 2 ≠ 1) (hJ : J = Matrix.fromBlocks 0 1 (-1) 0) (h3 : Z * (Z * Z) = 1)
    (hZ1 : Z ≠ 1) (hJZ : Zᵀ * J * Z = J) (hP : P = ω • (Z * Z) + ω ^ 2 • Z + 1)
    (hQ : Q = ω ^ 2 • (Z * Z) + ω • Z + 1) (hdiv : 3 ∣ P.rank) :
    ∃ g : GL (Fin 3 ⊕ Fin 3) F, g ∈ StatedSp 3 F ∧
      Z * (g : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) = (g : Matrix (Fin 3 ⊕ Fin 3)
        (Fin 3 ⊕ Fin 3) F) * Matrix.diagonal (Sum.elim ![ω, ω, ω] ![ω ^ 2, ω ^ 2, ω ^ 2]) := by
  obtain ⟨-, hJJ, hJJ'⟩ := k328r2c_JT hJ
  have hQ' : Q = ω ^ 2 • (Z * Z) + (ω ^ 2) ^ 2 • Z + 1 := by
    rw [hQ, show (ω ^ 2) ^ 2 = ω by linear_combination ω * hω3]
  have eP : Z * P = ω • P := k328r2c_eig h3 hω3 hP
  have eQ : Z * Q = ω ^ 2 • Q :=
    k328r2c_eig h3 (by rw [← pow_mul, mul_comm, pow_mul, hω3, one_pow]) hQ'
  obtain ⟨hr1, hr2, htop⟩ :=
    k328r2c_dims (by simp) h2 hω hωω h3 hZ1 hJZ hJJ hJJ' hP hQ eP eQ hdiv
  obtain ⟨V, -, hVmem, hZV⟩ :=
    k328r2c_frame (LinearMap.range P.mulVecLin) hr1 (k328r2c_range eP)
  obtain ⟨U, hUinj, hUmem, hZU⟩ :=
    k328r2c_frame (LinearMap.range Q.mulVecLin) hr2 (k328r2c_range eQ)
  have hspan : ∀ x, ∃ d e, x = V *ᵥ d + U *ᵥ e := by
    intro x
    have hx : x ∈ LinearMap.range P.mulVecLin ⊔ LinearMap.range Q.mulVecLin := by
      rw [htop]; trivial
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hx
    obtain ⟨d, rfl⟩ := (hVmem a).mp ha
    obtain ⟨e, rfl⟩ := (hUmem b).mp hb
    exact ⟨d, e, rfl⟩
  exact k328r2c_build hJ hJZ hωa hωb hZV hZU hUinj hspan

theorem row2_class (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (hF : Fintype.card F = 4) (ω : F)
    (hω : ω ^ 2 + ω + 1 = 0) (z₀ t₀ : GL (Fin 3 ⊕ Fin 3) F)
    (hz : (z₀ : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) =
      Matrix.diagonal (Sum.elim ![ω, ω, ω] ![ω ^ 2, ω ^ 2, ω ^ 2]))
    (ht : (t₀ : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) =
      Matrix.diagonal (Sum.elim ![ω, ω ^ 2, 1] ![ω ^ 2, ω, 1])) :
    ClassLeaf (StatedSp 3 F) z₀ := by
  have _ := ht
  intro z hzH hord X hXH hzX hXC hXp
  obtain ⟨h2, hω3, hωo, hωω, hωa, hωb⟩ := k328r2c_scalars hF hω
  obtain ⟨J, hJ⟩ : ∃ J : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F,
      J = Matrix.fromBlocks 0 1 (-1) 0 := ⟨_, rfl⟩
  obtain ⟨Z, hZ⟩ : ∃ Z : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F, (z : Matrix _ _ F) = Z :=
    ⟨_, rfl⟩
  have h3 : Z * (Z * Z) = 1 := by
    have hz3 : z ^ 3 = 1 := by
      have := pow_orderOf_eq_one z
      rwa [hord] at this
    have h := congrArg Units.val hz3
    rwa [Units.val_pow_eq_pow_val, pow_three, hZ, Units.val_one] at h
  have hZ1 : Z ≠ 1 := fun h => by
    have : z = 1 := Units.ext (hZ.trans h)
    rw [this, orderOf_one] at hord
    omega
  have hJZ : Zᵀ * J * Z = J := by
    rw [← hZ, hJ]
    exact StatedAPI.mem_statedSp_iff.mp hzH
  obtain ⟨P, hP⟩ : ∃ P : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F,
      P = ω • (Z * Z) + ω ^ 2 • Z + 1 := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F,
      Q = ω ^ 2 • (Z * Z) + ω • Z + 1 := ⟨_, rfl⟩
  obtain ⟨g, hgH, hg⟩ := k328r2c_conj h2 hω hω3 hωω hωa hωb hJ h3 hZ1 hJZ hP hQ
    (k328r2c_div hωo hZ hP (k328r2c_eig h3 hω3 hP) hzX hXC hXp)
  have hzg : z * g = g * z₀ := Units.ext (by rw [Units.val_mul, Units.val_mul, hZ, hz]; exact hg)
  refine ⟨g⁻¹, (StatedSp 3 F).inv_mem hgH, Or.inl ?_⟩
  rw [inv_inv, mul_assoc, hzg, ← mul_assoc, inv_mul_cancel, one_mul]

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328
