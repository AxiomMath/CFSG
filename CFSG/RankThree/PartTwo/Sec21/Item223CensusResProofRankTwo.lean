module

public import CFSG.RankThree.PartTwo.Sec21.Item223CensusProofSymp

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU projImage)
open Matrix

@[expose] def G2OddThreeRankTwo : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], 3 < p → ∀ (X : Type) [Group X],
    Blueprint.ChevalleyExceptionalModel X .G2 p 1 → CFSG.pRank 3 (X ⧸ Subgroup.center X) ≤ 2

@[expose] def ExcEvenThreeRankTwo : Prop :=
  ∀ (X : Type) [Group X] (f : ℕ),
    (Blueprint.ChevalleyExceptionalModel X .G2 2 f ∨
      Blueprint.ChevalleyExceptionalModel X .trialityD4 2 f ∨
      Blueprint.ReeTitsModel X .twistedF4 2 f) →
    CFSG.pRank 3 (X ⧸ Subgroup.center X) ≤ 2

namespace Item223CensusResProof

section Pairing

variable {L : Type*} [Field L] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem card_sq_le_of_pairing (E : Subgroup (GL ι L)) [Finite E] (hexp : ∀ x ∈ E, x ^ 3 = 1)
    {b : Module.Basis ι L (ι → L)} {d : GL ι L → ι → L}
    (hb : ∀ x ∈ E, ∀ a, (x : Matrix ι ι L) *ᵥ b a = d x a • b a)
    (hpair : ∀ a, ∃ a', ∀ x ∈ E, d x a' = (d x a)⁻¹) :
    Nat.card E ^ 2 ≤ 3 ^ Fintype.card ι := by
  classical
  set C : Finset (E → L) := Finset.univ.image fun a => fun x : E => d x a with hCdef
  have hCcard : C.card ≤ Fintype.card ι := Finset.card_image_le
  have h := Sec4.card_sq_le_of_characters (G := E) (K := L) C.card C ⊤ le_rfl
    (by
      intro χ hχ x _ y _
      obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hχ
      exact Sec4.eigen_mul hb x.2 y.2 a)
    (by
      intro χ hχ x _
      obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hχ
      exact Sec4.eigen_pow_three hb x.2 (hexp x x.2) a)
    (by
      intro χ hχ
      obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hχ
      obtain ⟨a', ha'⟩ := hpair a
      exact ⟨fun x : E => d x a', Finset.mem_image.mpr ⟨a', Finset.mem_univ _, rfl⟩,
        fun x _ => ha' x x.2⟩)
    (by
      intro x _ hx
      apply Subtype.ext
      rw [Subgroup.coe_one]
      refine Sec4.eigen_ext hb x.2 E.one_mem fun a => ?_
      rw [Sec4.eigen_one hb a]
      exact hx _ (Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩))
  rw [Subgroup.card_top] at h
  exact h.trans (Nat.pow_le_pow_right (by norm_num) hCcard)

theorem repr_mulVec_of_eigen {E : Subgroup (GL ι L)} {b : Module.Basis ι L (ι → L)}
    {d : GL ι L → ι → L} (hb : ∀ x ∈ E, ∀ a, (x : Matrix ι ι L) *ᵥ b a = d x a • b a)
    {x : GL ι L} (hx : x ∈ E) (v : ι → L) (a' : ι) :
    b.repr ((x : Matrix ι ι L) *ᵥ v) a' = d x a' * b.repr v a' := by
  have h : (b.coord a').comp (Matrix.toLin' (x : Matrix ι ι L)) = d x a' • b.coord a' := by
    refine b.ext fun a => ?_
    rw [LinearMap.comp_apply, Matrix.toLin'_apply, hb x hx a, LinearMap.smul_apply, map_smul]
    simp only [Module.Basis.coord_apply, Module.Basis.repr_self, smul_eq_mul,
      Finsupp.single_apply]
    split_ifs with haa
    · rw [haa]
    · simp
  have := LinearMap.congr_fun h v
  rwa [LinearMap.comp_apply, Matrix.toLin'_apply, LinearMap.smul_apply, Module.Basis.coord_apply,
    Module.Basis.coord_apply, smul_eq_mul] at this

theorem pow_eq_inv_of_mod_two {t : L} (ht : t ^ 3 = 1) {q : ℕ} (hq : q % 3 = 2) :
    t ^ q = t⁻¹ := by
  have ht0 : t ≠ 0 := by
    rintro rfl
    norm_num at ht
  have hq' : q = 3 * (q / 3) + 2 := by omega
  rw [hq', pow_add, pow_mul, ht, one_pow, one_mul]
  exact eq_inv_of_mul_eq_one_left (by rw [← pow_succ, ht])

theorem pow_eq_self_of_mod_one {t : L} (ht : t ^ 3 = 1) {q : ℕ} (hq : q % 3 = 1) :
    t ^ q = t := by
  have hq' : q = 3 * (q / 3) + 1 := by omega
  rw [hq', pow_add, pow_mul, ht, one_pow, one_mul, pow_one]

end Pairing

section Frobenius

variable {L : Type*} [Field L] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem card_sq_le_of_frobenius [IsAlgClosed L] {p : ℕ} [Fact p.Prime] [CharP L p]
    (h3 : (3 : L) ≠ 0) (E : Subgroup (GL ι L)) [Finite E]
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hexp : ∀ x ∈ E, x ^ 3 = 1) (f : ℕ)
    (hq3 : p ^ f % 3 = 2)
    (hfix : ∀ x ∈ E, ∀ i j, iterateFrobenius L p f ((x : Matrix ι ι L) i j) =
      (x : Matrix ι ι L) i j) :
    Nat.card E ^ 2 ≤ 3 ^ Fintype.card ι := by
  classical
  obtain ⟨b, d, hb⟩ := Sec4.exists_common_eigenbasis_pow_three h3 E hcomm hexp
  set φ := iterateFrobenius L p f with hφ
  set F : (ι → L) → (ι → L) := fun v i => φ (v i) with hF
  have hFx : ∀ x ∈ E, ∀ v, (x : Matrix ι ι L) *ᵥ F v = F ((x : Matrix ι ι L) *ᵥ v) := by
    intro x hx v
    funext i
    simp only [hF, Matrix.mulVec, dotProduct, map_sum, map_mul, hfix x hx]
  have hFs : ∀ (t : L) v, F (t • v) = φ t • F v := by
    intro t v
    funext i
    simp [hF]
  have hFinj : Function.Injective F := by
    intro v w h
    funext i
    exact φ.injective (congrFun h i)
  refine card_sq_le_of_pairing E hexp hb fun a => ?_
  set w := F (b a)
  have hw0 : w ≠ 0 := by
    intro h
    apply b.ne_zero a
    apply hFinj
    have hF0 : F 0 = 0 := by
      funext i
      simp [hF]
    rw [hF0]
    exact h
  obtain ⟨a', ha'⟩ : ∃ a', b.repr w a' ≠ 0 := by
    by_contra h
    push Not at h
    apply hw0
    rw [← b.sum_repr w]
    simp [h]
  refine ⟨a', fun x hx => ?_⟩
  have hd3 := Sec4.eigen_pow_three hb hx (hexp x hx) a
  have hxw : (x : Matrix ι ι L) *ᵥ w = (d x a)⁻¹ • w := by
    rw [hFx x hx, hb x hx a, hFs, hφ, iterateFrobenius_def, pow_eq_inv_of_mod_two hd3 hq3]
  have h1 := repr_mulVec_of_eigen hb hx w a'
  rw [hxw, map_smul, Finsupp.smul_apply, smul_eq_mul] at h1
  exact (mul_right_cancel₀ ha' h1).symm

theorem card_sq_le_of_card_mod_two {K : Type*} [Field K] [Fintype K] {p f : ℕ} [Fact p.Prime]
    [CharP K p] (hK : Fintype.card K = p ^ f) (hq3 : p ^ f % 3 = 2) (E : Subgroup (GL ι K))
    [Finite E] (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hexp : ∀ x ∈ E, x ^ 3 = 1) :
    Nat.card E ^ 2 ≤ 3 ^ Fintype.card ι := by
  set L := AlgebraicClosure K
  set Φ := Matrix.GeneralLinearGroup.map (n := ι) (algebraMap K L)
  have hΦ : Function.Injective Φ := Sec4.map_injective_GL _
  have h3K : (3 : K) ≠ 0 := by
    intro h
    have h1 : ((3 : ℕ) : K) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff K p] at h1
    have h2 : 3 ∣ p ^ f := by
      have hp3 : p = 3 := (Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_three).mp h1
      rw [hp3]
      rcases f with _ | f
      · norm_num at hq3
      · exact dvd_pow_self 3 (by omega)
    omega
  have h3 : (3 : L) ≠ 0 := by
    intro h
    apply h3K
    apply (algebraMap K L).injective
    rw [map_ofNat, h, map_zero]
  have : Finite (E.map Φ) := Finite.of_surjective _ (Φ.subgroupMap_surjective E)
  have h := card_sq_le_of_frobenius h3 (E.map Φ)
    (by
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      rw [← map_mul, ← map_mul, hcomm x hx y hy])
    (by
      rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow, hexp x hx, map_one])
    f hq3
    (by
      rintro _ ⟨x, -, rfl⟩ i j
      change iterateFrobenius L p f (algebraMap K L ((x : Matrix ι ι K) i j)) =
        algebraMap K L ((x : Matrix ι ι K) i j)
      rw [iterateFrobenius_def, ← map_pow, ← hK, FiniteField.pow_card])
  rwa [Subgroup.card_map_of_injective hΦ] at h

end Frobenius

section Unitary

variable {L : Type*} [Field L] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem card_sq_le_of_unitary [IsAlgClosed L] {p : ℕ} [Fact p.Prime] [CharP L p]
    (h3 : (3 : L) ≠ 0) (E : Subgroup (GL ι L)) [Finite E]
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hexp : ∀ x ∈ E, x ^ 3 = 1) (f : ℕ)
    (hq3 : p ^ f % 3 = 1)
    (hU : ∀ x ∈ E, ((x : Matrix ι ι L).map (iterateFrobenius L p f))ᵀ * (x : Matrix ι ι L) = 1) :
    Nat.card E ^ 2 ≤ 3 ^ Fintype.card ι := by
  classical
  obtain ⟨b, d, hb⟩ := Sec4.exists_common_eigenbasis_pow_three h3 E hcomm hexp
  set φ := iterateFrobenius L p f with hφ
  set F : (ι → L) → (ι → L) := fun v i => φ (v i) with hF
  have hFx : ∀ (x : GL ι L) v, F ((x : Matrix ι ι L) *ᵥ v) =
      (x : Matrix ι ι L).map φ *ᵥ F v := by
    intro x v
    funext i
    simp only [hF, Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply]
  have hFs : ∀ (t : L) v, F (t • v) = φ t • F v := by
    intro t v
    funext i
    simp [hF]
  have hinv : ∀ x ∈ E, ∀ v w, F ((x : Matrix ι ι L) *ᵥ v) ⬝ᵥ ((x : Matrix ι ι L) *ᵥ w) =
      F v ⬝ᵥ w := by
    intro x hx v w
    rw [hFx, ← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
      hU x hx, Matrix.one_mulVec]
  refine card_sq_le_of_pairing E hexp hb fun a => ?_
  obtain ⟨a', ha'⟩ : ∃ a', F (b a) ⬝ᵥ b a' ≠ 0 := by
    by_contra h
    push Not at h
    apply b.ne_zero a
    have hzero : ∀ w, F (b a) ⬝ᵥ w = 0 := by
      intro w
      rw [← b.sum_repr w, dotProduct_sum]
      simp [dotProduct_smul, h]
    funext i
    apply φ.injective
    have := hzero (Pi.single i 1)
    rw [dotProduct_single, mul_one] at this
    rw [Pi.zero_apply, map_zero]
    simpa [hF] using this
  refine ⟨a', fun x hx => ?_⟩
  have hd3 := Sec4.eigen_pow_three hb hx (hexp x hx) a
  have h1 := hinv x hx (b a) (b a')
  rw [hb x hx a, hb x hx a', hFs, smul_dotProduct, dotProduct_smul, hφ, iterateFrobenius_def,
    pow_eq_self_of_mod_one hd3 hq3, smul_smul, smul_eq_mul] at h1
  have hω : d x a * d x a' = 1 := by
    have : (d x a * d x a' - 1) * (F (b a) ⬝ᵥ b a') = 0 := by linear_combination h1
    rcases mul_eq_zero.mp this with h | h
    · linear_combination h
    · exact absurd h ha'
  exact eq_inv_of_mul_eq_one_right hω

theorem card_sq_le_of_unitary_of_mod_one {K : Type*} [Field K] {p f : ℕ} [Fact p.Prime]
    [CharP K p] (h3K : (3 : K) ≠ 0) (hq3 : p ^ f % 3 = 1) (E : Subgroup (GL ι K)) [Finite E]
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hexp : ∀ x ∈ E, x ^ 3 = 1)
    (hU : ∀ x ∈ E, ((x : Matrix ι ι K).map (· ^ (p ^ f)))ᵀ * (x : Matrix ι ι K) = 1) :
    Nat.card E ^ 2 ≤ 3 ^ Fintype.card ι := by
  set L := AlgebraicClosure K
  set Φ := Matrix.GeneralLinearGroup.map (n := ι) (algebraMap K L)
  have hΦ : Function.Injective Φ := Sec4.map_injective_GL _
  have h3 : (3 : L) ≠ 0 := by
    intro h
    apply h3K
    apply (algebraMap K L).injective
    rw [map_ofNat, h, map_zero]
  have : Finite (E.map Φ) := Finite.of_surjective _ (Φ.subgroupMap_surjective E)
  have h := card_sq_le_of_unitary h3 (E.map Φ)
    (by
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      rw [← map_mul, ← map_mul, hcomm x hx y hy])
    (by
      rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow, hexp x hx, map_one])
    f hq3
    (by
      rintro _ ⟨x, hx, rfl⟩
      change (((x : Matrix ι ι K).map (algebraMap K L)).map (iterateFrobenius L p f))ᵀ *
        (x : Matrix ι ι K).map (algebraMap K L) = 1
      have hcomp : ((x : Matrix ι ι K).map (algebraMap K L)).map (iterateFrobenius L p f) =
          ((x : Matrix ι ι K).map (· ^ (p ^ f))).map (algebraMap K L) := by
        ext i j
        simp [iterateFrobenius_def]
      rw [hcomp, ← Matrix.transpose_map, ← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply,
        ← map_mul, hU x hx, map_one])
  rwa [Subgroup.card_map_of_injective hΦ] at h

end Unitary

theorem census223Fact_projSL_four {p f : ℕ} [Fact p.Prime] (hf : 1 ≤ f) (hq3 : p ^ f % 3 = 2) :
    Census223Fact (projSL 4 (GaloisField p f)) := by
  set F := GaloisField p f
  have : Fintype F := Fintype.ofFinite F
  have hF : Fintype.card F = p ^ f := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card p f (by omega)]
  have hs : IsSimpleGroup (projSL 4 F) := by
    have := CFSG.BenderSuzuki.External.huppert_II_6_13 (K := F) 4 (by norm_num)
      (Or.inl (by norm_num)) (Or.inl (by norm_num))
    exact (Sec4.projSLEquivPSLn 4 F).isSimpleGroup
  refine Or.inl (Item223CensusProof.pRank_le_two_of_card_le_nine fun B hB =>
    Sec4.card_le_of_projImage (GeneralLinearGroup.det : GL (Fin 4) F →* Fˣ).ker hs (m := 4)
      (by norm_num) (fun c hc => ?_) (by norm_num) (fun P hPH hcomm hexp => ?_) B hB)
  · apply Sec4.pow_four_of_det_scalar
    have := congrArg Units.val (MonoidHom.mem_ker.mp hc)
    rwa [GeneralLinearGroup.val_det_apply] at this
  · have : Finite P := Finite.of_injective _ Subtype.val_injective
    have h := card_sq_le_of_card_mod_two hF hq3 P hcomm hexp
    rw [Fintype.card_fin] at h
    nlinarith

theorem unitary_of_mem_closure_su {n p f : ℕ} [Fact p.Prime] {K : Type} [Field K] [CharP K p]
    {A : GL (Fin n) K}
    (hA : A ∈ Subgroup.closure {A : GL (Fin n) K | GeneralLinearGroup.det A = 1 ∧
      ((A : Matrix (Fin n) (Fin n) K).map (· ^ (p ^ f)))ᵀ * (A : Matrix (Fin n) (Fin n) K) = 1}) :
    ((A : Matrix (Fin n) (Fin n) K).map (· ^ (p ^ f)))ᵀ * (A : Matrix (Fin n) (Fin n) K) = 1 := by
  set φ := iterateFrobenius K p f
  have hφ : ∀ M : Matrix (Fin n) (Fin n) K, M.map (· ^ (p ^ f)) = φ.mapMatrix M := by
    intro M
    ext i j
    simp [φ, iterateFrobenius_def]
  simp only [hφ] at hA ⊢
  induction hA using Subgroup.closure_induction with
  | mem x hx => rw [← hφ]; exact hx.2
  | one => simp
  | mul x y _ _ hx hy =>
    rw [Units.val_mul, map_mul, Matrix.transpose_mul, Matrix.mul_assoc,
      ← Matrix.mul_assoc (φ.mapMatrix (x : Matrix (Fin n) (Fin n) K))ᵀ, hx, Matrix.one_mul, hy]
  | inv x _ hx =>
    have hX' : (φ.mapMatrix (x : Matrix (Fin n) (Fin n) K))ᵀ =
        ((x⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
      calc (φ.mapMatrix (x : Matrix (Fin n) (Fin n) K))ᵀ =
          (φ.mapMatrix (x : Matrix (Fin n) (Fin n) K))ᵀ *
            ((x : Matrix (Fin n) (Fin n) K) *
              ((x⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
            rw [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
        _ = ((φ.mapMatrix (x : Matrix (Fin n) (Fin n) K))ᵀ * (x : Matrix (Fin n) (Fin n) K)) *
            ((x⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by rw [Matrix.mul_assoc]
        _ = ((x⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by rw [hx, Matrix.one_mul]
    have hYZ : φ.mapMatrix (x : Matrix (Fin n) (Fin n) K) *
        φ.mapMatrix ((x⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
      rw [← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one]
    calc (φ.mapMatrix ((x⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))ᵀ *
          ((x⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        (φ.mapMatrix ((x⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))ᵀ *
          (φ.mapMatrix (x : Matrix (Fin n) (Fin n) K))ᵀ := by rw [hX']
      _ = (φ.mapMatrix (x : Matrix (Fin n) (Fin n) K) *
          φ.mapMatrix ((x⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))ᵀ := by
          rw [Matrix.transpose_mul]
      _ = 1 := by rw [hYZ, Matrix.transpose_one]

theorem census223Fact_projSU_four {p f : ℕ} [Fact p.Prime] (hp3 : p ≠ 3) (hf : 1 ≤ f)
    (hq3 : p ^ f % 3 = 1) : Census223Fact (projSU 4 p f) := by
  set F := GaloisField p (2 * f)
  have hF : Nat.card F = p ^ (2 * f) := GaloisField.card p (2 * f) (by omega)
  have h3 : (3 : F) ≠ 0 := Sec4.three_ne_zero_of_card Fact.out hp3 hF
  have hs : IsSimpleGroup (projSU 4 p f) := by
    have := CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU F p f
      (by rw [hF, ← pow_mul, mul_comm]) 4 (by norm_num) (by
        intro h
        exact absurd (Prod.mk.inj h).1 (by norm_num))
    exact (Sec4.projSUEquivStatedProj 4 p f).isSimpleGroup
  refine Or.inl (Item223CensusProof.pRank_le_two_of_card_le_nine fun B hB =>
    Sec4.card_le_of_projImage (Subgroup.closure {A : GL (Fin 4) F | GeneralLinearGroup.det A = 1 ∧
      ((A : Matrix (Fin 4) (Fin 4) F).map (· ^ (p ^ f)))ᵀ * (A : Matrix (Fin 4) (Fin 4) F) = 1})
      hs (m := 4) (by norm_num)
      (fun c hc => Sec4.pow_four_of_det_scalar (Sec4.det_of_mem_closure_su _ hc))
      (by norm_num) (fun P hPH hcomm hexp => ?_) B hB)
  have : Finite F := inferInstance
  have : Finite P := Finite.of_injective _ Subtype.val_injective
  have h := card_sq_le_of_unitary_of_mod_one h3 hq3 P hcomm hexp
    fun x hx => unitary_of_mem_closure_su (hPH hx)
  rw [Fintype.card_fin] at h
  nlinarith

end Item223CensusResProof

open Item223CensusResProof

theorem census223RankTwoOddRest_of (hG2 : G2OddThreeRankTwo) : Census223RankTwoOddRest :=
  fun p _ hp3 => ⟨fun X _ hX => Or.inl (hG2 p hp3 X hX),
    fun hp => census223Fact_projSU_four (by omega) le_rfl (by rw [pow_one]; exact hp),
    fun hp => census223Fact_projSL_four le_rfl (by rw [pow_one]; exact hp)⟩

theorem two_pow_mod_three_of_even {n : ℕ} (hn : Even n) : 2 ^ n % 3 = 1 := by
  obtain ⟨k, rfl⟩ := hn
  rw [← two_mul, pow_mul, Nat.pow_mod]
  norm_num

theorem census223RankTwoEvenRest_of (hExc : ExcEvenThreeRankTwo) : Census223RankTwoEvenRest := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact ⟨fun n hn hev => census223Fact_projSU_four (by norm_num) hn
    (two_pow_mod_three_of_even hev), fun X _ f hX => Or.inl (hExc X f hX)⟩

end CFSG.RankThree.PartTwo.Sec21
