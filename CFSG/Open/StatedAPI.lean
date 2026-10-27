module

public import CFSG.Open.StatedDefs

public section

namespace CFSG.Open.StatedAPI

open Matrix

theorem statedScalars_eq_center (ι : Type) [Fintype ι] [DecidableEq ι] (K : Type) [Field K] :
    StatedScalars ι K = Subgroup.center (GL ι K) :=
  GeneralLinearGroup.center_eq_range_scalar.symm

theorem statedSL_eq_ker_det (n : ℕ) (K : Type) [Field K] :
    StatedSL n K = (GeneralLinearGroup.det : GL (Fin n) K →* Kˣ).ker := by
  have h : {A : GL (Fin n) K | (A : Matrix (Fin n) (Fin n) K).det = 1} =
      ((GeneralLinearGroup.det : GL (Fin n) K →* Kˣ).ker : Set (GL (Fin n) K)) := by
    ext A
    simp [Units.ext_iff]
  rw [StatedSL, h, Subgroup.closure_eq]

theorem mem_statedSL_iff {n : ℕ} {K : Type} [Field K] {A : GL (Fin n) K} :
    A ∈ StatedSL n K ↔ (A : Matrix (Fin n) (Fin n) K).det = 1 := by
  rw [statedSL_eq_ker_det, MonoidHom.mem_ker]
  simp [Units.ext_iff]

theorem mem_statedSL_of_det {n : ℕ} {K : Type} [Field K] {A : GL (Fin n) K}
    (h : (A : Matrix (Fin n) (Fin n) K).det = 1) : A ∈ StatedSL n K :=
  Subgroup.subset_closure h

theorem det_of_mem_statedSL {n : ℕ} {K : Type} [Field K] {A : GL (Fin n) K}
    (hA : A ∈ StatedSL n K) : (A : Matrix (Fin n) (Fin n) K).det = 1 :=
  mem_statedSL_iff.1 hA

theorem statedSL_eq_range_toGL (n : ℕ) (K : Type) [Field K] :
    StatedSL n K = (SpecialLinearGroup.toGL :
      SpecialLinearGroup (Fin n) K →* GL (Fin n) K).range := by
  ext A
  rw [mem_statedSL_iff, MonoidHom.mem_range]
  constructor
  · intro hA
    exact ⟨⟨A, hA⟩, Units.ext rfl⟩
  · rintro ⟨B, rfl⟩
    exact B.prop

theorem card_statedSL (n : ℕ) (K : Type) [Field K] :
    Nat.card (StatedSL n K) = Nat.card (SpecialLinearGroup (Fin n) K) := by
  rw [statedSL_eq_range_toGL]
  exact (Nat.card_congr (MonoidHom.ofInjective SpecialLinearGroup.toGL_injective).toEquiv).symm

theorem card_statedSL_two (K : Type) [Field K] [Finite K] :
    Nat.card (StatedSL 2 K) = Nat.card K * (Nat.card K ^ 2 - 1) := by
  let := Fintype.ofFinite K
  have hq : 1 < Fintype.card K := Fintype.one_lt_card
  rw [card_statedSL, Matrix.card_SL_field, Fin.prod_univ_two, Fin.val_zero, Fin.val_one, pow_zero,
    pow_one, Nat.card_eq_fintype_card, show Fintype.card K ^ 2 - Fintype.card K =
      Fintype.card K * (Fintype.card K - 1) by rw [Nat.mul_sub_one, sq], ← mul_assoc,
    Nat.mul_div_cancel _ (by omega), mul_comm]

theorem card_statedSL_three (K : Type) [Field K] [Finite K] :
    Nat.card (StatedSL 3 K) = Nat.card K ^ 3 * ((Nat.card K ^ 2 - 1) * (Nat.card K ^ 3 - 1)) := by
  let := Fintype.ofFinite K
  rw [card_statedSL, Matrix.card_SL_field, ← Nat.card_eq_fintype_card, Fin.prod_univ_three]
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one]
  set q := Nat.card K
  have hq : 2 ≤ q := Finite.one_lt_card
  have h1 : 1 ≤ q := by omega
  have hprod : (q ^ 3 - 1) * (q ^ 3 - q) * (q ^ 3 - q ^ 2) =
      (q - 1) * (q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1))) := by
    have e1 : 1 ≤ q ^ 3 := Nat.one_le_pow _ _ (by omega)
    have e2 : q ≤ q ^ 3 := Nat.le_self_pow (by norm_num) q
    have e3 : q ^ 2 ≤ q ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
    have e4 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
    zify [e1, e2, e3, e4, h1]
    ring
  rw [hprod, Nat.mul_div_cancel_left _ (by omega)]

theorem statedSU_le_statedSL (n q : ℕ) (K : Type) [Field K] : StatedSU n q K ≤ StatedSL n K :=
  (Subgroup.closure_le _).2 fun _ hA => Subgroup.subset_closure hA.1

theorem det_of_mem_statedSU {n q : ℕ} {K : Type} [Field K] {A : GL (Fin n) K}
    (hA : A ∈ StatedSU n q K) : (A : Matrix (Fin n) (Fin n) K).det = 1 :=
  det_of_mem_statedSL (statedSU_le_statedSL n q K hA)

section Projective

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]

theorem ker_mk_comp_subtype (H : Subgroup (GL ι K)) :
    ((ProjGenLinGroup.mk : GL ι K →* ProjGenLinGroup ι K).comp H.subtype).ker =
      (StatedScalars ι K).subgroupOf H := by
  rw [← MonoidHom.comap_ker, ProjGenLinGroup.ker_mk, GeneralLinearGroup.center_eq_range_scalar]
  rfl

@[expose] noncomputable def mapMkEquivStatedProj (H : Subgroup (GL ι K)) :
    H.map (ProjGenLinGroup.mk : GL ι K →* ProjGenLinGroup ι K) ≃* StatedProj H :=
  ((QuotientGroup.quotientMulEquivOfEq (ker_mk_comp_subtype H).symm).trans
    ((QuotientGroup.quotientKerEquivRange _).trans
      (MulEquiv.subgroupCongr (by rw [MonoidHom.range_comp, Subgroup.range_subtype])))).symm

@[simp] theorem coe_mapMkEquivStatedProj_symm_mk (H : Subgroup (GL ι K)) (A : H) :
    ((mapMkEquivStatedProj H).symm (A : StatedProj H) : ProjGenLinGroup ι K) =
      ProjGenLinGroup.mk (A : GL ι K) :=
  rfl

@[simp] theorem mapMkEquivStatedProj_mk (H : Subgroup (GL ι K)) (A : H) :
    mapMkEquivStatedProj H ⟨ProjGenLinGroup.mk (A : GL ι K), Subgroup.mem_map_of_mem _ A.2⟩ =
      (A : StatedProj H) := by
  rw [← MulEquiv.eq_symm_apply]
  exact Subtype.ext (coe_mapMkEquivStatedProj_symm_mk H A).symm

theorem statedProj_mk_eq_iff (Hg : Subgroup (GL ι K)) (x y : Hg) :
    (QuotientGroup.mk x : StatedProj Hg) = QuotientGroup.mk y ↔
      ∃ u : Kˣ, ((y : GL ι K) : Matrix ι ι K) =
        ((x : GL ι K) : Matrix ι ι K) * ((u : K) • (1 : Matrix ι ι K)) := by
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range]
  constructor
  · rintro ⟨u, hu⟩
    refine ⟨u, ?_⟩
    have h1 : (y : GL ι K) = (x : GL ι K) * Matrix.GeneralLinearGroup.scalar ι u := by
      rw [hu]; simp
    have h2 := congrArg (fun g : GL ι K => (g : Matrix ι ι K)) h1
    simp only [Units.val_mul] at h2
    rw [h2, Matrix.GeneralLinearGroup.coe_scalar]
    simp [Matrix.smul_one_eq_diagonal]
  · rintro ⟨u, hu⟩
    refine ⟨u, ?_⟩
    have h1 : (x : GL ι K) * Matrix.GeneralLinearGroup.scalar ι u = (y : GL ι K) := by
      apply Units.ext
      simp only [Units.val_mul]
      rw [hu, Matrix.GeneralLinearGroup.coe_scalar]
      simp [Matrix.smul_one_eq_diagonal]
    have h2 : ((x⁻¹ * y : Hg) : GL ι K) = (x : GL ι K)⁻¹ * (y : GL ι K) := by simp
    rw [h2, ← h1, inv_mul_cancel_left]

theorem statedScalars_subgroupOf_le_center (H : Subgroup (GL ι K)) :
    (StatedScalars ι K).subgroupOf H ≤ Subgroup.center H := by
  intro x hx
  rw [Subgroup.mem_subgroupOf, statedScalars_eq_center] at hx
  rw [Subgroup.mem_center_iff]
  intro g
  exact Subtype.ext (Subgroup.mem_center_iff.mp hx g)

end Projective

@[expose] def gramIsometry {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    (J : Matrix ι ι K) : Subgroup (GL ι K) where
  carrier := {A | (A : Matrix ι ι K)ᵀ * J * (A : Matrix ι ι K) = J}
  one_mem' := by simp
  mul_mem' {A B} hA hB := by
    simp only [Set.mem_ofPred_eq, Units.val_mul, transpose_mul] at hA hB ⊢
    calc (B : Matrix ι ι K)ᵀ * (A : Matrix ι ι K)ᵀ * J * ((A : Matrix ι ι K) * B)
        = (B : Matrix ι ι K)ᵀ * ((A : Matrix ι ι K)ᵀ * J * (A : Matrix ι ι K)) *
            (B : Matrix ι ι K) := by
          simp only [Matrix.mul_assoc]
      _ = J := by rw [hA, hB]
  inv_mem' {A} hA := by
    simp only [Set.mem_ofPred_eq] at hA ⊢
    have h₂ : (A : Matrix ι ι K) * ((A⁻¹ : GL ι K) : Matrix ι ι K) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    calc ((A⁻¹ : GL ι K) : Matrix ι ι K)ᵀ * J * ((A⁻¹ : GL ι K) : Matrix ι ι K)
        = ((A⁻¹ : GL ι K) : Matrix ι ι K)ᵀ * ((A : Matrix ι ι K)ᵀ * J * (A : Matrix ι ι K)) *
            ((A⁻¹ : GL ι K) : Matrix ι ι K) := by rw [hA]
      _ = ((A : Matrix ι ι K) * ((A⁻¹ : GL ι K) : Matrix ι ι K))ᵀ * J *
            ((A : Matrix ι ι K) * ((A⁻¹ : GL ι K) : Matrix ι ι K)) := by
          simp only [transpose_mul, Matrix.mul_assoc]
      _ = J := by rw [h₂, transpose_one, Matrix.one_mul, Matrix.mul_one]

theorem mem_statedSp_iff {n : ℕ} {K : Type} [Field K] {A : GL (Fin n ⊕ Fin n) K} :
    A ∈ StatedSp n K ↔ (A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)ᵀ *
      fromBlocks 0 1 (-1) 0 * (A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) =
        fromBlocks 0 1 (-1) 0 := by
  have h : StatedSp n K = gramIsometry (fromBlocks 0 1 (-1) 0) := by
    rw [StatedSp]
    exact Subgroup.closure_eq (gramIsometry _)
  rw [h]
  rfl

theorem scalar_mem_statedSp_iff {n : ℕ} {K : Type} [Field K] (hn : 1 ≤ n) (c : Kˣ) :
    GeneralLinearGroup.scalar (Fin n ⊕ Fin n) c ∈ StatedSp n K ↔ c ^ 2 = 1 := by
  have hconj : (diagonal fun _ : Fin n ⊕ Fin n => (c : K))ᵀ * fromBlocks 0 1 (-1) 0 *
      diagonal (fun _ : Fin n ⊕ Fin n => (c : K)) =
        ((c : K) * c) • fromBlocks (0 : Matrix (Fin n) (Fin n) K) 1 (-1) 0 := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [Matrix.mul_apply, Matrix.diagonal_apply] <;> ring
  have hu : (c : K) * c = 1 ↔ c ^ 2 = 1 := by
    rw [← Units.val_mul, ← sq, Units.val_eq_one]
  rw [mem_statedSp_iff, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, hconj, ← hu]
  constructor
  · intro h
    have h1 := congrFun (congrFun h (Sum.inl ⟨0, hn⟩)) (Sum.inr ⟨0, hn⟩)
    simpa [Matrix.fromBlocks_apply₁₂] using h1
  · intro h
    rw [h, one_smul]

theorem statedScalars_subgroupOf_statedSp_eq_bot {n : ℕ} {K : Type} [Field K] [CharP K 2] :
    (StatedScalars (Fin n ⊕ Fin n) K).subgroupOf (StatedSp n K) = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  obtain ⟨c, hc⟩ := Subgroup.mem_subgroupOf.1 hg
  rw [Subgroup.mem_bot]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact Subtype.ext (Units.ext (Matrix.ext fun a => by rcases a with a | a <;> exact a.elim0))
  have hsp : GeneralLinearGroup.scalar (Fin n ⊕ Fin n) c ∈ StatedSp n K := by
    rw [hc]; exact (g : StatedSp n K).2
  have hc1 : c = 1 := by
    apply Units.ext
    have h := congrArg Units.val ((scalar_mem_statedSp_iff hn c).1 hsp)
    rw [Units.val_pow_eq_pow_val, Units.val_one, sq] at h
    rcases mul_self_eq_one_iff.1 h with h1 | h1
    · exact h1
    · rw [h1, CharTwo.neg_eq, Units.val_one]
  apply Subtype.ext
  rw [← hc, hc1, map_one]
  rfl

theorem map_mem_statedSp {n : ℕ} {K L : Type} [Field K] [Field L] (φ : K →+* L)
    {g : GL (Fin n ⊕ Fin n) K} (hg : g ∈ StatedSp n K) :
    GeneralLinearGroup.map φ g ∈ StatedSp n L := by
  rw [mem_statedSp_iff] at hg ⊢
  have hJ : (fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K).map φ =
      fromBlocks 0 1 (-1) 0 := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> simp [Matrix.one_apply, apply_ite φ]
  have h := congrArg (fun M => M.map φ) hg
  simp only [Matrix.map_mul, Matrix.transpose_map, hJ] at h
  exact h

theorem statedClassicalModel_of_mulEquiv {G G' : Type} [Group G] [Group G'] (e : G ≃* G')
    {t : StatedLieTag} {n p f : ℕ} (h : StatedClassicalModel G t n p f) :
    StatedClassicalModel G' t n p f := by
  obtain ⟨hadm, hmodel⟩ := h
  refine ⟨hadm, ?_⟩
  cases t <;> first
    | exact hmodel
    | (obtain ⟨K, hK, hKf, hcard, ⟨e'⟩⟩ := hmodel
       exact ⟨K, hK, hKf, hcard, ⟨e.symm.trans e'⟩⟩)
    | (obtain ⟨K, hK, hKf, hcard, b, c, hbc, ⟨e'⟩⟩ := hmodel
       exact ⟨K, hK, hKf, hcard, b, c, hbc, ⟨e.symm.trans e'⟩⟩)

theorem not_dvd_card_statedScalars_subgroupOf {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type}
    [Field K] (M : Subgroup (GL ι K)) [Finite M] {d p : ℕ} (hp : p.Prime) (hpd : ¬ p ∣ d)
    (hd : ∀ c : Kˣ, Matrix.GeneralLinearGroup.scalar ι c ∈ M → c ^ d = 1) :
    ¬ p ∣ Nat.card ((StatedScalars ι K).subgroupOf M) := by
  intro hdvd
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hdvd
  obtain ⟨c, hc⟩ := Subgroup.mem_subgroupOf.1 x.2
  have hcM : Matrix.GeneralLinearGroup.scalar ι c ∈ M := by
    rw [hc]
    exact x.1.2
  have hxd : x ^ d = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_pow, Subgroup.coe_one, Subgroup.coe_one, ← hc, ← map_pow,
      hd c hcM, map_one]
  exact hpd (hx ▸ orderOf_dvd_of_pow_eq_one hxd)

theorem statedLieAdmissible_G2_two {f : ℕ} (hf : 2 ≤ f) : StatedLieAdmissible .G2 0 2 f := by
  refine ⟨Nat.prime_two, by omega, rfl, ?_⟩
  calc 3 ≤ 2 ^ 2 := by norm_num
    _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf

theorem pow_three_eq_one_of_mem_statedScalars {K : Type} [Field K] {z : GL (Fin 3) K}
    (hz : z ∈ StatedScalars (Fin 3) K)
    (hdet : (z : Matrix (Fin 3) (Fin 3) K).det = 1) : z ^ 3 = 1 := by
  obtain ⟨c, rfl⟩ := hz
  have h1 : ((c : K)) ^ 3 = 1 := by
    rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.det_diagonal,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hdet
    exact hdet
  rw [← map_pow]
  have h2 : c ^ 3 = 1 := Units.ext (by simpa using h1)
  rw [h2, map_one]

theorem exists_smul_mulVec_of_mk_eq {σ : Type} [Fintype σ] [DecidableEq σ] {K : Type} [Field K]
    {Q₀ : (σ → K) → K} {A B : StatedOmega Q₀}
    (h : (QuotientGroup.mk A : StatedProj (StatedOmega Q₀)) = QuotientGroup.mk B) :
    ∃ d : K, ∀ x : σ → K, ((A : GL σ K) : Matrix σ σ K) *ᵥ x =
      d • (((B : GL σ K) : Matrix σ σ K) *ᵥ x) := by
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at h
  obtain ⟨u, hu⟩ := (MonoidHom.mem_range).1 h
  have hAB : (A : GL σ K) * Matrix.GeneralLinearGroup.scalar σ u = (B : GL σ K) := by
    rw [hu]; simp
  refine ⟨((u⁻¹ : Kˣ) : K), fun x => ?_⟩
  have : (B : GL σ K) * Matrix.GeneralLinearGroup.scalar σ u⁻¹ = (A : GL σ K) := by
    rw [← hAB, mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one]
  rw [← this, Units.val_mul, ← Matrix.mulVec_mulVec]
  have hs : ((Matrix.GeneralLinearGroup.scalar σ u⁻¹ : GL σ K) : Matrix σ σ K) =
      ((u⁻¹ : Kˣ) : K) • (1 : Matrix σ σ K) := by
    ext i j
    simp [Matrix.GeneralLinearGroup.scalar, Matrix.one_apply, Matrix.diagonal_apply]
  rw [hs, Matrix.smul_mulVec, Matrix.one_mulVec, Matrix.mulVec_smul]

theorem statedScalars_subgroupOf_mul_comm {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type}
    [Field K] (H : Subgroup (GL ι K)) :
    ∀ x ∈ (StatedScalars ι K).subgroupOf H, ∀ y ∈ (StatedScalars ι K).subgroupOf H,
      x * y = y * x := by
  intro x hx y _
  have hc : (x : GL ι K) ∈ Subgroup.center (GL ι K) := by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    exact hx
  exact Subtype.ext (Subgroup.mem_center_iff.mp hc (y : GL ι K)).symm

theorem not_psl_two_of_statedLieAdmissible_three_one {t : StatedLieTag} {n : ℕ}
    (hadm : StatedLieAdmissible t n 3 1) : ¬ (t = .PSL ∧ n = 2) := by
  rintro ⟨rfl, rfl⟩
  obtain ⟨-, -, -, -, h⟩ := hadm
  exact h (by norm_num)

theorem mem_statedSL_zmod_two {n : ℕ} (g : GL (Fin n) (ZMod 2)) : g ∈ StatedSL n (ZMod 2) := by
  rw [mem_statedSL_iff]
  have h : GeneralLinearGroup.det g = 1 := Subsingleton.elim _ _
  simpa [Units.ext_iff] using h

theorem statedScalars_zmod_two_eq_bot (ι : Type) [Fintype ι] [DecidableEq ι] :
    StatedScalars ι (ZMod 2) = ⊥ := by
  rw [eq_bot_iff]
  rintro _ ⟨c, rfl⟩
  rw [Subgroup.mem_bot, Subsingleton.elim c 1, map_one]

theorem card_statedSL_three_zmod_two : Nat.card (StatedSL 3 (ZMod 2)) = 168 := by
  rw [card_statedSL_three, Nat.card_zmod]
  rfl

theorem card_statedSL_four_zmod_two : Nat.card (StatedSL 4 (ZMod 2)) = 20160 := by
  rw [card_statedSL, Matrix.card_SL_field, Fin.prod_univ_four, ZMod.card]
  rfl

theorem card_statedSL_five_zmod_two : Nat.card (StatedSL 5 (ZMod 2)) = 9999360 := by
  rw [card_statedSL, Matrix.card_SL_field, Fin.prod_univ_five, ZMod.card]
  rfl

theorem card_statedSL_three_of_card_eq_two {K : Type} [Field K] (hK : Nat.card K = 2) :
    Nat.card (StatedSL 3 K) = 168 := by
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  rw [card_statedSL_three, hK]
  rfl

theorem card_statedSL_four_of_card_eq_two {K : Type} [Field K] (hK : Nat.card K = 2) :
    Nat.card (StatedSL 4 K) = 20160 := by
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  let := Fintype.ofFinite K
  rw [card_statedSL, Matrix.card_SL_field, Fin.prod_univ_four, ← Nat.card_eq_fintype_card, hK]
  rfl

theorem card_statedSL_five_of_card_eq_two {K : Type} [Field K] (hK : Nat.card K = 2) :
    Nat.card (StatedSL 5 K) = 9999360 := by
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  let := Fintype.ofFinite K
  rw [card_statedSL, Matrix.card_SL_field, Fin.prod_univ_five, ← Nat.card_eq_fintype_card, hK]
  rfl

theorem statedScalars_subgroupOf_statedSL_two_eq_bot {K : Type} [Field K] [CharP K 2] :
    (StatedScalars (Fin 2) K).subgroupOf (StatedSL 2 K) = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  obtain ⟨c, hc⟩ := Subgroup.mem_subgroupOf.1 hg
  have hdet := mem_statedSL_iff.1 (hc ▸ (g : StatedSL 2 K).2 :
    GeneralLinearGroup.scalar (Fin 2) c ∈ StatedSL 2 K)
  rw [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.det_diagonal,
    Fin.prod_const] at hdet
  have hc1 : c = 1 := by
    apply Units.ext
    rw [sq] at hdet
    rcases mul_self_eq_one_iff.1 hdet with h1 | h1
    · exact h1
    · rw [h1, CharTwo.neg_eq, Units.val_one]
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  rw [← hc, hc1, map_one]
  rfl

end CFSG.Open.StatedAPI
