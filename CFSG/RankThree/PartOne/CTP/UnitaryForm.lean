module

public import CFSG.RankThree.PartOne.CTP.UnitaryBlk

public section

namespace CFSG.RankThree.PartOne.CTP

open Matrix
open CFSG.LieType.Universal.Unitary (SUid conjTr conjTr_mul)
open CFSG.LieType.Steinberg (embSUid embSUid_injective conjTr_diagonal)
open CFSG.ClassicalGroups.Unitary (IsUnitaryInvolution herm herm_mulVec mkSU herm_add_left
  herm_add_right herm_smul_left herm_smul_right herm_zero_left herm_zero_right herm_conj
  herm_self_fixed herm_eq_zero_comm eq_zero_of_herm exists_smul_norm_one exists_norm_one_perp
  exists_aniso_of_lt hermL)
open scoped MatrixGroups

variable {F : Type} [Field F] {σ : F ≃+* F} {W ℓ : Submodule F (Fin 3 → F)}

private theorem finrank_line_of_compl (hc : IsCompl W ℓ) (hW : Module.finrank F W = 2) :
    Module.finrank F ℓ = 1 := by
  have := Submodule.finrank_add_eq_of_isCompl hc
  rw [Module.finrank_fin_fun, hW] at this
  omega

private theorem line_eq_span {u : Fin 3 → F} (hℓ : Module.finrank F ℓ = 1) (hu : u ∈ ℓ)
    (hu0 : u ≠ 0) : ℓ = Submodule.span F {u} := by
  refine (Submodule.eq_of_le_of_finrank_eq ?_ ?_).symm
  · exact Submodule.span_le.mpr (by simpa using hu)
  · rw [finrank_span_singleton hu0, hℓ]

private theorem exists_ne_zero_of_finrank_one (hℓ : Module.finrank F ℓ = 1) :
    ∃ u ∈ ℓ, u ≠ 0 := by
  have hne : ℓ ≠ ⊥ := fun h => by rw [h, finrank_bot] at hℓ; omega
  exact (Submodule.ne_bot_iff _).mp hne

theorem herm_ne_zero_of_mem_line (hσ : IsUnitaryInvolution σ) (hc : IsCompl W ℓ)
    (hW : Module.finrank F W = 2) (horth : ∀ w ∈ W, ∀ u ∈ ℓ, herm σ w u = 0) {u : Fin 3 → F}
    (hu : u ∈ ℓ) (hu0 : u ≠ 0) : herm σ u u ≠ 0 := by
  intro h
  apply hu0
  apply eq_zero_of_herm σ
  intro y
  have hy : y ∈ W ⊔ ℓ := by rw [hc.sup_eq_top]; exact Submodule.mem_top
  obtain ⟨w, hw, l, hl, rfl⟩ := Submodule.mem_sup.mp hy
  rw [line_eq_span (finrank_line_of_compl hc hW) hu hu0] at hl
  obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hl
  rw [herm_add_right, herm_smul_right, h, mul_zero, add_zero]
  exact herm_eq_zero_comm σ hσ.invol (horth w hw u hu)

theorem no_isotropic_plane (hσ : IsUnitaryInvolution σ) (hc : IsCompl W ℓ)
    (hW : Module.finrank F W = 2) (hiso : ∀ w ∈ W, ∀ w' ∈ W, herm σ w w' = 0) : False := by
  obtain ⟨u, hu, hu0⟩ := exists_ne_zero_of_finrank_one (finrank_line_of_compl hc hW)
  have hℓu := line_eq_span (finrank_line_of_compl hc hW) hu hu0
  have key : ∀ w ∈ W, w ≠ 0 → herm σ w u ≠ 0 := by
    intro w hw hw0 h0
    apply hw0
    apply eq_zero_of_herm σ
    intro y
    have hy : y ∈ W ⊔ ℓ := by rw [hc.sup_eq_top]; exact Submodule.mem_top
    obtain ⟨w', hw', l, hl, rfl⟩ := Submodule.mem_sup.mp hy
    rw [hℓu] at hl
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hl
    rw [herm_add_right, hiso w hw w' hw', herm_smul_right, h0, mul_zero, add_zero]
  have hWne : W ≠ ⊥ := fun h => by rw [h, finrank_bot] at hW; omega
  obtain ⟨w₁, hw₁, hw₁0⟩ := (Submodule.ne_bot_iff _).mp hWne
  obtain ⟨w₂, hw₂, hw₂n⟩ : ∃ w ∈ W, w ∉ Submodule.span F {w₁} := by
    by_contra hcon
    push Not at hcon
    have hle : W ≤ Submodule.span F {w₁} := hcon
    have := Submodule.finrank_mono hle
    rw [hW, finrank_span_singleton hw₁0] at this
    omega
  have hx1 := key w₁ hw₁ hw₁0
  set c : F := σ (-(herm σ w₂ u / herm σ w₁ u)) with hcdef
  have hσc : σ c = -(herm σ w₂ u / herm σ w₁ u) := by rw [hcdef, hσ.invol]
  have hne : c • w₁ + w₂ ≠ 0 := by
    intro h
    apply hw₂n
    have : w₂ = -(c • w₁) := by rw [eq_neg_iff_add_eq_zero, add_comm]; exact h
    rw [this]
    exact Submodule.neg_mem _ (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))
  refine key _ (W.add_mem (W.smul_mem _ hw₁) hw₂) hne ?_
  rw [herm_add_left, herm_smul_left, hσc]
  field_simp
  ring

theorem herm_eigen_orth {M : Matrix (Fin 3) (Fin 3) F} (hM : conjTr σ M * M = 1)
    {w u : Fin 3 → F} {a b : F} (hw : M *ᵥ w = a • w) (hu : M *ᵥ u = b • u) :
    (σ a * b - 1) * herm σ w u = 0 := by
  have h := herm_mulVec σ M w u
  rw [hM, one_mulVec, hw, hu, herm_smul_left, herm_smul_right] at h
  linear_combination h

theorem orth_of_eigen_unitary (hσ : IsUnitaryInvolution σ) {M : Matrix (Fin 3) (Fin 3) F}
    (hM : conjTr σ M * M = 1) (hc : IsCompl W ℓ) (hW : Module.finrank F W = 2) {a b : F}
    (hab : a ≠ b) (hWa : ∀ w ∈ W, M *ᵥ w = a • w) (hℓb : ∀ u ∈ ℓ, M *ᵥ u = b • u) :
    ∀ w ∈ W, ∀ u ∈ ℓ, herm σ w u = 0 := by
  have hna : σ a * a = 1 := by
    by_contra hne
    apply no_isotropic_plane hσ hc hW
    intro w hw w' hw'
    have := herm_eigen_orth hM (hWa w hw) (hWa w' hw')
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hne)
  have ha0 : a ≠ 0 := by
    rintro rfl
    simp at hna
  intro w hw u hu
  have h := herm_eigen_orth hM (hWa w hw) (hℓb u hu)
  refine (mul_eq_zero.mp h).resolve_left fun h1 => hab ?_
  have hσa : σ a = a⁻¹ := eq_inv_of_mul_eq_one_left hna
  rw [hσa] at h1
  have h2 : a⁻¹ * b = 1 := sub_eq_zero.mp h1
  field_simp at h2
  exact h2.symm

theorem exists_orthonormal_adapted (hσ : IsUnitaryInvolution σ) (hc : IsCompl W ℓ)
    (hW : Module.finrank F W = 2) (horth : ∀ w ∈ W, ∀ u ∈ ℓ, herm σ w u = 0) :
    ∃ b : Module.Basis (Fin 3) F (Fin 3 → F),
      (∀ i j, herm σ (b i) (b j) = if i = j then 1 else 0) ∧
        Submodule.span F {b 0, b 1} = W ∧ Submodule.span F {b 2} = ℓ := by
  have hℓ : Module.finrank F ℓ = 1 := finrank_line_of_compl hc hW
  obtain ⟨u, hu, hu0⟩ := exists_ne_zero_of_finrank_one hℓ
  obtain ⟨c, hc1⟩ := exists_smul_norm_one hσ (herm_ne_zero_of_mem_line hσ hc hW horth hu hu0)
  set b₂ : Fin 3 → F := c • u with hb₂
  have hb₂ℓ : b₂ ∈ ℓ := ℓ.smul_mem c hu
  have hb₂0 : b₂ ≠ 0 := fun h => by
    rw [h, herm_zero_left] at hc1
    exact zero_ne_one hc1
  have hℓb₂ : ℓ = Submodule.span F {b₂} := line_eq_span hℓ hb₂ℓ hb₂0
  have hperp : ∀ z, herm σ b₂ z = 0 → z ∈ W := by
    intro z hz
    have hz' : z ∈ W ⊔ ℓ := by rw [hc.sup_eq_top]; exact Submodule.mem_top
    obtain ⟨w, hw, l, hl, rfl⟩ := Submodule.mem_sup.mp hz'
    rw [hℓb₂] at hl
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hl
    have h1 : herm σ b₂ w = 0 := herm_eq_zero_comm σ hσ.invol (horth w hw b₂ hb₂ℓ)
    rw [herm_add_right, h1, herm_smul_right, hc1, mul_one, zero_add] at hz
    rw [hz, zero_smul, add_zero]
    exact hw
  obtain ⟨b₀, hb₀1, hb₀2⟩ := exists_norm_one_perp hσ (n := 3) (by norm_num) hc1
  have hb₂₀ : herm σ b₀ b₂ = 0 := herm_eq_zero_comm σ hσ.invol hb₀2
  set P : (Fin 3 → F) →ₗ[F] (Fin 3 → F) :=
    LinearMap.id - (hermL σ b₀).smulRight b₀ - (hermL σ b₂).smulRight b₂ with hPdef
  have hPy : ∀ y, P y = y - herm σ b₀ y • b₀ - herm σ b₂ y • b₂ := fun y => rfl
  obtain ⟨y, hy⟩ := exists_aniso_of_lt hσ (k := 2) (by omega) ![b₀, b₂] P
    (fun y => by
      rw [hPy, show y - (y - herm σ b₀ y • b₀ - herm σ b₂ y • b₂) =
        herm σ b₀ y • b₀ + herm σ b₂ y • b₂ by abel]
      exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
        (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩)))
    (fun y j => by
      fin_cases j <;> simp [hPy, hb₀1, hc1, hb₀2, hb₂₀])
  obtain ⟨c', hc'⟩ := exists_smul_norm_one hσ hy
  set b₁ : Fin 3 → F := c' • P y with hb₁
  have hb₁1 : herm σ b₁ b₁ = 1 := hc'
  have hb₀₁ : herm σ b₀ b₁ = 0 := by simp [hb₁, hPy, hb₀1, hb₂₀]
  have hb₂₁ : herm σ b₂ b₁ = 0 := by simp [hb₁, hPy, hb₀2, hc1]
  have hb₁₀ : herm σ b₁ b₀ = 0 := herm_eq_zero_comm σ hσ.invol hb₀₁
  have hb₁₂ : herm σ b₁ b₂ = 0 := herm_eq_zero_comm σ hσ.invol hb₂₁
  have hb₀W : b₀ ∈ W := hperp b₀ hb₀2
  have hb₁W : b₁ ∈ W := hperp b₁ hb₂₁
  have horn : ∀ i j, herm σ (![b₀, b₁, b₂] i) (![b₀, b₁, b₂] j) = if i = j then 1 else 0 := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [hb₀1, hb₁1, hc1, hb₀₁, hb₁₀, hb₀2, hb₂₀, hb₂₁, hb₁₂]
  have hli : LinearIndependent F ![b₀, b₁, b₂] := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have h := congrArg (fun z => herm σ (![b₀, b₁, b₂] i) z) hg
    simp only [Fin.sum_univ_three, herm_add_right, herm_smul_right, herm_zero_right] at h
    rw [horn i 0, horn i 1, horn i 2] at h
    fin_cases i <;> simpa using h
  let b : Module.Basis (Fin 3) F (Fin 3 → F) :=
    basisOfLinearIndependentOfCardEqFinrank hli (by simp)
  have hbv : ⇑b = ![b₀, b₁, b₂] := coe_basisOfLinearIndependentOfCardEqFinrank hli _
  have hb0 : b 0 = b₀ := by rw [hbv]; rfl
  have hb1 : b 1 = b₁ := by rw [hbv]; rfl
  have hb2 : b 2 = b₂ := by rw [hbv]; rfl
  refine ⟨b, fun i j => by rw [hbv]; exact horn i j, ?_, ?_⟩
  · refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
    · exact Submodule.span_le.mpr (by
        rintro z (rfl | rfl)
        · exact hb0 ▸ hb₀W
        · exact hb1 ▸ hb₁W)
    · rw [finrank_span_pair_basis b, hW]
  · refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
    · exact Submodule.span_le.mpr (by simpa [hb2] using hb₂ℓ)
    · rw [finrank_span_singleton (b.ne_zero 2), hℓ]

theorem card_ublkGroup (hσ : IsUnitaryInvolution σ) (hc : IsCompl W ℓ)
    (hW : Module.finrank F W = 2) (horth : ∀ w ∈ W, ∀ u ∈ ℓ, herm σ w u = 0) :
    Nat.card (ublkGroup σ W ℓ) = Nat.card (SUid σ 2) := by
  obtain ⟨b, hb, hbW, hbℓ⟩ := exists_orthonormal_adapted hσ hc hW horth
  obtain ⟨c, h1, -⟩ := exists_conj_of_orthonormal σ b hb
  rw [hbW, hbℓ] at h1
  rw [← h1, Subgroup.card_map_of_injective (MulAut.conj c⁻¹).injective]
  exact (Nat.card_congr (MonoidHom.ofInjective (embSUid_injective σ 2)).toEquiv).symm

private theorem conjTr_conjTr_of_invol (hinv : ∀ c, σ (σ c) = c) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) F) : conjTr σ (conjTr σ A) = A := by
  ext i j
  simp [conjTr, hinv]

private theorem det_conjTr_eq {n : ℕ} (A : Matrix (Fin n) (Fin n) F) :
    (conjTr σ A).det = σ A.det := by
  rw [conjTr, Matrix.det_transpose]
  exact (RingHom.map_det σ.toRingHom A).symm

theorem exists_su_diag_of_orthonormal (hσ : IsUnitaryInvolution σ) (b : Fin 3 → Fin 3 → F)
    (hb : ∀ i j, herm σ (b i) (b j) = if i = j then 1 else 0) {a : F} (ha : σ a * a = 1) :
    ∃ g : SUid σ 3, ∀ i, ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ b i =
      (![a, a⁻¹, 1] i) • b i := by
  set Q : Matrix (Fin 3) (Fin 3) F := Matrix.of fun i j => b j i with hQ
  have hQQ : conjTr σ Q * Q = 1 := by
    ext i j
    have := hb i j
    simpa [Matrix.mul_apply, conjTr, herm, Matrix.one_apply, hQ] using this
  have hQQ' : Q * conjTr σ Q = 1 := mul_eq_one_comm.mp hQQ
  have hd : σ Q.det * Q.det = 1 := by
    have h1 := congrArg Matrix.det hQQ
    rw [Matrix.det_mul, Matrix.det_one, det_conjTr_eq] at h1
    exact h1
  have ha0 : a ≠ 0 := by
    rintro rfl
    simp at ha
  set s : Fin 3 → F := ![a, a⁻¹, 1] with hs
  have hss : ∀ j, σ (s j) * s j = 1 := by
    intro j
    fin_cases j
    · simpa [hs] using ha
    · simp only [hs]
      simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero, map_inv₀]
      rw [← mul_inv, ha, inv_one]
    · simp [hs]
  set D : Matrix (Fin 3) (Fin 3) F := Matrix.diagonal s with hD
  have hDD : conjTr σ D * D = 1 := by
    rw [hD, conjTr_diagonal, Matrix.diagonal_mul_diagonal]
    simp_rw [hss]
    exact Matrix.diagonal_one
  set M : Matrix (Fin 3) (Fin 3) F := Q * D * conjTr σ Q with hMdef
  have hM : conjTr σ M * M = 1 := by
    have e : conjTr σ M * M = Q * (conjTr σ D * (conjTr σ Q * Q) * D) * conjTr σ Q := by
      rw [hMdef, conjTr_mul, conjTr_mul, conjTr_conjTr_of_invol hσ.invol]
      simp only [Matrix.mul_assoc]
    rw [e, hQQ, Matrix.mul_one, hDD, Matrix.mul_one, hQQ']
  have hdetM : M.det = 1 := by
    rw [hMdef, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, det_conjTr_eq,
      Fin.prod_univ_three]
    simp only [hs, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    calc Q.det * (a * a⁻¹ * 1) * σ Q.det = σ Q.det * Q.det := by
          rw [mul_inv_cancel₀ ha0]; ring
      _ = 1 := hd
  have hiso : ∀ x y, herm σ (M *ᵥ x) (M *ᵥ y) = herm σ x y := fun x y => by
    rw [herm_mulVec, hM, one_mulVec]
  have hbQ : ∀ i, b i = Q *ᵥ Pi.single i 1 := by
    intro i
    funext k
    simp [hQ]
  have hMQ : M * Q = Q * D := by
    rw [hMdef, Matrix.mul_assoc, hQQ, Matrix.mul_one]
  refine ⟨mkSU σ M hdetM hiso, fun i => ?_⟩
  change M *ᵥ b i = s i • b i
  rw [hbQ i, Matrix.mulVec_mulVec, hMQ, ← Matrix.mulVec_mulVec]
  have hDe : D *ᵥ Pi.single i 1 = s i • Pi.single i 1 := by
    funext k
    by_cases hk : k = i
    · subst hk
      simp [hD]
    · simp [hD, hk]
  rw [hDe, Matrix.mulVec_smul]

theorem fixed_space_ublk (hσ : IsUnitaryInvolution σ) (hc : IsCompl W ℓ)
    (hW : Module.finrank F W = 2) (horth : ∀ w ∈ W, ∀ u ∈ ℓ, herm σ w u = 0)
    {x : Fin 3 → F}
    (hx : ∀ g ∈ ublkGroup σ W ℓ,
      ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ x = x) : x ∈ ℓ := by
  obtain ⟨b, hb, hbW, hbℓ⟩ := exists_orthonormal_adapted hσ hc hW horth
  obtain ⟨a, ha, ha1⟩ := hσ.exists_norm_one_ne_one
  obtain ⟨g, hg⟩ := exists_su_diag_of_orthonormal hσ ⇑b hb ha
  have hmem : g ∈ ublkGroup σ W ℓ := by
    rw [← hbW, ← hbℓ]
    refine ⟨fun v hv => ?_, fun v => ?_⟩
    · obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hv
      rw [Matrix.mulVec_smul, hg 2]
      simp
    · rw [mem_span_pair_iff_repr, mem_span_pair_iff_repr,
        repr_mulVec_of_eigen b ![a, a⁻¹, 1] _ hg v 2]
      simp
  have hfix := hx g hmem
  rw [← hbℓ, mem_span_single_iff_repr]
  have key : ∀ i, (![a, a⁻¹, 1] i) * b.repr x i = b.repr x i := fun i => by
    have := congrArg (fun z => b.repr z i) hfix
    simpa [repr_mulVec_of_eigen b ![a, a⁻¹, 1] _ hg x i] using this
  constructor
  · have h0 := key 0
    simp only [Matrix.cons_val_zero] at h0
    have : (a - 1) * b.repr x 0 = 0 := by linear_combination h0
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr ha1)
  · have h1 := key 1
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero] at h1
    have : (a⁻¹ - 1) * b.repr x 1 = 0 := by linear_combination h1
    refine (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr fun h => ha1 ?_)
    exact inv_eq_one.mp h

theorem normalizer_ublk (hσ : IsUnitaryInvolution σ) (hc : IsCompl W ℓ)
    (hW : Module.finrank F W = 2) (horth : ∀ w ∈ W, ∀ u ∈ ℓ, herm σ w u = 0)
    {M : Matrix (Fin 3) (Fin 3) F} (hM : conjTr σ M * M = 1)
    (h2 : ∀ g ∈ ublkGroup σ W ℓ, ∃ g' ∈ ublkGroup σ W ℓ,
      ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * M =
        M * ((g' : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) :
    (∀ v ∈ ℓ, M *ᵥ v ∈ ℓ) ∧ (∀ v ∈ W, M *ᵥ v ∈ W) := by
  have hℓM : ∀ u ∈ ℓ, M *ᵥ u ∈ ℓ := by
    intro u hu
    refine fixed_space_ublk hσ hc hW horth fun g hg => ?_
    obtain ⟨g', hg', hgg⟩ := h2 g hg
    rw [Matrix.mulVec_mulVec, hgg, ← Matrix.mulVec_mulVec, hg'.1 u hu]
  refine ⟨hℓM, ?_⟩
  have hℓ : Module.finrank F ℓ = 1 := finrank_line_of_compl hc hW
  obtain ⟨u₀, hu₀, hu₀0⟩ := exists_ne_zero_of_finrank_one hℓ
  have hℓu := line_eq_span hℓ hu₀ hu₀0
  have hd : herm σ u₀ u₀ ≠ 0 := herm_ne_zero_of_mem_line hσ hc hW horth hu₀ hu₀0
  obtain ⟨c, hcu⟩ : ∃ c : F, c • u₀ = M *ᵥ u₀ := by
    have := hℓM u₀ hu₀
    rw [hℓu] at this
    exact Submodule.mem_span_singleton.mp this
  have hinj : ∀ x, M *ᵥ x = 0 → x = 0 := fun x hx => by
    have := congrArg (fun z => (conjTr σ M) *ᵥ z) hx
    simpa [Matrix.mulVec_mulVec, hM] using this
  have hc0 : c ≠ 0 := by
    intro h0
    apply hu₀0
    apply hinj
    rw [← hcu, h0, zero_smul]
  intro w hw
  have hMw : M *ᵥ w ∈ W ⊔ ℓ := by rw [hc.sup_eq_top]; exact Submodule.mem_top
  obtain ⟨w', hw', u, hu, hsum⟩ := Submodule.mem_sup.mp hMw
  have h1 : herm σ (M *ᵥ w) (M *ᵥ u₀) = herm σ w u₀ := by
    rw [herm_mulVec, hM, one_mulVec]
  rw [horth w hw u₀ hu₀, ← hcu, herm_smul_right] at h1
  have h3 : herm σ (M *ᵥ w) u₀ = 0 := (mul_eq_zero.mp h1).resolve_left hc0
  rw [← hsum, herm_add_left, horth w' hw' u₀ hu₀] at h3
  rw [hℓu] at hu
  obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hu
  rw [zero_add, herm_smul_left] at h3
  have ht : σ t = 0 := (mul_eq_zero.mp h3).resolve_right hd
  have ht0 : t = 0 := (map_eq_zero_iff σ σ.injective).mp ht
  rw [← hsum, ht0, zero_smul, add_zero]
  exact hw'

theorem exists_orthonormal_of_orthogonal (hσ : IsUnitaryInvolution σ)
    (b : Module.Basis (Fin 3) F (Fin 3 → F)) (hb : ∀ i j, i ≠ j → herm σ (b i) (b j) = 0) :
    ∃ b' : Module.Basis (Fin 3) F (Fin 3 → F),
      (∀ i j, herm σ (b' i) (b' j) = if i = j then 1 else 0) ∧
        ∀ i, ∃ c : F, c ≠ 0 ∧ b' i = c • b i := by
  have hne : ∀ i, herm σ (b i) (b i) ≠ 0 := by
    intro i h0
    apply b.ne_zero i
    apply eq_zero_of_herm σ
    intro y
    have hbij : ∀ j, herm σ (b i) (b j) = 0 := fun j => by
      by_cases hij : i = j
      · subst hij
        exact h0
      · exact hb i j hij
    have hexp : y = ∑ j, b.repr y j • b j := (b.sum_repr y).symm
    conv_lhs => rw [hexp]
    simp only [Fin.sum_univ_three, herm_add_right, herm_smul_right, hbij, mul_zero, add_zero]
  choose c hc using fun i => exists_smul_norm_one hσ (hne i)
  have hc0 : ∀ i, c i ≠ 0 := fun i h0 => by
    have h := hc i
    rw [h0, zero_smul, herm_zero_left] at h
    exact zero_ne_one h
  refine ⟨b.unitsSMul (fun i => Units.mk0 (c i) (hc0 i)), ?_, fun i => ⟨c i, hc0 i, ?_⟩⟩
  · intro i j
    simp only [Module.Basis.unitsSMul_apply, Units.smul_def, Units.val_mk0]
    by_cases hij : i = j
    · subst hij
      simpa using hc i
    · simp [hij, hb i j hij]
  · simp [Module.Basis.unitsSMul_apply]

end CFSG.RankThree.PartOne.CTP
