module

public import CFSG.RankThree.SubgroupLists.PointLocalSL2

public section

namespace CFSG.RankThree.SubgroupLists

open Matrix CFSG.Assembly.LowTwoRank Module
open scoped MatrixGroups

local notation "V₄" => Fin 2 ⊕ Fin 2

variable {K : Type} [Field K]

@[expose] def IsSqZero (x : GL V₄ K) : Prop :=
  ((x : Matrix V₄ V₄ K) - 1) * ((x : Matrix V₄ V₄ K) - 1) = 0

@[expose] noncomputable def unipAxis (x : GL V₄ K) : Submodule K (V₄ → K) :=
  LinearMap.ker (Matrix.toLin' ((x : Matrix V₄ V₄ K) - 1))

theorem mem_unipAxis {x : GL V₄ K} {v : V₄ → K} :
    v ∈ unipAxis x ↔ (x : Matrix V₄ V₄ K) *ᵥ v = v := by
  rw [unipAxis, LinearMap.mem_ker, Matrix.toLin'_apply, Matrix.sub_mulVec, Matrix.one_mulVec,
    sub_eq_zero]

theorem sq_eq_of_isSqZero {x : GL V₄ K} (hx : IsSqZero x) :
    (x : Matrix V₄ V₄ K) * x = 2 • (x : Matrix V₄ V₄ K) - 1 := by
  have h := hx
  rw [IsSqZero] at h
  have : (x : Matrix V₄ V₄ K) * x - 2 • (x : Matrix V₄ V₄ K) + 1 = 0 := by
    rw [← h]; noncomm_ring
  calc (x : Matrix V₄ V₄ K) * x
      = ((x : Matrix V₄ V₄ K) * x - 2 • (x : Matrix V₄ V₄ K) + 1) +
          (2 • (x : Matrix V₄ V₄ K) - 1) := by abel
    _ = 2 • (x : Matrix V₄ V₄ K) - 1 := by rw [this, zero_add]

theorem sub_mem_unipAxis {x : GL V₄ K} (hx : IsSqZero x) (v : V₄ → K) :
    (x : Matrix V₄ V₄ K) *ᵥ v - v ∈ unipAxis x := by
  rw [unipAxis, LinearMap.mem_ker, Matrix.toLin'_apply,
    show (x : Matrix V₄ V₄ K) *ᵥ v - v = ((x : Matrix V₄ V₄ K) - 1) *ᵥ v by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec],
    Matrix.mulVec_mulVec, hx, Matrix.zero_mulVec]

theorem spForm_eq_zero_of_mem_unipAxis {x : GL V₄ K} (hxS : x ∈ StatedSp 2 K) (hx : IsSqZero x)
    (h2 : finrank K (unipAxis x) = 2) {u v : V₄ → K} (hu : u ∈ unipAxis x)
    (hv : v ∈ unipAxis x) : spForm 2 K u v = 0 := by
  set N := Matrix.toLin' ((x : Matrix V₄ V₄ K) - 1) with hN
  have hle : LinearMap.range N ≤ unipAxis x := by
    rintro _ ⟨w, rfl⟩
    rw [hN, Matrix.toLin'_apply, Matrix.sub_mulVec, Matrix.one_mulVec]
    exact sub_mem_unipAxis hx w
  have hrank := LinearMap.finrank_range_add_finrank_ker N
  rw [show finrank K (LinearMap.ker N) = 2 from h2, Module.finrank_fintype_fun_eq_card] at hrank
  simp only [Fintype.card_sum, Fintype.card_fin] at hrank
  have heq : LinearMap.range N = unipAxis x :=
    Submodule.eq_of_le_of_finrank_eq hle (by rw [h2]; omega)
  rw [← heq] at hu
  obtain ⟨w, rfl⟩ := hu
  rw [hN, Matrix.toLin'_apply, Matrix.sub_mulVec, Matrix.one_mulVec, map_sub,
    LinearMap.sub_apply]
  have hxv := mem_unipAxis.mp hv
  have e : spForm 2 K ((x : Matrix V₄ V₄ K) *ᵥ w) v = spForm 2 K w v := by
    conv_lhs => rw [← hxv]
    exact spForm_mulVec hxS w v
  rw [e, sub_self]

theorem isSqZero_conj {x : GL V₄ K} (hx : IsSqZero x) (h : GL V₄ K) :
    IsSqZero (h * x * h⁻¹) := by
  have hh : ((h⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) * h = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hh' : (h : Matrix V₄ V₄ K) * ((h⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have e : ((h * x * h⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) - 1 =
      (h : Matrix V₄ V₄ K) * ((x : Matrix V₄ V₄ K) - 1) * ((h⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) := by
    rw [Units.val_mul, Units.val_mul]
    calc (h : Matrix V₄ V₄ K) * x * ((h⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) - 1
        = (h : Matrix V₄ V₄ K) * x * ((h⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) -
            (h : Matrix V₄ V₄ K) * ((h⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) := by rw [hh']
      _ = (h : Matrix V₄ V₄ K) * ((x : Matrix V₄ V₄ K) - 1) *
            ((h⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) := by noncomm_ring
  rw [IsSqZero, e]
  calc (h : Matrix V₄ V₄ K) * ((x : Matrix V₄ V₄ K) - 1) * ((h⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) *
        ((h : Matrix V₄ V₄ K) * ((x : Matrix V₄ V₄ K) - 1) * ((h⁻¹ : GL V₄ K) : Matrix V₄ V₄ K))
      = (h : Matrix V₄ V₄ K) * ((x : Matrix V₄ V₄ K) - 1) *
          (((h⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) * h) * ((x : Matrix V₄ V₄ K) - 1) *
          ((h⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) := by simp only [Matrix.mul_assoc]
    _ = 0 := by
      rw [hh, Matrix.mul_one, Matrix.mul_assoc (h : Matrix V₄ V₄ K), hx, Matrix.mul_zero,
        Matrix.zero_mul]

theorem mem_unipAxis_conj {x h : GL V₄ K} {v : V₄ → K} :
    (h : Matrix V₄ V₄ K) *ᵥ v ∈ unipAxis (h * x * h⁻¹) ↔ v ∈ unipAxis x := by
  rw [mem_unipAxis, mem_unipAxis, gl_mulVec_mul, gl_mulVec_mul, gl_inv_mulVec_mulVec]
  constructor
  · intro h'
    have := congrArg (fun w => ((h⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) *ᵥ w) h'
    simpa only [gl_inv_mulVec_mulVec] using this
  · intro h'
    rw [h']

@[expose] def projE (v : V₄ → K) : Fin 2 → K := ![v (Sum.inl 1), v (Sum.inr 1)]

theorem spBlock_sub_one_sq {x : GL V₄ K} (hxS : x ∈ StatedSp 2 K) (hx : IsSqZero x)
    (hxe : (x : Matrix V₄ V₄ K) *ᵥ spE = spE) :
    (spBlock (x : Matrix V₄ V₄ K) - 1) * (spBlock (x : Matrix V₄ V₄ K) - 1) = 0 := by
  have hxe' : (x : Matrix V₄ V₄ K) *ᵥ spE = (1 : K) • spE := by rw [one_smul]; exact hxe
  have hmul := spBlock_mul hxS hxe' hxe'
  rw [Units.val_mul, sq_eq_of_isSqZero hx] at hmul
  have h2x : spBlock (2 • (x : Matrix V₄ V₄ K) - 1) = 2 • spBlock (x : Matrix V₄ V₄ K) - 1 := by
    rw [two_smul, two_smul]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [spBlock]
  rw [h2x] at hmul
  calc (spBlock (x : Matrix V₄ V₄ K) - 1) * (spBlock (x : Matrix V₄ V₄ K) - 1)
      = spBlock (x : Matrix V₄ V₄ K) * spBlock (x : Matrix V₄ V₄ K) -
          (2 • spBlock (x : Matrix V₄ V₄ K) - 1) := by noncomm_ring
    _ = 0 := by rw [← hmul, sub_self]

theorem pow_eq_of_sub_one_sq {b : Matrix (Fin 2) (Fin 2) K} (hb : (b - 1) * (b - 1) = 0)
    (n : ℕ) : b ^ n = 1 + (n : K) • (b - 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih]
    have : (1 + (n : K) • (b - 1)) * b =
        1 + ((n : K) + 1) • (b - 1) + (n : K) • ((b - 1) * (b - 1)) := by
      simp only [Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.mul_sub, Matrix.mul_one,
        Matrix.sub_mul, add_smul, one_smul, smul_sub]
      abel
    rw [this, hb, smul_zero, add_zero, Nat.cast_succ]

variable (h2 : (2 : K) ≠ 0)
include h2

omit h2 in
theorem projE_mem_of_mem_unipAxis {x : GL V₄ K} (hxS : x ∈ StatedSp 2 K) (hx : IsSqZero x)
    (hx2 : finrank K (unipAxis x) = 2) (he : spE ∈ unipAxis x) {v : V₄ → K}
    (hv : v ∈ unipAxis x) :
    v (Sum.inr 0) = 0 ∧ spBlock (x : Matrix V₄ V₄ K) *ᵥ projE v = projE v := by
  have hv0 : v (Sum.inr 0) = 0 := by
    rw [← spForm_spE_left v]
    exact spForm_eq_zero_of_mem_unipAxis hxS hx hx2 he hv
  have hxe : (x : Matrix V₄ V₄ K) *ᵥ spE = (1 : K) • spE := by
    rw [one_smul]; exact mem_unipAxis.mp he
  have hxv := mem_unipAxis.mp hv
  refine ⟨hv0, ?_⟩
  have e1 := mulVec_inl_one_of_lineStab hxe hv0
  have e3 := mulVec_inr_one_of_lineStab hxe hv0
  rw [hxv] at e1 e3
  ext i
  fin_cases i
  · simp [projE, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    exact e1.symm
  · simp [projE, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    exact e3.symm

omit h2 in
theorem mem_span_of_mulVec_eq_zero {N : Matrix (Fin 2) (Fin 2) K} (hN0 : N ≠ 0)
    {u w : Fin 2 → K} (hu : N *ᵥ u = 0) (hu0 : u ≠ 0) (hw : N *ᵥ w = 0) :
    w ∈ K ∙ u := by
  have hker : LinearMap.ker (Matrix.toLin' N) = K ∙ u := by
    symm
    apply Submodule.eq_of_le_of_finrank_le
    · rw [Submodule.span_singleton_le_iff_mem, LinearMap.mem_ker, Matrix.toLin'_apply]
      exact hu
    · rw [finrank_span_singleton hu0]
      have h := LinearMap.finrank_range_add_finrank_ker (Matrix.toLin' N)
      rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h
      have hr : 0 < finrank K (LinearMap.range (Matrix.toLin' N)) := by
        rw [Module.finrank_pos_iff_exists_ne_zero]
        by_contra hcon
        push Not at hcon
        apply hN0
        apply Matrix.toLin'.injective
        refine LinearMap.ext fun v => ?_
        have := hcon ⟨Matrix.toLin' N v, ⟨v, rfl⟩⟩
        rw [map_zero, LinearMap.zero_apply]
        exact congrArg Subtype.val this
      omega
  rw [← hker, LinearMap.mem_ker, Matrix.toLin'_apply]
  exact hw

omit h2 in
theorem mem_span_of_linear_eq_zero {α β : K} (hαβ : α ≠ 0 ∨ β ≠ 0) {u w : Fin 2 → K}
    (hu : α * u 0 + β * u 1 = 0) (hu0 : u ≠ 0) (hw : α * w 0 + β * w 1 = 0) :
    w ∈ K ∙ u := by
  refine mem_span_of_mulVec_eq_zero (N := !![α, β; 0, 0]) ?_ ?_ hu0 ?_
  · intro h
    have h1 := congrFun (congrFun h 0) 0
    have h2' := congrFun (congrFun h 0) 1
    simp at h1 h2'
    rcases hαβ with h' | h'
    · exact h' h1
    · exact h' h2'
  · ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, hu]
  · ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, hw]

omit h2 in
theorem finrank_hyperplane_spE :
    finrank K (LinearMap.ker (LinearMap.proj (Sum.inr 0) : (V₄ → K) →ₗ[K] K)) = 3 := by
  have h := LinearMap.finrank_range_add_finrank_ker
    (LinearMap.proj (Sum.inr 0) : (V₄ → K) →ₗ[K] K)
  have hr : LinearMap.range (LinearMap.proj (Sum.inr 0) : (V₄ → K) →ₗ[K] K) = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro c
    exact ⟨fun _ => c, rfl⟩
  rw [hr, finrank_top, Module.finrank_self, Module.finrank_fintype_fun_eq_card] at h
  simp only [Fintype.card_sum, Fintype.card_fin] at h
  omega

omit h2 in
theorem exists_projE_ne_zero {A : Submodule K (V₄ → K)} (hA : finrank K A = 2)
    (hAe : ∀ v ∈ A, v (Sum.inr 0) = 0) : ∃ w ∈ A, projE w ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have hle : A ≤ K ∙ spE := by
    intro v hv
    rw [Submodule.mem_span_singleton]
    refine ⟨v (Sum.inl 0), ?_⟩
    have h0 := hcon v hv
    have h1 := congrFun h0 0
    have h3 := congrFun h0 1
    simp [projE] at h1 h3
    ext i
    rcases i with i | i <;> fin_cases i <;> simp [spE, h1, h3, hAe v hv]
  have := Submodule.finrank_mono hle
  rw [hA, finrank_span_singleton (spE_ne_zero (K := K))] at this
  omega

omit h2 in
theorem projE_not_mem_span {A₁ A₂ : Submodule K (V₄ → K)} (hA : A₁ ⊓ A₂ = K ∙ spE)
    (he : spE ∈ A₁) {w₁ w₂ : V₄ → K} (hw₁ : w₁ ∈ A₁) (hw₂ : w₂ ∈ A₂)
    (hw₁0 : w₁ (Sum.inr 0) = 0) (hw₂0 : w₂ (Sum.inr 0) = 0) (hw₂p : projE w₂ ≠ 0) :
    projE w₂ ∉ K ∙ projE w₁ := by
  intro hmem
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
  have hc1 := congrFun hc 0
  have hc3 := congrFun hc 1
  simp [projE] at hc1 hc3
  have hw₂eq : w₂ = c • w₁ + (w₂ (Sum.inl 0) - c * w₁ (Sum.inl 0)) • spE := by
    ext i
    rcases i with i | i <;> fin_cases i <;> simp [spE, hw₁0, hw₂0, ← hc1, ← hc3]
  have hw₂A₁ : w₂ ∈ A₁ := by
    rw [hw₂eq]
    exact A₁.add_mem (A₁.smul_mem c hw₁) (A₁.smul_mem _ he)
  have : w₂ ∈ A₁ ⊓ A₂ := ⟨hw₂A₁, hw₂⟩
  rw [hA, Submodule.mem_span_singleton] at this
  obtain ⟨d, hd⟩ := this
  apply hw₂p
  rw [← hd]
  ext i
  fin_cases i <;> simp [projE, spE]

omit h2 in
theorem mem_unipAxis_heis_iff (α β γ : K) {v : V₄ → K} (hv : v (Sum.inr 0) = 0) :
    v ∈ unipAxis (heis α β γ) ↔ α * v (Sum.inl 1) + β * v (Sum.inr 1) = 0 := by
  rw [mem_unipAxis, heis_mulVec_of_mem α β γ hv]
  constructor
  · intro h
    have := congrFun h (Sum.inl 0)
    simpa [spE] using this
  · intro h
    rw [h, zero_smul, add_zero]

omit h2 in
theorem heis_ne_of_finrank_unipAxis {x : GL V₄ K} (hx2 : finrank K (unipAxis x) = 2) (γ : K) :
    x ≠ heis 0 0 γ := by
  rintro rfl
  have hle : LinearMap.ker (LinearMap.proj (Sum.inr 0) : (V₄ → K) →ₗ[K] K) ≤
      unipAxis (heis 0 0 γ) := by
    intro v hv
    rw [mem_unipAxis, heis_mulVec]
    have hv0 : v (Sum.inr 0) = 0 := hv
    simp [hv0]
  have := Submodule.finrank_mono hle
  rw [finrank_hyperplane_spE, hx2] at this
  omega

omit h2 in
theorem heis_params_ne_zero {α β γ : K} (hx2 : finrank K (unipAxis (heis α β γ)) = 2) :
    α ≠ 0 ∨ β ≠ 0 := by
  by_contra h
  push Not at h
  obtain ⟨rfl, rfl⟩ := h
  exact heis_ne_of_finrank_unipAxis hx2 γ rfl

theorem heis_comm_iff (α β γ α' β' γ' : K) :
    heis α β γ * heis α' β' γ' = heis α' β' γ' * heis α β γ ↔ α * β' - α' * β = 0 := by
  rw [heis_mul, heis_mul]
  constructor
  · intro h
    have := congrArg (fun g : GL V₄ K => (g : Matrix V₄ V₄ K) (Sum.inl 0) (Sum.inr 0)) h
    simp only [coe_heis, heisMat_inl_zero_inr_zero] at this
    have h' : (2 : K) * (α * β' - α' * β) = 0 := by linear_combination this
    exact (mul_eq_zero.mp h').resolve_left h2
  · intro h
    congr 1
    · ring
    · ring
    · linear_combination 2 * h

theorem exists_spTrans_of_axes_meet_heis {G : Subgroup (GL V₄ K)} (hGS : G ≤ StatedSp 2 K)
    {x y : GL V₄ K} (hxG : x ∈ G) (hyG : y ∈ G) (hx : IsSqZero x) (hy : IsSqZero y)
    (hx2 : finrank K (unipAxis x) = 2) (hy2 : finrank K (unipAxis y) = 2)
    (hxy : unipAxis x ⊓ unipAxis y = K ∙ spE) (hbx : spBlock (x : Matrix V₄ V₄ K) = 1) :
    ∃ a : V₄ → K, ∃ c : K, a ≠ 0 ∧ c ≠ 0 ∧ spTrans a c ∈ G := by
  classical
  have hxS := hGS hxG
  have hyS := hGS hyG
  have hspE : spE ∈ unipAxis x ⊓ unipAxis y := by
    rw [hxy]; exact Submodule.mem_span_singleton_self _
  have hex : spE ∈ unipAxis x := hspE.1
  have hey : spE ∈ unipAxis y := hspE.2
  have hxe : (x : Matrix V₄ V₄ K) *ᵥ spE = spE := mem_unipAxis.mp hex
  have hye : (y : Matrix V₄ V₄ K) *ᵥ spE = spE := mem_unipAxis.mp hey
  have hye' : (y : Matrix V₄ V₄ K) *ᵥ spE = (1 : K) • spE := by rw [one_smul]; exact hye
  have hxheis := eq_heis_of_fix hxS hxe hbx
  set α := (x : Matrix V₄ V₄ K) (Sum.inl 0) (Sum.inl 1) with hα
  set β := (x : Matrix V₄ V₄ K) (Sum.inl 0) (Sum.inr 1) with hβ
  set γ := (x : Matrix V₄ V₄ K) (Sum.inl 0) (Sum.inr 0) with hγ
  have hx2' : finrank K (unipAxis (heis α β γ)) = 2 := by rw [← hxheis]; exact hx2
  have hαβ := heis_params_ne_zero hx2'
  have hax : ∀ v ∈ unipAxis x, v (Sum.inr 0) = 0 :=
    fun v hv => (projE_mem_of_mem_unipAxis hxS hx hx2 hex hv).1
  have hay : ∀ v ∈ unipAxis y, v (Sum.inr 0) = 0 :=
    fun v hv => (projE_mem_of_mem_unipAxis hyS hy hy2 hey hv).1
  obtain ⟨wx, hwx, hwx0⟩ := exists_projE_ne_zero hx2 hax
  obtain ⟨wy, hwy, hwy0⟩ := exists_projE_ne_zero hy2 hay
  have hkey : projE wy ∉ K ∙ projE wx :=
    projE_not_mem_span hxy hex hwx hwy (hax wx hwx) (hay wy hwy) hwy0
  have hkey' : projE wx ∉ K ∙ projE wy :=
    projE_not_mem_span (by rw [inf_comm]; exact hxy) hey hwy hwx (hay wy hwy) (hax wx hwx) hwx0
  have hxeq : α * projE wx 0 + β * projE wx 1 = 0 := by
    have := (mem_unipAxis_heis_iff α β γ (hax wx hwx)).mp (hxheis ▸ hwx)
    simpa [projE] using this
  have hxH : IsHeisAt spE x := by rw [hxheis]; exact isHeisAt_heis α β γ
  by_cases hby : spBlock (y : Matrix V₄ V₄ K) = 1
  ·
    have hyheis := eq_heis_of_fix hyS hye hby
    set α' := (y : Matrix V₄ V₄ K) (Sum.inl 0) (Sum.inl 1) with hα'
    set β' := (y : Matrix V₄ V₄ K) (Sum.inl 0) (Sum.inr 1) with hβ'
    set γ' := (y : Matrix V₄ V₄ K) (Sum.inl 0) (Sum.inr 0) with hγ'
    have hy2' : finrank K (unipAxis (heis α' β' γ')) = 2 := by rw [← hyheis]; exact hy2
    have hα'β' := heis_params_ne_zero hy2'
    have hyeq : α' * projE wy 0 + β' * projE wy 1 = 0 := by
      have := (mem_unipAxis_heis_iff α' β' γ' (hay wy hwy)).mp (hyheis ▸ hwy)
      simpa [projE] using this
    have hnc : x * y ≠ y * x := by
      intro hc
      rw [hxheis, hyheis, heis_comm_iff h2] at hc
      apply hkey
      refine mem_span_of_linear_eq_zero hαβ hxeq hwx0 ?_
      rcases hα'β' with h' | h'
      · by_cases hαz : α = 0
        · have hβz : β ≠ 0 := hαβ.resolve_left (not_not.mpr hαz)
          have : α' = 0 := by
            have := hc; rw [hαz] at this
            have h0 : α' * β = 0 := by linear_combination -this
            exact (mul_eq_zero.mp h0).resolve_right hβz
          exact absurd this h'
        · have : α * (α' * projE wy 0 + β' * projE wy 1) =
              α' * (α * projE wy 0 + β * projE wy 1) := by
            linear_combination projE wy 1 * hc
          rw [hyeq, mul_zero] at this
          exact (mul_eq_zero.mp this.symm).resolve_left h'
      · by_cases hβz : β = 0
        · have hαz : α ≠ 0 := hαβ.resolve_right (not_not.mpr hβz)
          have : β' = 0 := by
            have := hc; rw [hβz] at this
            have h0 : α * β' = 0 := by linear_combination this
            exact (mul_eq_zero.mp h0).resolve_left hαz
          exact absurd this h'
        · have : β * (α' * projE wy 0 + β' * projE wy 1) =
              β' * (α * projE wy 0 + β * projE wy 1) := by
            linear_combination -(projE wy 0) * hc
          rw [hyeq, mul_zero] at this
          exact (mul_eq_zero.mp this.symm).resolve_left h'
    have hyH : IsHeisAt spE y := by rw [hyheis]; exact isHeisAt_heis α' β' γ'
    obtain ⟨c, hc0, hc⟩ := exists_commutator_eq_spTrans h2 spE_ne_zero hxH hyH hnc
    exact ⟨spE, c, spE_ne_zero, hc0, hc ▸
      G.mul_mem (G.mul_mem (G.mul_mem hxG hyG) (G.inv_mem hxG)) (G.inv_mem hyG)⟩
  ·
    have hzG : y * x * y⁻¹ ∈ G := G.mul_mem (G.mul_mem hyG hxG) (G.inv_mem hyG)
    have hzH : IsHeisAt spE (y * x * y⁻¹) := by
      have := hxH.conj hyS
      rwa [hye] at this
    obtain ⟨α', β', γ', hzheis⟩ := exists_eq_heis_of_isHeisAt hzH
    have hyie : ((y⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) *ᵥ spE = (1 : K) • spE := by
      rw [one_smul]
      conv_lhs => rw [← hye]
      rw [gl_inv_mulVec_mulVec]
    have hrel : ∀ v : V₄ → K, v (Sum.inr 0) = 0 →
        α' * v (Sum.inl 1) + β' * v (Sum.inr 1) =
          α * (((y⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) *ᵥ v) (Sum.inl 1) +
            β * (((y⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) *ᵥ v) (Sum.inr 1) := by
      intro v hv
      have e1 := heis_conj_param hyS hye' hyie α β γ hv
      have e2 := heis_mulVec_of_mem α' β' γ' hv
      rw [← hzheis, hxheis, e1] at e2
      have := congrFun e2 (Sum.inl 0)
      simp [spE, -Matrix.coe_units_inv] at this
      linear_combination -this
    have hα'β' : α' ≠ 0 ∨ β' ≠ 0 := by
      by_contra h
      push Not at h
      obtain ⟨h1, h3⟩ := h
      apply hαβ.elim
      · intro hα0
        apply hα0
        have := hrel ((y : Matrix V₄ V₄ K) *ᵥ Pi.single (Sum.inl 1) 1)
          (mulVec_inr_zero_of_lineStab hyS hye' (by simp))
        rw [gl_inv_mulVec_mulVec, h1, h3] at this
        simpa using this.symm
      · intro hβ0
        apply hβ0
        have := hrel ((y : Matrix V₄ V₄ K) *ᵥ Pi.single (Sum.inr 1) 1)
          (mulVec_inr_zero_of_lineStab hyS hye' (by simp))
        rw [gl_inv_mulVec_mulVec, h1, h3] at this
        simpa using this.symm
    have hnc : x * (y * x * y⁻¹) ≠ (y * x * y⁻¹) * x := by
      intro hc
      rw [hzheis] at hc
      conv at hc => rw [hxheis]
      rw [heis_comm_iff h2] at hc
      set u := (y : Matrix V₄ V₄ K) *ᵥ wx with hu
      have hu0 : u (Sum.inr 0) = 0 := mulVec_inr_zero_of_lineStab hyS hye' (hax wx hwx)
      have hu' : α' * u (Sum.inl 1) + β' * u (Sum.inr 1) = 0 := by
        rw [hrel u hu0, hu, gl_inv_mulVec_mulVec]
        simpa [projE] using hxeq
      have hueq : α * projE u 0 + β * projE u 1 = 0 := by
        simp only [projE, Matrix.cons_val_zero, Matrix.cons_val_one]
        rcases hα'β' with h' | h'
        · have : α' * (α * u (Sum.inl 1) + β * u (Sum.inr 1)) = 0 := by
            linear_combination α * hu' - u (Sum.inr 1) * hc
          exact (mul_eq_zero.mp this).resolve_left h'
        · have : β' * (α * u (Sum.inl 1) + β * u (Sum.inr 1)) = 0 := by
            linear_combination β * hu' + u (Sum.inl 1) * hc
          exact (mul_eq_zero.mp this).resolve_left h'
      have hmem := mem_span_of_linear_eq_zero hαβ hxeq hwx0 hueq
      obtain ⟨μ, hμ⟩ := Submodule.mem_span_singleton.mp hmem
      have hblk : projE u = spBlock (y : Matrix V₄ V₄ K) *ᵥ projE wx := by
        have e1 := mulVec_inl_one_of_lineStab hye' (hax wx hwx)
        have e3 := mulVec_inr_one_of_lineStab hye' (hax wx hwx)
        ext i
        fin_cases i
        · simp [projE, Matrix.mulVec, dotProduct, Fin.sum_univ_two, hu, e1]
        · simp [projE, Matrix.mulVec, dotProduct, Fin.sum_univ_two, hu, e3]
      have hsq := spBlock_sub_one_sq hyS hy hye
      have hfix : (spBlock (y : Matrix V₄ V₄ K) - 1) *ᵥ projE wx = 0 := by
        have hev : spBlock (y : Matrix V₄ V₄ K) *ᵥ projE wx = μ • projE wx := by
          rw [← hblk, hμ]
        have h' : (spBlock (y : Matrix V₄ V₄ K) - 1) *ᵥ projE wx = (μ - 1) • projE wx := by
          rw [Matrix.sub_mulVec, hev, Matrix.one_mulVec, sub_smul, one_smul]
        have h'' : ((spBlock (y : Matrix V₄ V₄ K) - 1) * (spBlock (y : Matrix V₄ V₄ K) - 1)) *ᵥ
            projE wx = ((μ - 1) * (μ - 1)) • projE wx := by
          rw [← Matrix.mulVec_mulVec, h', Matrix.mulVec_smul, h', smul_smul]
        rw [hsq, Matrix.zero_mulVec] at h''
        have hμ1 : (μ - 1) * (μ - 1) = 0 := by
          by_contra hne
          exact hwx0 ((smul_eq_zero.mp h''.symm).resolve_left hne)
        have : μ - 1 = 0 := mul_self_eq_zero.mp hμ1
        rw [h', this, zero_smul]
      have hfixy : (spBlock (y : Matrix V₄ V₄ K) - 1) *ᵥ projE wy = 0 := by
        rw [Matrix.sub_mulVec, (projE_mem_of_mem_unipAxis hyS hy hy2 hey hwy).2,
          Matrix.one_mulVec, sub_self]
      exact hkey' (mem_span_of_mulVec_eq_zero (sub_ne_zero.mpr hby) hfixy hwy0 hfix)
    obtain ⟨c, hc0, hc⟩ := exists_commutator_eq_spTrans h2 spE_ne_zero hxH hzH hnc
    exact ⟨spE, c, spE_ne_zero, hc0, hc ▸
      G.mul_mem (G.mul_mem (G.mul_mem hxG hzG) (G.inv_mem hxG)) (G.inv_mem hzG)⟩

omit h2

theorem exists_spTrans_of_axes_meet_spE {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p)
    {G : Subgroup (GL V₄ (ZMod p))} (hGS : G ≤ StatedSp 2 (ZMod p))
    {x y : GL V₄ (ZMod p)} (hxG : x ∈ G) (hyG : y ∈ G) (hx : IsSqZero x) (hy : IsSqZero y)
    (hx2 : finrank (ZMod p) (unipAxis x) = 2) (hy2 : finrank (ZMod p) (unipAxis y) = 2)
    (hxy : unipAxis x ⊓ unipAxis y = (ZMod p) ∙ spE) :
    ∃ a : V₄ → ZMod p, ∃ c : ZMod p, a ≠ 0 ∧ c ≠ 0 ∧ spTrans a c ∈ G := by
  classical
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at this
    have := Nat.le_of_dvd (by norm_num) this
    omega
  by_cases hbx : spBlock (x : Matrix V₄ V₄ (ZMod p)) = 1
  · exact exists_spTrans_of_axes_meet_heis h2 hGS hxG hyG hx hy hx2 hy2 hxy hbx
  by_cases hby : spBlock (y : Matrix V₄ V₄ (ZMod p)) = 1
  · exact exists_spTrans_of_axes_meet_heis h2 hGS hyG hxG hy hx hy2 hx2
      (by rw [inf_comm]; exact hxy) hby
  have hxS := hGS hxG
  have hyS := hGS hyG
  have hspE : spE ∈ unipAxis x ⊓ unipAxis y := by
    rw [hxy]; exact Submodule.mem_span_singleton_self _
  have hex : spE ∈ unipAxis x := hspE.1
  have hey : spE ∈ unipAxis y := hspE.2
  have hxe : (x : Matrix V₄ V₄ (ZMod p)) *ᵥ spE = spE := mem_unipAxis.mp hex
  have hye : (y : Matrix V₄ V₄ (ZMod p)) *ᵥ spE = spE := mem_unipAxis.mp hey
  have hax : ∀ v ∈ unipAxis x, v (Sum.inr 0) = 0 :=
    fun v hv => (projE_mem_of_mem_unipAxis hxS hx hx2 hex hv).1
  have hay : ∀ v ∈ unipAxis y, v (Sum.inr 0) = 0 :=
    fun v hv => (projE_mem_of_mem_unipAxis hyS hy hy2 hey hv).1
  obtain ⟨wx, hwx, hwx0⟩ := exists_projE_ne_zero hx2 hax
  obtain ⟨wy, hwy, hwy0⟩ := exists_projE_ne_zero hy2 hay
  have hkey' : projE wx ∉ (ZMod p) ∙ projE wy :=
    projE_not_mem_span (by rw [inf_comm]; exact hxy) hey hwy hwx (hay wy hwy) (hax wx hwx) hwx0
  have hfixx : (spBlock (x : Matrix V₄ V₄ (ZMod p)) - 1) *ᵥ projE wx = 0 := by
    rw [Matrix.sub_mulVec, (projE_mem_of_mem_unipAxis hxS hx hx2 hex hwx).2,
      Matrix.one_mulVec, sub_self]
  have hfixy : (spBlock (y : Matrix V₄ V₄ (ZMod p)) - 1) *ᵥ projE wy = 0 := by
    rw [Matrix.sub_mulVec, (projE_mem_of_mem_unipAxis hyS hy hy2 hey hwy).2,
      Matrix.one_mulVec, sub_self]
  have hsqx := spBlock_sub_one_sq hxS hx hxe
  have hsqy := spBlock_sub_one_sq hyS hy hye
  have hxe' : (x : Matrix V₄ V₄ (ZMod p)) *ᵥ spE = (1 : ZMod p) • spE := by
    rw [one_smul]; exact hxe
  have hye' : (y : Matrix V₄ V₄ (ZMod p)) *ᵥ spE = (1 : ZMod p) • spE := by
    rw [one_smul]; exact hye
  set gx : lineStabE G := ⟨x, hxG, 1, hxe'⟩
  set gy : lineStabE G := ⟨y, hyG, 1, hye'⟩
  have hpow : ∀ (g : lineStabE G),
      (spBlock ((g : GL V₄ (ZMod p)) : Matrix V₄ V₄ (ZMod p)) - 1) *
        (spBlock ((g : GL V₄ (ZMod p)) : Matrix V₄ V₄ (ZMod p)) - 1) = 0 →
      spBlockHom hGS g ^ p = 1 := by
    intro g hg
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow, coe_spBlockHom, pow_eq_of_sub_one_sq hg,
      ZMod.natCast_self, zero_smul, add_zero]
    rfl
  refine exists_spTrans_mem_of_unipotent_blocks hp5 hGS gx gy (hpow gx hsqx) ?_ (hpow gy hsqy) ?_
  · intro h
    apply hbx
    have := congrArg (fun A : SL(2, ZMod p) => (A : Matrix (Fin 2) (Fin 2) (ZMod p))) h
    simpa [coe_spBlockHom] using this
  · intro hmem
    rw [← mem_powers_iff_mem_zpowers] at hmem
    obtain ⟨n, hn⟩ := hmem
    have hn' := congrArg (fun A : SL(2, ZMod p) => (A : Matrix (Fin 2) (Fin 2) (ZMod p))) hn
    simp only [Matrix.SpecialLinearGroup.coe_pow, coe_spBlockHom] at hn'
    rw [pow_eq_of_sub_one_sq hsqx] at hn'
    have hfix : (spBlock (y : Matrix V₄ V₄ (ZMod p)) - 1) *ᵥ projE wx = 0 := by
      have : spBlock (y : Matrix V₄ V₄ (ZMod p)) - 1 =
          (n : ZMod p) • (spBlock (x : Matrix V₄ V₄ (ZMod p)) - 1) := by
        rw [← hn']; abel
      rw [this, Matrix.smul_mulVec, hfixx, smul_zero]
    exact hkey' (mem_span_of_mulVec_eq_zero (sub_ne_zero.mpr hby) hfixy hwy0 hfix)

theorem exists_spTrans_of_axes_meet {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p)
    {G : Subgroup (GL V₄ (ZMod p))} (hGS : G ≤ StatedSp 2 (ZMod p))
    {x y : GL V₄ (ZMod p)} (hxG : x ∈ G) (hyG : y ∈ G) (hx : IsSqZero x) (hy : IsSqZero y)
    (hx2 : finrank (ZMod p) (unipAxis x) = 2) (hy2 : finrank (ZMod p) (unipAxis y) = 2)
    {z : V₄ → ZMod p} (hz : z ≠ 0) (hxy : unipAxis x ⊓ unipAxis y = (ZMod p) ∙ z) :
    ∃ a : V₄ → ZMod p, ∃ c : ZMod p, a ≠ 0 ∧ c ≠ 0 ∧ spTrans a c ∈ G := by
  obtain ⟨h, hh, hhz⟩ := exists_mem_statedSp_mulVec_eq hz (spE_ne_zero (K := ZMod p))
  set G' : Subgroup (GL V₄ (ZMod p)) := G.map (MulAut.conj h).toMonoidHom with hG'
  have hmem : ∀ g ∈ G, h * g * h⁻¹ ∈ G' := fun g hg => ⟨g, hg, rfl⟩
  have hG'S : G' ≤ StatedSp 2 (ZMod p) := by
    rintro _ ⟨g, hg, rfl⟩
    exact mul_mem (mul_mem hh (hGS hg)) (inv_mem hh)
  have hinj :
      Function.Injective (Matrix.toLin' ((h : GL V₄ (ZMod p)) : Matrix V₄ V₄ (ZMod p))) := by
    intro a b hab
    simp only [Matrix.toLin'_apply] at hab
    rw [← gl_inv_mulVec_mulVec h a, hab, gl_inv_mulVec_mulVec]
  have hax' : ∀ w : GL V₄ (ZMod p), unipAxis (h * w * h⁻¹) = translate h (unipAxis w) := by
    intro w
    ext u
    rw [mem_translate]
    constructor
    · intro hu
      refine ⟨((h⁻¹ : GL V₄ (ZMod p)) : Matrix V₄ V₄ (ZMod p)) *ᵥ u, ?_, gl_mulVec_inv_mulVec h u⟩
      rw [← mem_unipAxis_conj (h := h), gl_mulVec_inv_mulVec]
      exact hu
    · rintro ⟨v, hv, rfl⟩
      exact mem_unipAxis_conj.mpr hv
  have hint : unipAxis (h * x * h⁻¹) ⊓ unipAxis (h * y * h⁻¹) = (ZMod p) ∙ spE := by
    rw [hax', hax', translate, translate, ← Submodule.map_inf _ hinj, hxy,
      Submodule.map_span, Set.image_singleton, Matrix.toLin'_apply, hhz]
  obtain ⟨a, c, ha, hc, hT⟩ := exists_spTrans_of_axes_meet_spE hp5 hG'S (hmem x hxG)
    (hmem y hyG) (isSqZero_conj hx h) (isSqZero_conj hy h)
    (by rw [hax', finrank_translate]; exact hx2) (by rw [hax', finrank_translate]; exact hy2)
    hint
  obtain ⟨g, hg, hgT⟩ := hT
  refine ⟨((h⁻¹ : GL V₄ (ZMod p)) : Matrix V₄ V₄ (ZMod p)) *ᵥ a, c, ?_, hc, ?_⟩
  · intro h0
    apply ha
    rw [← gl_mulVec_inv_mulVec h a, h0, Matrix.mulVec_zero]
  · have key := conj_spTrans (inv_mem hh) a c
    rw [← key]
    have : g = h⁻¹ * spTrans a c * h⁻¹⁻¹ := by
      rw [inv_inv, ← hgT]
      simp [MulAut.conj_apply]
      group
    rw [← this]
    exact hg

end CFSG.RankThree.SubgroupLists
