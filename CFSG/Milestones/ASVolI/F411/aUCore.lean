module

public import CFSG.ClassicalGroups.UnitaryFlag.OrderSylow
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherSemilinearData

public section

namespace CFSG.ASVolI

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

section UCore

variable {p f : ℕ} {K : Type} [Field K]

theorem burnsideF411a_hyp_eq_of_proj_eq (h : UnitaryFieldData p f K) {r ε : ℕ} (hr : 1 ≤ r)
    {g u : hypSU h r ε} (m : ℕ) (hg : g ^ p ^ m = 1) (hu : u ^ p ^ m = 1)
    (hgu : hypProj h r ε g = hypProj h r ε u) : g = u := by
  have : Fact p.Prime := ⟨h.prime⟩
  have : CharP K p := h.charP
  have hz : g⁻¹ * u ∈ hypScalars h r ε := QuotientGroup.eq.mp hgu
  obtain ⟨c, -, -, hc⟩ := hz
  have hcen : ((g⁻¹ * u : hypSU h r ε) : GL (HypIndex r ε) K) ∈
      Subgroup.center (GL (HypIndex r ε) K) := by
    rw [hc, Matrix.GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨c, rfl⟩
  have hcomm : Commute g (g⁻¹ * u) :=
    Subtype.ext (Subgroup.mem_center_iff.mp hcen (g : GL (HypIndex r ε) K))
  have hu' : u = g * (g⁻¹ * u) := by rw [mul_inv_cancel_left]
  have hzN : (g⁻¹ * u) ^ p ^ m = 1 := by
    have h2 := hcomm.mul_pow (p ^ m)
    rw [← hu', hu, hg, one_mul] at h2
    exact h2.symm
  have hcN : Matrix.GeneralLinearGroup.scalar (HypIndex r ε) (c ^ p ^ m) = 1 := by
    rw [map_pow, ← hc, ← Subgroup.coe_pow, hzN, Subgroup.coe_one]
  have hc1 : (c : K) ^ p ^ m = 1 := by
    have h3 := congrArg (fun x : GL (HypIndex r ε) K =>
      (x : Matrix (HypIndex r ε) (HypIndex r ε) K) (Sum.inl ⟨0, hr⟩) (Sum.inl ⟨0, hr⟩)) hcN
    simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply_eq,
      Units.val_one, Matrix.one_apply_eq, Units.val_pow_eq_pow_val] at h3
    exact h3
  have hc2 : c = 1 := by
    have h0 : ((c : K) - 1) ^ p ^ m = 0 := by rw [sub_pow_char_pow, hc1, one_pow, sub_self]
    exact Units.ext
      (sub_eq_zero.mp ((pow_eq_zero_iff (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)).mp h0))
  have hz1 : g⁻¹ * u = 1 := by
    apply Subtype.ext
    rw [hc, hc2, map_one]
    rfl
  rw [hu', hz1, mul_one]

theorem burnsideF411a_isPGroup_hypUnitriangular (h : UnitaryFieldData p f K) {r ε : ℕ}
    (hε : ε ≤ 1) : IsPGroup p (hypUnitriangular h r ε) :=
  IsPGroup.of_card (n := f * ((2 * r + ε) * (2 * r + ε - 1) / 2))
    (by rw [card_hypUnitriangular h hε, pow_mul])

theorem burnsideF411a_hyp_intertwine_aux {ι : Type*} [Fintype ι] [DecidableEq ι] {A : GL ι K}
    {X Y : Matrix ι ι K}
    (h : (A : Matrix ι ι K) * X * ((A⁻¹ : GL ι K) : Matrix ι ι K) = Y) :
    (A : Matrix ι ι K) * X = Y * (A : Matrix ι ι K) := by
  rw [← h, Matrix.mul_assoc _ ((A⁻¹ : GL ι K) : Matrix ι ι K), Units.inv_mul, Matrix.mul_one]

theorem burnsideF411a_hyp_intertwine (h : UnitaryFieldData p f K) {r ε : ℕ} (hr : 1 ≤ r)
    (hε : ε ≤ 1) (α : MulAut (hypPSU h r ε))
    (hα : ∀ x ∈ hypProjUnitriangular h r ε, α x = x) (σ : K ≃+* K) (A : GL (HypIndex r ε) K)
    (hAg : ∀ g : hypSU h r ε, ∃ hg : A * glAut σ (g : GL (HypIndex r ε) K) * A⁻¹ ∈ hypSU h r ε,
      α (hypProj h r ε g) = hypProj h r ε ⟨_, hg⟩)
    (u : hypSU h r ε) (hu : u ∈ hypUnitriangular h r ε) :
    (A : Matrix (HypIndex r ε) (HypIndex r ε) K) *
        ((u : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K).map σ =
      ((u : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) *
        (A : Matrix (HypIndex r ε) (HypIndex r ε) K) := by
  obtain ⟨hg, hαu⟩ := hAg u
  obtain ⟨m, hm⟩ := burnsideF411a_isPGroup_hypUnitriangular h (r := r) hε ⟨u, hu⟩
  have hum : u ^ p ^ m = 1 := by simpa using congrArg Subtype.val hm
  have hgm : (⟨_, hg⟩ : hypSU h r ε) ^ p ^ m = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    show (A * glAut σ (u : GL (HypIndex r ε) K) * A⁻¹) ^ p ^ m = 1
    rw [conj_pow, ← map_pow, ← Subgroup.coe_pow, hum, Subgroup.coe_one, map_one, mul_one,
      mul_inv_cancel]
  have heq : (⟨_, hg⟩ : hypSU h r ε) = u :=
    burnsideF411a_hyp_eq_of_proj_eq h hr m hgm hum
      (by rw [← hαu, hα _ (Subgroup.mem_map_of_mem _ hu)])
  have h1 := congrArg (fun x : hypSU h r ε =>
    ((x : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K)) heq
  simp only [Units.val_mul, coe_glAut] at h1
  exact burnsideF411a_hyp_intertwine_aux h1

theorem burnsideF411a_hyp_det_of_unitri {r ε : ℕ} {M : Matrix (HypIndex r ε) (HypIndex r ε) K}
    (hM : M.BlockTriangular fullPos) (hd : ∀ a, M a a = 1) : M.det = 1 := by
  obtain ⟨hblk, hA, hP, hD⟩ := eq_blk3_of_blockTriangular hM
  rw [hblk, det_blk3, det_of_isUpperTriangular hA, det_of_isUpperTriangular hP,
    det_of_isLowerTriangular _ hD]
  simp [blkA, blkP, blkD, hd]

theorem burnsideF411a_hyp_inner_of_shape (h : UnitaryFieldData p f K) {r ε : ℕ}
    (α : MulAut (hypPSU h r ε)) (σ : K ≃+* K) (hσ : σ = 1) (A : GL (HypIndex r ε) K)
    (hA : ((A : Matrix (HypIndex r ε) (HypIndex r ε) K).map h.bar)ᵀ * hypGram r ε K *
      (A : Matrix (HypIndex r ε) (HypIndex r ε) K) = hypGram r ε K)
    (hAg : ∀ g : hypSU h r ε, ∃ hg : A * glAut σ (g : GL (HypIndex r ε) K) * A⁻¹ ∈ hypSU h r ε,
      α (hypProj h r ε g) = hypProj h r ε ⟨_, hg⟩)
    (a : K) (ha : a ≠ 0) (hBT : (A : Matrix (HypIndex r ε) (HypIndex r ε) K).BlockTriangular fullPos)
    (hdiag : ∀ x, (A : Matrix (HypIndex r ε) (HypIndex r ε) K) x x = a)
    (hna : h.bar a * a = 1) : ∃ g, α = MulAut.conj g := by
  set M := (A : Matrix (HypIndex r ε) (HypIndex r ε) K) with hMdef
  have hiso : ((a⁻¹ • M).map h.bar)ᵀ * hypGram r ε K * (a⁻¹ • M) = hypGram r ε K := by
    have hmap : (a⁻¹ • M).map h.bar = h.bar a⁻¹ • M.map h.bar := by
      ext i j
      simp
    have hna' : a⁻¹ * (h.bar a)⁻¹ = 1 := by
      rw [← mul_inv, mul_comm a, hna, inv_one]
    rw [hmap, transpose_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, hA, smul_smul,
      map_inv₀, hna', one_smul]
  have hdet : (a⁻¹ • M).det = 1 := by
    refine burnsideF411a_hyp_det_of_unitri (fun i j hij => ?_) fun x => ?_
    · rw [Matrix.smul_apply, hBT hij, smul_zero]
    · rw [Matrix.smul_apply, hdiag x, smul_eq_mul, inv_mul_cancel₀ ha]
  set u' : hypSU h r ε := mkHypSU h (a⁻¹ • M) hiso hdet with hu'
  have hAu : A = Matrix.GeneralLinearGroup.scalar (HypIndex r ε) (Units.mk0 a ha) *
      (u' : GL (HypIndex r ε) K) := by
    apply Units.ext
    rw [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, hu', coe_mkHypSU, Units.val_mk0,
      Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul, smul_smul, mul_inv_cancel₀ ha, one_smul]
  have hscent : Matrix.GeneralLinearGroup.scalar (HypIndex r ε) (Units.mk0 a ha) ∈
      Subgroup.center (GL (HypIndex r ε) K) := by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨_, rfl⟩
  refine ⟨hypProj h r ε u', ?_⟩
  ext x
  obtain ⟨g, rfl⟩ := hypProj_surjective h r ε x
  obtain ⟨hg, hαg⟩ := hAg g
  rw [hαg, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  show A * glAut σ (g : GL (HypIndex r ε) K) * A⁻¹ = (u' : GL (HypIndex r ε) K) *
    (g : GL (HypIndex r ε) K) * (u' : GL (HypIndex r ε) K)⁻¹
  rw [hσ, map_one, MulAut.one_apply, hAu]
  set s₀ := Matrix.GeneralLinearGroup.scalar (HypIndex r ε) (Units.mk0 a ha) with hs₀
  have key : ∀ y : GL (HypIndex r ε) K, s₀ * y * s₀⁻¹ = y := fun y => by
    rw [← Subgroup.mem_center_iff.mp hscent y, mul_inv_cancel_right]
  calc s₀ * (u' : GL (HypIndex r ε) K) * (g : GL (HypIndex r ε) K) *
        (s₀ * (u' : GL (HypIndex r ε) K))⁻¹ =
        s₀ * ((u' : GL (HypIndex r ε) K) * (g : GL (HypIndex r ε) K) *
          (u' : GL (HypIndex r ε) K)⁻¹) * s₀⁻¹ := by group
    _ = _ := key _

theorem burnsideF411a_hyp_inner_of_fix_sylow (h : UnitaryFieldData p f K) {r ε : ℕ} (hr : 1 ≤ r)
    (hε : ε ≤ 1)
    (hcore : ∀ β : MulAut (hypPSU h r ε), (∀ x ∈ hypProjUnitriangular h r ε, β x = x) →
      ∃ g, β = MulAut.conj g)
    (α : MulAut (hypPSU h r ε)) (S : Sylow p (hypPSU h r ε))
    (hα : ∀ s ∈ (S : Subgroup (hypPSU h r ε)), α s = s) : ∃ g, α = MulAut.conj g := by
  have : Fact p.Prime := ⟨h.prime⟩
  have := h.finite
  obtain ⟨-, -, -, -, ⟨P₀, hP₀⟩, -, -⟩ := unitary_order_and_Sylow h hr hε
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq (hypPSU h r ε) P₀ S
  have hβ : ∀ u ∈ hypProjUnitriangular h r ε,
      ((MulAut.conj x)⁻¹ * α * MulAut.conj x) u = u := by
    intro u hu
    have hxu : x * u * x⁻¹ ∈ (S : Subgroup (hypPSU h r ε)) := by
      rw [← hx, Sylow.coe_subgroup_smul]
      have h1 := Subgroup.smul_mem_pointwise_smul u (MulAut.conj x) (P₀ : Subgroup _)
        (by rw [hP₀]; exact hu)
      rwa [MulAut.smul_def, MulAut.conj_apply] at h1
    rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_apply, hα _ hxu, MulAut.conj_inv_apply]
    group
  obtain ⟨g, hg⟩ := hcore _ hβ
  refine ⟨x * g * x⁻¹, ?_⟩
  rw [map_mul, map_mul, map_inv, ← hg]
  group

end UCore

end CFSG.ASVolI
