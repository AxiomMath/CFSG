module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TorusQSSL2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TorusQS

open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl CFSG.Assembly.LowTwoRank
open scoped Matrix

variable {K : Type} [Field K]

private theorem sp4_eq_one_of_perfect {G A : Type*} [Group G] [CommGroup A] {H : Subgroup G}
    (hH : ⁅H, H⁆ = H) (f : ↥H →* A) (x : ↥H) : f x = 1 := by
  have : Group.IsPerfect ↥H := Subgroup.isPerfect_iff.mpr hH
  have hx : x ∈ commutator ↥H := by
    rw [Group.IsPerfect.commutator_eq_top]
    exact Subgroup.mem_top x
  exact (MonoidHom.mem_ker).1 (Abelianization.commutator_subset_ker f hx)

private def sp4ToSL {G : Type*} [Group G] (f : G →* Matrix (Fin 2) (Fin 2) K)
    (hf : ∀ g, (f g).det = 1) : G →* Matrix.SpecialLinearGroup (Fin 2) K where
  toFun g := ⟨f g, hf g⟩
  map_one' := Subtype.ext (map_one f)
  map_mul' a b := Subtype.ext (map_mul f a b)

private theorem coe_sp4ToSL {G : Type*} [Group G] (f : G →* Matrix (Fin 2) (Fin 2) K)
    (hf : ∀ g, (f g).det = 1) (g : G) :
    ((sp4ToSL f hf g : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = f g :=
  rfl

open CFSG.CGT.Timmesfeld75 in
private theorem sp4_range_eq_bot_or_top [Finite K] [CharP K 2] (h4 : 4 ≤ Nat.card K)
    {G : Type*} [Group G]
    {H : Subgroup G} (hHH : ⁅H, H⁆ = H) (f : ↥H →* Matrix (Fin 2) (Fin 2) K)
    (hf : ∀ g, (f g).det = 1)
    (hT : ∀ (a : Kˣ) (g : ↥H), ∃ g' : ↥H, f g' 0 0 = a * f g 0 0 * ↑a⁻¹ ∧
      f g' 0 1 = a * f g 0 1 * a ∧ f g' 1 0 = ↑a⁻¹ * f g 1 0 * ↑a⁻¹ ∧
      f g' 1 1 = ↑a⁻¹ * f g 1 1 * a) :
    (sp4ToSL f hf).range = ⊥ ∨ (sp4ToSL f hf).range = ⊤ := by
  have : Group.IsPerfect ↥H := Subgroup.isPerfect_iff.mpr hHH
  refine perfect_eq_bot_or_top_of_torus h4
    (Subgroup.isPerfect_iff.mp (Group.IsPerfect.range (sp4ToSL f hf))) ?_
  rw [Subgroup.le_normalizer_iff]
  rintro t ht _ ⟨g, rfl⟩
  obtain ⟨a, rfl⟩ := CFSG.CGT.Timmesfeld75.mem_torus_iff.1 ht
  obtain ⟨g', e00, e01, e10, e11⟩ := hT a g
  refine ⟨g', CFSG.CGT.Timmesfeld75.sl2_ext ?_ ?_ ?_ ?_⟩ <;> sl2_simp <;>
    simp only [coe_sp4ToSL]
  · rw [e00]; ring
  · rw [e01]; ring
  · rw [e10]; ring
  · rw [e11]; ring

private theorem sp4_symp_entry {M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K}
    (hM : Mᵀ * Matrix.fromBlocks 0 1 (-1) 0 * M = Matrix.fromBlocks 0 1 (-1) 0)
    (a b : Fin 2 ⊕ Fin 2) :
    M (Sum.inl 0) a * M (Sum.inr 0) b - M (Sum.inr 0) a * M (Sum.inl 0) b +
      (M (Sum.inl 1) a * M (Sum.inr 1) b - M (Sum.inr 1) a * M (Sum.inl 1) b) =
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) a b := by
  rw [← hM]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Fintype.sum_sum_type, Fin.sum_univ_two,
    Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
    Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, Matrix.neg_apply, Matrix.one_apply_eq,
    Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
    Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide)]
  ring

private theorem sp4_torus_conj_apply (s : Fin 2 → Kˣ) (g : StatedSp 2 K) (x y : Fin 2 ⊕ Fin 2) :
    (((torusHom s * g * (torusHom s)⁻¹ : StatedSp 2 K) :
      Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) x y =
      Sum.elim (fun i => (s i : K)) (fun i => (((s i)⁻¹ : Kˣ) : K)) x *
        ((g : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) K) :
          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) x y *
        Sum.elim (fun i => (((s i)⁻¹ : Kˣ) : K)) (fun i => (s i : K)) y := by
  rw [coe_mul_statedSp, coe_mul_statedSp, ← map_inv, coe_torusHom, coe_torusHom,
    Matrix.mul_diagonal, Matrix.diagonal_mul]
  rcases y with y | y <;> simp

private theorem sp4_toBlocks₁₁_mul {M N : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K}
    (hN : ∀ i j : Fin 2, N (Sum.inr i) (Sum.inl j) = 0) :
    (M * N).toBlocks₁₁ = M.toBlocks₁₁ * N.toBlocks₁₁ := by
  ext i j
  simp [Matrix.toBlocks₁₁, Matrix.mul_apply, Fintype.sum_sum_type, hN]

private def sp4LagHom {H : Subgroup (StatedSp 2 K)}
    (hW : ∀ h ∈ H, ∀ i j : Fin 2,
      ((h : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) K) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) (Sum.inr i) (Sum.inl j) = 0) :
    ↥H →* Matrix (Fin 2) (Fin 2) K where
  toFun h := (((h : StatedSp 2 K) : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) K) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K).toBlocks₁₁
  map_one' := by
    ext i j
    simp [Matrix.toBlocks₁₁, Matrix.one_apply]
  map_mul' x y := by
    simp only [Subgroup.coe_mul, Units.val_mul]
    exact sp4_toBlocks₁₁_mul (hW _ y.2)

private theorem sp4_det_lagHom {H : Subgroup (StatedSp 2 K)} (hHH : ⁅H, H⁆ = H)
    (hW : ∀ h ∈ H, ∀ i j : Fin 2,
      ((h : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) K) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) (Sum.inr i) (Sum.inl j) = 0) (x : ↥H) :
    (sp4LagHom hW x).det = 1 := by
  have h := congrArg Units.val
    (sp4_eq_one_of_perfect hHH (Matrix.detMonoidHom.comp (sp4LagHom hW)).toHomUnits x)
  simpa using h

private theorem sp4LagHom_conj {H : Subgroup (StatedSp 2 K)}
    (hW : ∀ h ∈ H, ∀ i j : Fin 2,
      ((h : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) K) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) (Sum.inr i) (Sum.inl j) = 0)
    (s : Fin 2 → Kˣ) (g : ↥H) (hg : torusHom s * (g : StatedSp 2 K) * (torusHom s)⁻¹ ∈ H)
    (i j : Fin 2) :
    sp4LagHom hW ⟨_, hg⟩ i j = (s i : K) * sp4LagHom hW g i j * (((s j)⁻¹ : Kˣ) : K) :=
  sp4_torus_conj_apply s g (Sum.inl i) (Sum.inl j)

private theorem sp4_lag_mul_self [CharP K 2] {M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K}
    (hM : Mᵀ * Matrix.fromBlocks 0 1 (-1) 0 * M = Matrix.fromBlocks 0 1 (-1) 0)
    (hW : ∀ i j : Fin 2, M (Sum.inr i) (Sum.inl j) = 0) (hA : M.toBlocks₁₁ = 1) :
    M * M = 1 := by
  have hA' : ∀ i j : Fin 2, M (Sum.inl i) (Sum.inl j) = if i = j then 1 else 0 := by
    intro i j
    rw [← Matrix.one_apply]
    exact congrFun (congrFun hA i) j
  have hD : ∀ i j : Fin 2, M (Sum.inr i) (Sum.inr j) = if i = j then 1 else 0 := by
    intro i j
    have h := sp4_symp_entry hM (Sum.inl i) (Sum.inr j)
    rw [hW 0 i, hW 1 i, hA' 0 i, hA' 1 i, Matrix.fromBlocks_apply₁₂, Matrix.one_apply] at h
    fin_cases i <;> simpa using h
  ext (i | i) (j | j) <;>
    simp [Matrix.mul_apply, Fintype.sum_sum_type, hA', hW, hD, Matrix.one_apply,
      CharTwo.add_self_eq_zero]

theorem exists_sl2_of_stab_lagrangian [Finite K] [CharP K 2] (hK : 8 ≤ Nat.card K)
    {H : Subgroup (StatedSp 2 K)}
    (hHH : ⁅H, H⁆ = H) (hT : torus 2 K ≤ Subgroup.normalizer (H : Set (StatedSp 2 K)))
    (hW : ∀ h ∈ H, ∀ i j : Fin 2,
      ((h : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) K) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) (Sum.inr i) (Sum.inl j) = 0) :
    ∃ ψ : ↥H →* Matrix.SpecialLinearGroup (Fin 2) K, (ψ.range = ⊥ ∨ ψ.range = ⊤) ∧
      IsPGroup 2 ψ.ker := by
  refine ⟨sp4ToSL (sp4LagHom hW) (sp4_det_lagHom hHH hW),
    sp4_range_eq_bot_or_top (by omega) hHH _ _ fun a g => ?_, ?_⟩
  · have hτ := hT (torusHom_mem_torus ![a, a⁻¹])
    refine ⟨⟨_, (Subgroup.mem_normalizer_iff.1 hτ _).1 g.2⟩, ?_, ?_, ?_, ?_⟩ <;>
      rw [sp4LagHom_conj] <;> simp
  · rintro ⟨⟨x, hxH⟩, hk⟩
    have hk' : sp4ToSL (sp4LagHom hW) (sp4_det_lagHom hHH hW) ⟨x, hxH⟩ = 1 :=
      (MonoidHom.mem_ker).1 hk
    have hA : sp4LagHom hW ⟨x, hxH⟩ = 1 :=
      congrArg (fun A : Matrix.SpecialLinearGroup (Fin 2) K => (A : Matrix (Fin 2) (Fin 2) K)) hk'
    have hx2 : x ^ 2 = 1 := by
      apply statedSp_ext
      rw [pow_two, coe_mul_statedSp]
      exact sp4_lag_mul_self
        (CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.mem_statedSp_iff.1 x.2)
        (hW x hxH) hA
    refine ⟨1, Subtype.ext (Subtype.ext ?_)⟩
    simpa using hx2

private def sp4Idx : Fin 2 → Fin 2 ⊕ Fin 2 := ![Sum.inl 1, Sum.inr 1]

private theorem sp4_line_row {M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K}
    (hM : Mᵀ * Matrix.fromBlocks 0 1 (-1) 0 * M = Matrix.fromBlocks 0 1 (-1) 0)
    (hW : ∀ i, i ≠ Sum.inl 0 → M i (Sum.inl 0) = 0) :
    M (Sum.inl 0) (Sum.inl 0) * M (Sum.inr 0) (Sum.inr 0) = 1 ∧
      M (Sum.inr 0) (Sum.inl 1) = 0 ∧ M (Sum.inr 0) (Sum.inr 1) = 0 := by
  have key : ∀ b, M (Sum.inl 0) (Sum.inl 0) * M (Sum.inr 0) b =
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) (Sum.inl 0) b := by
    intro b
    have h := sp4_symp_entry hM (Sum.inl 0) b
    rw [hW (Sum.inr 0) Sum.inr_ne_inl, hW (Sum.inl 1) (by decide),
      hW (Sum.inr 1) Sum.inr_ne_inl] at h
    simpa using h
  have h1 : M (Sum.inl 0) (Sum.inl 0) * M (Sum.inr 0) (Sum.inr 0) = 1 := by
    simpa using key (Sum.inr 0)
  have h0 : M (Sum.inl 0) (Sum.inl 0) ≠ 0 := left_ne_zero_of_mul_eq_one h1
  exact ⟨h1, by simpa [h0] using key (Sum.inl 1),
    by simpa [h0, Matrix.one_apply] using key (Sum.inr 1)⟩

private theorem sp4_det_line {M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K}
    (hM : Mᵀ * Matrix.fromBlocks 0 1 (-1) 0 * M = Matrix.fromBlocks 0 1 (-1) 0)
    (hW : ∀ i, i ≠ Sum.inl 0 → M i (Sum.inl 0) = 0) :
    (M.submatrix sp4Idx sp4Idx).det = 1 := by
  obtain ⟨-, h1, h2⟩ := sp4_line_row hM hW
  have h := sp4_symp_entry hM (Sum.inl 1) (Sum.inr 1)
  rw [h1, h2, Matrix.fromBlocks_apply₁₂, Matrix.one_apply_eq] at h
  rw [Matrix.det_fin_two]
  simp only [sp4Idx, Matrix.submatrix_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  linear_combination h

private theorem sp4_submatrix_mul {M N : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K}
    (hM1 : M (Sum.inl 1) (Sum.inl 0) = 0) (hM2 : M (Sum.inr 1) (Sum.inl 0) = 0)
    (hN1 : N (Sum.inr 0) (Sum.inl 1) = 0) (hN2 : N (Sum.inr 0) (Sum.inr 1) = 0) :
    (M * N).submatrix sp4Idx sp4Idx = M.submatrix sp4Idx sp4Idx * N.submatrix sp4Idx sp4Idx := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.submatrix_apply, Fintype.sum_sum_type, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> simp [sp4Idx, hM1, hM2, hN1, hN2]

private def sp4LineHom {H : Subgroup (StatedSp 2 K)}
    (hW : ∀ h ∈ H, ∀ i : Fin 2 ⊕ Fin 2, i ≠ Sum.inl 0 →
      ((h : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) K) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) i (Sum.inl 0) = 0) :
    ↥H →* Matrix (Fin 2) (Fin 2) K where
  toFun h := (((h : StatedSp 2 K) : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) K) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K).submatrix sp4Idx sp4Idx
  map_one' := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [sp4Idx, Matrix.one_apply]
  map_mul' x y := by
    obtain ⟨-, h1, h2⟩ := sp4_line_row
      (CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.mem_statedSp_iff.1
        (y : StatedSp 2 K).2) (hW _ y.2)
    simp only [Subgroup.coe_mul, Units.val_mul]
    exact sp4_submatrix_mul (hW _ x.2 _ (by decide)) (hW _ x.2 _ Sum.inr_ne_inl) h1 h2

private theorem sp4_det_lineHom {H : Subgroup (StatedSp 2 K)}
    (hW : ∀ h ∈ H, ∀ i : Fin 2 ⊕ Fin 2, i ≠ Sum.inl 0 →
      ((h : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) K) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) i (Sum.inl 0) = 0) (x : ↥H) :
    (sp4LineHom hW x).det = 1 :=
  sp4_det_line (CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.mem_statedSp_iff.1
    (x : StatedSp 2 K).2) (hW _ x.2)

private theorem sp4LineHom_conj {H : Subgroup (StatedSp 2 K)}
    (hW : ∀ h ∈ H, ∀ i : Fin 2 ⊕ Fin 2, i ≠ Sum.inl 0 →
      ((h : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) K) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) i (Sum.inl 0) = 0)
    (s : Fin 2 → Kˣ) (g : ↥H) (hg : torusHom s * (g : StatedSp 2 K) * (torusHom s)⁻¹ ∈ H)
    (i j : Fin 2) :
    sp4LineHom hW ⟨_, hg⟩ i j =
      Sum.elim (fun k => (s k : K)) (fun k => (((s k)⁻¹ : Kˣ) : K)) (sp4Idx i) *
        sp4LineHom hW g i j *
        Sum.elim (fun k => (((s k)⁻¹ : Kˣ) : K)) (fun k => (s k : K)) (sp4Idx j) :=
  sp4_torus_conj_apply s g (sp4Idx i) (sp4Idx j)

private theorem sp4LineHom_eq_one {H : Subgroup (StatedSp 2 K)}
    {hW : ∀ h ∈ H, ∀ i : Fin 2 ⊕ Fin 2, i ≠ Sum.inl 0 →
      ((h : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) K) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) i (Sum.inl 0) = 0}
    {x : StatedSp 2 K} {hx : x ∈ H} (hA : sp4LineHom hW ⟨x, hx⟩ = 1) :
    ((x : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) K) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) (Sum.inl 1) (Sum.inl 1) = 1 ∧
      ((x : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) K) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) (Sum.inl 1) (Sum.inr 1) = 0 ∧
      ((x : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) K) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) (Sum.inr 1) (Sum.inl 1) = 0 ∧
      ((x : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) K) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) (Sum.inr 1) (Sum.inr 1) = 1 := by
  have e : ∀ i j, ((x : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) (sp4Idx i) (sp4Idx j) =
      if i = j then 1 else 0 := by
    intro i j
    rw [← Matrix.one_apply]
    exact congrFun (congrFun hA i) j
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [sp4Idx] using e 0 0
  · simpa [sp4Idx] using e 0 1
  · simpa [sp4Idx] using e 1 0
  · simpa [sp4Idx] using e 1 1

private theorem sp4_mul_apply_inl0 {M N : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K}
    (hN : ∀ i, i ≠ Sum.inl 0 → N i (Sum.inl 0) = 0) :
    (M * N) (Sum.inl 0) (Sum.inl 0) = M (Sum.inl 0) (Sum.inl 0) * N (Sum.inl 0) (Sum.inl 0) := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (Sum.inl 0)]
  · intro b _ hb
    rw [hN b hb, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

private def sp4LamHom {H : Subgroup (StatedSp 2 K)}
    (hW : ∀ h ∈ H, ∀ i : Fin 2 ⊕ Fin 2, i ≠ Sum.inl 0 →
      ((h : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) K) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) i (Sum.inl 0) = 0) :
    ↥H →* K where
  toFun h := (((h : StatedSp 2 K) : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) K) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) (Sum.inl 0) (Sum.inl 0)
  map_one' := by simp
  map_mul' x y := by
    simp only [Subgroup.coe_mul, Units.val_mul]
    exact sp4_mul_apply_inl0 (hW _ y.2)

private theorem sp4_lam_eq_one {H : Subgroup (StatedSp 2 K)} (hHH : ⁅H, H⁆ = H)
    (hW : ∀ h ∈ H, ∀ i : Fin 2 ⊕ Fin 2, i ≠ Sum.inl 0 →
      ((h : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) K) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) i (Sum.inl 0) = 0)
    {x : StatedSp 2 K} (hx : x ∈ H) :
    ((x : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) (Sum.inl 0) (Sum.inl 0) = 1 := by
  have h := congrArg Units.val (sp4_eq_one_of_perfect hHH (sp4LamHom hW).toHomUnits ⟨x, hx⟩)
  exact h

private theorem sp4_line_sq_apply [CharP K 2] {M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K}
    (h1 : M (Sum.inl 0) (Sum.inl 0) = 1) (h2 : M (Sum.inl 1) (Sum.inl 0) = 0)
    (h3 : M (Sum.inr 0) (Sum.inl 0) = 0) (h4 : M (Sum.inr 1) (Sum.inl 0) = 0)
    (h5 : M (Sum.inl 1) (Sum.inl 1) = 1) (h6 : M (Sum.inl 1) (Sum.inr 1) = 0)
    (h7 : M (Sum.inr 1) (Sum.inl 1) = 0) (h8 : M (Sum.inr 1) (Sum.inr 1) = 1)
    (h9 : M (Sum.inr 0) (Sum.inl 1) = 0) (h10 : M (Sum.inr 0) (Sum.inr 1) = 0)
    (h11 : M (Sum.inr 0) (Sum.inr 0) = 1) (x y : Fin 2 ⊕ Fin 2)
    (hxy : ¬(x = Sum.inl 0 ∧ y = Sum.inr 0)) :
    (M * M) x y = if x = y then 1 else 0 := by
  rcases x with x | x <;> rcases y with y | y <;> fin_cases x <;> fin_cases y <;>
    simp [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, h1, h2, h3, h4, h5, h6, h7,
      h8, h9, h10, h11, CharTwo.add_self_eq_zero] at hxy ⊢

private theorem sp4_mul_self_of_apply [CharP K 2] {P : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K}
    (hP : ∀ x y, ¬(x = Sum.inl 0 ∧ y = Sum.inr 0) → P x y = if x = y then 1 else 0) :
    P * P = 1 := by
  ext x y
  rcases x with x | x <;> rcases y with y | y <;> fin_cases x <;> fin_cases y <;>
    simp [Matrix.mul_apply, Fintype.sum_sum_type, hP, CharTwo.add_self_eq_zero]

theorem exists_sl2_of_stab_line [Finite K] [CharP K 2] (hK : 8 ≤ Nat.card K)
    {H : Subgroup (StatedSp 2 K)}
    (hHH : ⁅H, H⁆ = H) (hT : torus 2 K ≤ Subgroup.normalizer (H : Set (StatedSp 2 K)))
    (hW : ∀ h ∈ H, ∀ i : Fin 2 ⊕ Fin 2, i ≠ Sum.inl 0 →
      ((h : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) K) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) i (Sum.inl 0) = 0) :
    ∃ ψ : ↥H →* Matrix.SpecialLinearGroup (Fin 2) K, (ψ.range = ⊥ ∨ ψ.range = ⊤) ∧
      IsPGroup 2 ψ.ker := by
  refine ⟨sp4ToSL (sp4LineHom hW) (sp4_det_lineHom hW),
    sp4_range_eq_bot_or_top (by omega) hHH _ _ fun a g => ?_, ?_⟩
  · have hτ := hT (torusHom_mem_torus fun _ : Fin 2 => a)
    refine ⟨⟨_, (Subgroup.mem_normalizer_iff.1 hτ _).1 g.2⟩, ?_, ?_, ?_, ?_⟩ <;>
      rw [sp4LineHom_conj] <;> simp [sp4Idx]
  · rintro ⟨⟨x, hxH⟩, hk⟩
    have hk' : sp4ToSL (sp4LineHom hW) (sp4_det_lineHom hW) ⟨x, hxH⟩ = 1 :=
      (MonoidHom.mem_ker).1 hk
    have hA : sp4LineHom hW ⟨x, hxH⟩ = 1 :=
      congrArg (fun A : Matrix.SpecialLinearGroup (Fin 2) K => (A : Matrix (Fin 2) (Fin 2) K)) hk'
    obtain ⟨e5, e6, e7, e8⟩ := sp4LineHom_eq_one hA
    have e1 := sp4_lam_eq_one hHH hW hxH
    obtain ⟨r1, r2, r3⟩ := sp4_line_row
      (CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.mem_statedSp_iff.1 x.2) (hW x hxH)
    rw [e1, one_mul] at r1
    have hx4 : x ^ 4 = 1 := by
      apply statedSp_ext
      rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sq, sq, coe_mul_statedSp, coe_mul_statedSp]
      exact sp4_mul_self_of_apply (sp4_line_sq_apply e1 (hW x hxH _ (by decide))
        (hW x hxH _ Sum.inr_ne_inl) (hW x hxH _ Sum.inr_ne_inl) e5 e6 e7 e8 r2 r3 r1)
    refine ⟨2, Subtype.ext (Subtype.ext ?_)⟩
    simpa using hx4

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TorusQS

end
