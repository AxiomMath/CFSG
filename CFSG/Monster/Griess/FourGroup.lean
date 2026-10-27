module

public import CFSG.Monster.Griess.TrialityMatrix
public import CFSG.Monster.Griess.Parity

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Griess

open CFSG.Monster CFSG.Monster.Spin Matrix Module

@[expose] def oddSign (s : Fin 3 → ℚ) : TIdx → ℚ
  | .inr (.inr (.inl (_, _, k))) => s k
  | _ => 1

@[expose] noncomputable def oddSignMat (s : Fin 3 → ℚ) : Matrix TIdx TIdx ℚ :=
  diag2 1 (diag2 1 (diag2 (kron1 C₀ (kron1 (Fin 24) (diagonal s))) 1))

@[expose] def sgnX : Fin 3 → ℚ := ![1, -1, -1]

@[expose] def sgnY : Fin 3 → ℚ := ![-1, 1, -1]

@[expose] def sgnZ : Fin 3 → ℚ := ![-1, -1, 1]

theorem oddSign_odd (s : Fin 3 → ℚ) (c : C₀) (i : Fin 24) (k : Fin 3) :
    oddSign s (.inr (.inr (.inl (c, i, k)))) = s k := rfl

theorem oddSignMat_eq_diagonal (s : Fin 3 → ℚ) : oddSignMat s = diagonal (oddSign s) := by
  ext x y
  rcases x with i | q | ⟨c, i, k⟩ | o <;> rcases y with j | q' | ⟨c', i', k'⟩ | o'
  all_goals try simp [oddSignMat, diag2, diagonal_apply, oddSign, one_apply]
  simp only [kron1_apply, one_apply, diagonal_apply]
  by_cases hc : c = c' <;> by_cases hi : i = i' <;> by_cases hk : k = k' <;> simp [hc, hi, hk]

theorem oddSignMat_mul (s t : Fin 3 → ℚ) : oddSignMat s * oddSignMat t = oddSignMat (s * t) := by
  rw [oddSignMat, oddSignMat, oddSignMat, diag2_mul, diag2_mul, diag2_mul, kron1_mul, kron1_mul,
    diagonal_mul_diagonal, Matrix.one_mul, Matrix.one_mul, Matrix.one_mul]
  rfl

theorem oddSignMat_one : oddSignMat (fun _ => 1) = 1 := by
  rw [oddSignMat, diagonal_one, kron1_one, kron1_one, diag2_one, diag2_one, diag2_one]

theorem tauMat_transpose_conj (s : Fin 3 → ℚ) :
    tauMatᵀ * oddSignMat s * tauMat = oddSignMat ![s 2, s 0, s 1] := by
  simp only [tauMat, oddSignMat, diag2_transpose, diag2_mul, transpose_one, Matrix.mul_one,
    pairBlock_transpose_mul, octBlock_transpose_mul, oddBlock, kron1_transpose, kron1_mul,
    cyc3_conj_diagonal]

private theorem apply_tbasis_of_coe {g : SpaceB ≃ₗ[ℚ] SpaceB} {s : Fin 3 → ℚ}
    (hg : (g : SpaceB →ₗ[ℚ] SpaceB) = toLin tbasis tbasis (oddSignMat s)) (t : TIdx) :
    g (tbasis t) = oddSign s t • tbasis t := by
  have h := LinearMap.congr_fun hg (tbasis t)
  rw [oddSignMat_eq_diagonal, toLin_diagonal_self] at h
  exact h

private theorem coe_mul_of_coe {g h : SpaceB ≃ₗ[ℚ] SpaceB} {s t : Fin 3 → ℚ}
    (hg : (g : SpaceB →ₗ[ℚ] SpaceB) = toLin tbasis tbasis (oddSignMat s))
    (hh : (h : SpaceB →ₗ[ℚ] SpaceB) = toLin tbasis tbasis (oddSignMat t)) :
    ((g * h : SpaceB ≃ₗ[ℚ] SpaceB) : SpaceB →ₗ[ℚ] SpaceB) =
      toLin tbasis tbasis (oddSignMat (s * t)) := by
  rw [LinearEquiv.coe_toLinearMap_mul, hg, hh, ← oddSignMat_mul, Matrix.toLin_mul tbasis tbasis]
  rfl

theorem coe_conj_tauB {g : SpaceB ≃ₗ[ℚ] SpaceB} {G : Matrix TIdx TIdx ℚ}
    (hg : (g : SpaceB →ₗ[ℚ] SpaceB) = toLin tbasis tbasis G) :
    ((tauB * g * tauB⁻¹ : SpaceB ≃ₗ[ℚ] SpaceB) : SpaceB →ₗ[ℚ] SpaceB) =
      toLin tbasis tbasis (tauMatᵀ * G * tauMat) := by
  rw [LinearEquiv.coe_toLinearMap_mul, LinearEquiv.coe_toLinearMap_mul, coe_tauB, hg,
    Matrix.toLin_mul tbasis tbasis tbasis, Matrix.toLin_mul tbasis tbasis tbasis]
  rfl

private theorem eq_of_coe {g h : SpaceB ≃ₗ[ℚ] SpaceB} {s : Fin 3 → ℚ}
    (hg : (g : SpaceB →ₗ[ℚ] SpaceB) = toLin tbasis tbasis (oddSignMat s))
    (hh : (h : SpaceB →ₗ[ℚ] SpaceB) = toLin tbasis tbasis (oddSignMat s)) : g = h :=
  LinearEquiv.toLinearMap_injective (hg.trans hh.symm)

private theorem ne_of_coe {g h : SpaceB ≃ₗ[ℚ] SpaceB} {s t : Fin 3 → ℚ}
    (hg : (g : SpaceB →ₗ[ℚ] SpaceB) = toLin tbasis tbasis (oddSignMat s))
    (hh : (h : SpaceB →ₗ[ℚ] SpaceB) = toLin tbasis tbasis (oddSignMat t)) {k : Fin 3}
    (hk : s k ≠ t k) : g ≠ h := by
  intro hgh
  have e := congrArg (fun f : SpaceB ≃ₗ[ℚ] SpaceB => f (tbasis (.inr (.inr (.inl (0, 0, k))))))
    hgh
  simp only [apply_tbasis_of_coe hg, apply_tbasis_of_coe hh, oddSign_odd] at e
  exact hk ((smul_left_inj (tbasis.ne_zero _)).1 e)

private theorem coe_one_eq : ((1 : SpaceB ≃ₗ[ℚ] SpaceB) : SpaceB →ₗ[ℚ] SpaceB) =
    toLin tbasis tbasis (oddSignMat fun _ => 1) := by
  rw [oddSignMat_one, Matrix.toLin_one]
  rfl

private theorem xB_mk (a : symMat) (b : SpaceX) (c : SpaceW) : xB (a, b, c) = (a, b, -c) := rfl

theorem xB_tbasis (t : TIdx) : xB (tbasis t) = oddSign sgnX t • tbasis t := by
  rcases t with i | ⟨p, k⟩ | ⟨c, i, k⟩ | o
  · rw [tbasis_diag, xB_mk, neg_zero]
    exact (one_smul ℚ _).symm
  · obtain rfl | rfl | rfl : k = 0 ∨ k = 1 ∨ k = 2 := by fin_cases k <;> simp
    · rw [tbasis_pair_zero, xB_mk, neg_zero]
      exact (one_smul ℚ _).symm
    · rw [tbasis_pair_one, xB_mk, neg_zero]
      exact (one_smul ℚ _).symm
    · rw [tbasis_pair_two, xB_mk, neg_zero]
      exact (one_smul ℚ _).symm
  · obtain rfl | rfl | rfl : k = 0 ∨ k = 1 ∨ k = 2 := by fin_cases k <;> simp
    · rw [tbasis_odd_zero, xB_mk, neg_zero]
      exact (one_smul ℚ _).symm
    · rw [tbasis_odd_one, xB_mk, oddSign_odd]
      simp [sgnX]
    · rw [tbasis_odd_two, xB_mk, oddSign_odd]
      simp [sgnX]
  · rw [tbasis_oct, xB_mk, neg_zero]
    exact (one_smul ℚ _).symm

theorem coe_xB : (xB : SpaceB →ₗ[ℚ] SpaceB) = toLin tbasis tbasis (oddSignMat sgnX) := by
  refine tbasis.ext fun t => ?_
  rw [LinearEquiv.coe_coe, xB_tbasis, oddSignMat_eq_diagonal, toLin_diagonal_self]

@[expose] noncomputable def yB : SpaceB ≃ₗ[ℚ] SpaceB := tauB * xB * tauB⁻¹

@[expose] noncomputable def zB : SpaceB ≃ₗ[ℚ] SpaceB := tauB ^ 2 * xB * (tauB ^ 2)⁻¹

theorem zB_eq : zB = tauB * yB * tauB⁻¹ := by
  rw [zB, yB, pow_two, _root_.mul_inv_rev]
  simp only [mul_assoc]

theorem coe_yB : (yB : SpaceB →ₗ[ℚ] SpaceB) = toLin tbasis tbasis (oddSignMat sgnY) := by
  rw [yB, coe_conj_tauB coe_xB, tauMat_transpose_conj]
  rfl

theorem coe_zB : (zB : SpaceB →ₗ[ℚ] SpaceB) = toLin tbasis tbasis (oddSignMat sgnZ) := by
  rw [zB_eq, coe_conj_tauB coe_yB, tauMat_transpose_conj]
  rfl

theorem yB_tbasis (t : TIdx) : yB (tbasis t) = oddSign sgnY t • tbasis t :=
  apply_tbasis_of_coe coe_yB t

theorem zB_tbasis (t : TIdx) : zB (tbasis t) = oddSign sgnZ t • tbasis t :=
  apply_tbasis_of_coe coe_zB t

theorem sgnX_mul_sgnY : sgnX * sgnY = sgnZ := by
  funext k; fin_cases k <;> norm_num [sgnX, sgnY, sgnZ]

theorem sgnY_mul_sgnX : sgnY * sgnX = sgnZ := by
  funext k; fin_cases k <;> norm_num [sgnX, sgnY, sgnZ]

theorem sgnY_mul_sgnZ : sgnY * sgnZ = sgnX := by
  funext k; fin_cases k <;> norm_num [sgnX, sgnY, sgnZ]

theorem sgnZ_mul_sgnY : sgnZ * sgnY = sgnX := by
  funext k; fin_cases k <;> norm_num [sgnX, sgnY, sgnZ]

theorem sgnZ_mul_sgnX : sgnZ * sgnX = sgnY := by
  funext k; fin_cases k <;> norm_num [sgnX, sgnY, sgnZ]

theorem sgnX_mul_sgnZ : sgnX * sgnZ = sgnY := by
  funext k; fin_cases k <;> norm_num [sgnX, sgnY, sgnZ]

theorem sgnX_mul_sgnX : sgnX * sgnX = fun _ => 1 := by
  funext k; fin_cases k <;> norm_num [sgnX]

theorem sgnY_mul_sgnY : sgnY * sgnY = fun _ => 1 := by
  funext k; fin_cases k <;> norm_num [sgnY]

theorem sgnZ_mul_sgnZ : sgnZ * sgnZ = fun _ => 1 := by
  funext k; fin_cases k <;> norm_num [sgnZ]

theorem xB_mul_yB : xB * yB = zB :=
  eq_of_coe (sgnX_mul_sgnY ▸ coe_mul_of_coe coe_xB coe_yB) coe_zB

theorem yB_mul_xB : yB * xB = zB :=
  eq_of_coe (sgnY_mul_sgnX ▸ coe_mul_of_coe coe_yB coe_xB) coe_zB

theorem yB_mul_zB : yB * zB = xB :=
  eq_of_coe (sgnY_mul_sgnZ ▸ coe_mul_of_coe coe_yB coe_zB) coe_xB

theorem zB_mul_yB : zB * yB = xB :=
  eq_of_coe (sgnZ_mul_sgnY ▸ coe_mul_of_coe coe_zB coe_yB) coe_xB

theorem zB_mul_xB : zB * xB = yB :=
  eq_of_coe (sgnZ_mul_sgnX ▸ coe_mul_of_coe coe_zB coe_xB) coe_yB

theorem xB_mul_zB : xB * zB = yB :=
  eq_of_coe (sgnX_mul_sgnZ ▸ coe_mul_of_coe coe_xB coe_zB) coe_yB

theorem yB_mul_self : yB * yB = 1 :=
  eq_of_coe (sgnY_mul_sgnY ▸ coe_mul_of_coe coe_yB coe_yB) coe_one_eq

theorem zB_mul_self : zB * zB = 1 :=
  eq_of_coe (sgnZ_mul_sgnZ ▸ coe_mul_of_coe coe_zB coe_zB) coe_one_eq

theorem xB_ne_yB : xB ≠ yB := ne_of_coe coe_xB coe_yB (k := 0) (by norm_num [sgnX, sgnY])

theorem xB_ne_zB : xB ≠ zB := ne_of_coe coe_xB coe_zB (k := 0) (by norm_num [sgnX, sgnZ])

theorem yB_ne_zB : yB ≠ zB := ne_of_coe coe_yB coe_zB (k := 1) (by norm_num [sgnY, sgnZ])

theorem one_ne_xB : (1 : SpaceB ≃ₗ[ℚ] SpaceB) ≠ xB :=
  ne_of_coe coe_one_eq coe_xB (k := 1) (by norm_num [sgnX])

theorem one_ne_yB : (1 : SpaceB ≃ₗ[ℚ] SpaceB) ≠ yB :=
  ne_of_coe coe_one_eq coe_yB (k := 0) (by norm_num [sgnY])

theorem one_ne_zB : (1 : SpaceB ≃ₗ[ℚ] SpaceB) ≠ zB :=
  ne_of_coe coe_one_eq coe_zB (k := 0) (by norm_num [sgnZ])

theorem conj_tauB_xB : tauB * xB * tauB⁻¹ = yB := rfl

theorem conj_tauB_yB : tauB * yB * tauB⁻¹ = zB := zB_eq.symm

theorem conj_tauB_zB : tauB * zB * tauB⁻¹ = xB := by
  have h : tauB * zB * tauB⁻¹ = tauB ^ 3 * xB * (tauB ^ 3)⁻¹ := by
    rw [zB]
    group
  rw [h, tauB_pow_three, inv_one, one_mul, mul_one]

@[expose] noncomputable def fourGroupB : Subgroup (SpaceB ≃ₗ[ℚ] SpaceB) where
  carrier := {1, xB, yB, zB}
  mul_mem' := by
    rintro a b (rfl | rfl | rfl | rfl) (rfl | rfl | rfl | rfl) <;>
      simp [xB_mul_self, yB_mul_self, zB_mul_self, xB_mul_yB, yB_mul_xB, yB_mul_zB, zB_mul_yB,
        zB_mul_xB, xB_mul_zB]
  one_mem' := Or.inl rfl
  inv_mem' := by
    rintro a (rfl | rfl | rfl | rfl)
    · simp
    · rw [inv_eq_of_mul_eq_one_right xB_mul_self]; simp
    · rw [inv_eq_of_mul_eq_one_right yB_mul_self]; simp
    · rw [inv_eq_of_mul_eq_one_right zB_mul_self]; simp

theorem mem_fourGroupB {g : SpaceB ≃ₗ[ℚ] SpaceB} :
    g ∈ fourGroupB ↔ g = 1 ∨ g = xB ∨ g = yB ∨ g = zB := Iff.rfl

theorem fourGroupB_eq_closure : fourGroupB = Subgroup.closure {xB, yB} := by
  apply le_antisymm
  · rintro g (rfl | rfl | rfl | rfl)
    · exact Subgroup.one_mem _
    · exact Subgroup.subset_closure (Set.mem_insert _ _)
    · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
    · rw [← xB_mul_yB]
      exact Subgroup.mul_mem _ (Subgroup.subset_closure (Set.mem_insert _ _))
        (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl))
  · rw [Subgroup.closure_le]
    rintro g (rfl | rfl)
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))

theorem sq_of_mem_fourGroupB {g : SpaceB ≃ₗ[ℚ] SpaceB} (hg : g ∈ fourGroupB) : g * g = 1 := by
  rcases hg with rfl | rfl | rfl | rfl
  · exact one_mul 1
  · exact xB_mul_self
  · exact yB_mul_self
  · exact zB_mul_self

theorem mul_comm_of_mem_fourGroupB {g h : SpaceB ≃ₗ[ℚ] SpaceB} (hg : g ∈ fourGroupB)
    (hh : h ∈ fourGroupB) : g * h = h * g := by
  rcases hg with rfl | rfl | rfl | rfl <;> rcases hh with rfl | rfl | rfl | rfl <;>
    simp only [one_mul, mul_one, xB_mul_yB, yB_mul_xB, yB_mul_zB, zB_mul_yB, zB_mul_xB, xB_mul_zB]

theorem isElementaryAbelian_fourGroupB : IsElementaryAbelian 2 fourGroupB where
  is_comm := ⟨fun g h => Subtype.ext (mul_comm_of_mem_fourGroupB g.2 h.2)⟩
  exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun g =>
    Subtype.ext (by rw [Subgroup.coe_pow, pow_two, sq_of_mem_fourGroupB g.2, Subgroup.coe_one])

theorem card_fourGroupB : Nat.card fourGroupB = 4 := by
  change Set.ncard ({1, xB, yB, zB} : Set (SpaceB ≃ₗ[ℚ] SpaceB)) = 4
  rw [Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem, Set.ncard_pair yB_ne_zB]
  · rintro (h | h)
    · exact xB_ne_yB h
    · exact xB_ne_zB h
  · rintro (h | h | h)
    · exact one_ne_xB h
    · exact one_ne_yB h
    · exact one_ne_zB h

theorem bform_yB (u v : SpaceB) : bform (yB u) (yB v) = bform u v := by
  change bform (tauB (xB (tauB.symm u))) (tauB (xB (tauB.symm v))) = bform u v
  rw [bform_tauB, bform_xB, bform_tauB_symm]

theorem bform_zB (u v : SpaceB) : bform (zB u) (zB v) = bform u v := by
  rw [zB_eq]
  change bform (tauB (yB (tauB.symm u))) (tauB (yB (tauB.symm v))) = bform u v
  rw [bform_tauB, bform_yB, bform_tauB_symm]

theorem yB_mem_BR_iff {u : SpaceB} : yB u ∈ BR ↔ u ∈ BR := by
  change tauB (xB (tauB.symm u)) ∈ BR ↔ u ∈ BR
  rw [tauB_mem_BR_iff, xB_mem_BR_iff, tauB_symm_mem_BR_iff]

theorem zB_mem_BR_iff {u : SpaceB} : zB u ∈ BR ↔ u ∈ BR := by
  rw [zB_eq]
  change tauB (yB (tauB.symm u)) ∈ BR ↔ u ∈ BR
  rw [tauB_mem_BR_iff, yB_mem_BR_iff, tauB_symm_mem_BR_iff]

theorem bform_of_mem_fourGroupB {g : SpaceB ≃ₗ[ℚ] SpaceB} (hg : g ∈ fourGroupB) (u v : SpaceB) :
    bform (g u) (g v) = bform u v := by
  rcases hg with rfl | rfl | rfl | rfl
  · rfl
  · exact bform_xB u v
  · exact bform_yB u v
  · exact bform_zB u v

theorem mem_BR_iff_of_mem_fourGroupB {g : SpaceB ≃ₗ[ℚ] SpaceB} (hg : g ∈ fourGroupB)
    {u : SpaceB} : g u ∈ BR ↔ u ∈ BR := by
  rcases hg with rfl | rfl | rfl | rfl
  · exact Iff.rfl
  · exact xB_mem_BR_iff
  · exact yB_mem_BR_iff
  · exact zB_mem_BR_iff

theorem map_BR_of_mem_fourGroupB {g : SpaceB ≃ₗ[ℚ] SpaceB} (hg : g ∈ fourGroupB) :
    BR.map ((g : SpaceB →ₗ[ℚ] SpaceB).restrictScalars dyadic) = BR := by
  ext u
  refine ⟨?_, fun h => ⟨g.symm u, (mem_BR_iff_of_mem_fourGroupB hg).1 (by simpa using h),
    g.apply_symm_apply u⟩⟩
  rintro ⟨v, hv, rfl⟩
  exact (mem_BR_iff_of_mem_fourGroupB hg).2 hv

theorem eigenspace_conj_eq_map (e g : SpaceB ≃ₗ[ℚ] SpaceB) (μ : ℚ) :
    End.eigenspace ((e * g * e⁻¹ : SpaceB ≃ₗ[ℚ] SpaceB) : End ℚ SpaceB) μ =
      (End.eigenspace (g : End ℚ SpaceB) μ).map (e : SpaceB →ₗ[ℚ] SpaceB) := by
  ext u
  rw [End.mem_eigenspace_iff, Submodule.mem_map_equiv, End.mem_eigenspace_iff]
  change e (g (e.symm u)) = μ • u ↔ g (e.symm u) = μ • e.symm u
  constructor
  · intro h
    rw [← map_smul, ← h, LinearEquiv.symm_apply_apply]
  · intro h
    rw [h, map_smul, LinearEquiv.apply_symm_apply]

theorem finrank_eigenspace_conj (e g : SpaceB ≃ₗ[ℚ] SpaceB) (μ : ℚ) :
    finrank ℚ (End.eigenspace ((e * g * e⁻¹ : SpaceB ≃ₗ[ℚ] SpaceB) : End ℚ SpaceB) μ) =
      finrank ℚ (End.eigenspace (g : End ℚ SpaceB) μ) := by
  rw [eigenspace_conj_eq_map, LinearEquiv.finrank_map_eq]

theorem finrank_eigenspace_yB_neg_one :
    finrank ℚ (End.eigenspace (yB : End ℚ SpaceB) (-1)) = 98304 := by
  rw [yB, finrank_eigenspace_conj, finrank_eigenspace_xB_neg_one]

theorem finrank_eigenspace_zB_neg_one :
    finrank ℚ (End.eigenspace (zB : End ℚ SpaceB) (-1)) = 98304 := by
  rw [zB_eq, finrank_eigenspace_conj, finrank_eigenspace_yB_neg_one]

theorem rational_triality_four_group :
    yB = tauB * xB * tauB⁻¹ ∧ zB = tauB ^ 2 * xB * (tauB ^ 2)⁻¹ ∧
    (∀ t : TIdx, xB (tbasis t) = oddSign ![1, -1, -1] t • tbasis t) ∧
    (∀ t : TIdx, yB (tbasis t) = oddSign ![-1, 1, -1] t • tbasis t) ∧
    (∀ t : TIdx, zB (tbasis t) = oddSign ![-1, -1, 1] t • tbasis t) ∧
    (∀ g : SpaceB ≃ₗ[ℚ] SpaceB, g ∈ fourGroupB ↔ g = 1 ∨ g = xB ∨ g = yB ∨ g = zB) ∧
    fourGroupB = Subgroup.closure {xB, yB} ∧
    Nat.card fourGroupB = 4 ∧ IsElementaryAbelian 2 fourGroupB ∧
    xB * yB = zB ∧ yB * zB = xB ∧ zB * xB = yB ∧
    yB * xB = zB ∧ zB * yB = xB ∧ xB * zB = yB ∧
    tauB * xB * tauB⁻¹ = yB ∧ tauB * yB * tauB⁻¹ = zB ∧ tauB * zB * tauB⁻¹ = xB ∧
    (∀ g ∈ fourGroupB, ∀ u v : SpaceB, bform (g u) (g v) = bform u v) ∧
    (∀ g ∈ fourGroupB, BR.map ((g : SpaceB →ₗ[ℚ] SpaceB).restrictScalars dyadic) = BR) ∧
    finrank ℚ (End.eigenspace (xB : End ℚ SpaceB) (-1)) = 98304 ∧
    finrank ℚ (End.eigenspace (yB : End ℚ SpaceB) (-1)) = 98304 ∧
    finrank ℚ (End.eigenspace (zB : End ℚ SpaceB) (-1)) = 98304 :=
  ⟨rfl, rfl, xB_tbasis, yB_tbasis, zB_tbasis, fun _ => Iff.rfl, fourGroupB_eq_closure,
    card_fourGroupB, isElementaryAbelian_fourGroupB, xB_mul_yB, yB_mul_zB, zB_mul_xB,
    yB_mul_xB, zB_mul_yB, xB_mul_zB, conj_tauB_xB, conj_tauB_yB, conj_tauB_zB,
    fun _ hg => bform_of_mem_fourGroupB hg, fun _ hg => map_BR_of_mem_fourGroupB hg,
    finrank_eigenspace_xB_neg_one,
    finrank_eigenspace_yB_neg_one, finrank_eigenspace_zB_neg_one⟩

end CFSG.Monster.Griess
