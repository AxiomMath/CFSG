module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoIVU62Model

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK432

open Matrix CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIVU62
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag

@[expose] noncomputable def dgl : (Fin 6 → F4ˣ) →* GL (Fin 6) F4 :=
  (Units.map (diagonalRingHom (Fin 6) F4).toMonoidHom).comp MulEquiv.piUnits.symm.toMonoidHom

theorem coe_dgl (d : Fin 6 → F4ˣ) :
    (dgl d : Matrix (Fin 6) (Fin 6) F4) = diagonal fun i => (d i : F4) :=
  rfl

theorem dgl_apply (d : Fin 6 → F4ˣ) (i j : Fin 6) :
    (dgl d : Matrix (Fin 6) (Fin 6) F4) i j = if i = j then (d i : F4) else 0 := by
  rw [coe_dgl, diagonal_apply]

theorem dgl_injective : Function.Injective dgl := by
  intro d e h
  funext i
  apply Units.ext
  have := congrArg (fun g : GL (Fin 6) F4 => (g : Matrix (Fin 6) (Fin 6) F4) i i) h
  simpa [dgl_apply] using this

theorem scalar_eq_dgl (c : F4ˣ) :
    GeneralLinearGroup.scalar (Fin 6) c = dgl (fun _ => c) := by
  apply Units.ext
  rw [GeneralLinearGroup.coe_scalar, scalar_apply, coe_dgl]

@[expose] noncomputable def pgl : Equiv.Perm (Fin 6) →* GL (Fin 6) F4 :=
  (permMatrixHom : Equiv.Perm (Fin 6) →* Matrix (Fin 6) (Fin 6) F4).toHomUnits

theorem pgl_apply (σ : Equiv.Perm (Fin 6)) (i j : Fin 6) :
    (pgl σ : Matrix (Fin 6) (Fin 6) F4) i j = if σ⁻¹ i = j then 1 else 0 := by
  simp [pgl, permMatrixHom_apply, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply,
    Equiv.toPEquiv_apply]

theorem u62_permMatrix_mul_diagonal_mul (τ : Equiv.Perm (Fin 6)) (d : Fin 6 → F4) :
    (τ.permMatrix F4) * diagonal d * (τ⁻¹.permMatrix F4) = diagonal (fun i => d (τ i)) := by
  ext i l
  rw [Matrix.mul_apply, Finset.sum_eq_single (τ i)]
  · simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Matrix.mul_diagonal,
      Matrix.diagonal_apply]
  · intro k _ hk
    simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Matrix.mul_diagonal,
      Ne.symm hk]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem pgl_mul_dgl_mul_inv (σ : Equiv.Perm (Fin 6)) (d : Fin 6 → F4ˣ) :
    pgl σ * dgl d * (pgl σ)⁻¹ = dgl (fun j => d (σ⁻¹ j)) := by
  rw [← map_inv pgl σ]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_dgl]
  exact u62_permMatrix_mul_diagonal_mul σ⁻¹ (fun j => (d j : F4))

abbrev S6 : Type := gramSU uData M6

noncomputable abbrev mk6 : S6 →* P6 := QuotientGroup.mk' (normOneScalars uData (gramSU uData M6) 6)

@[expose] def diagSU : Subgroup (Fin 6 → F4ˣ) where
  carrier := {d | ∏ i, d i = 1}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq, Pi.mul_apply, Finset.prod_mul_distrib] at ha hb ⊢
    simp [ha, hb]
  one_mem' := by simp
  inv_mem' {a} ha := by
    simp only [Set.mem_setOf_eq, Pi.inv_apply, Finset.prod_inv_distrib] at ha ⊢
    simp [ha]

theorem mem_diagSU {d : Fin 6 → F4ˣ} : d ∈ diagSU ↔ ∏ i, d i = 1 :=
  Iff.rfl

theorem u62_units_pow_three (c : F4ˣ) : c ^ 3 = 1 :=
  Units.ext (by rw [Units.val_pow_eq_pow_val, pow_three_F4 c.ne_zero, Units.val_one])

theorem dgl_mem_gramSU {d : Fin 6 → F4ˣ} (hd : d ∈ diagSU) : dgl d ∈ gramSU uData M6 := by
  refine ⟨?_, ?_⟩
  · rw [coe_dgl, Matrix.diagonal_map (map_zero _), diagonal_transpose, M6_eq_one, Matrix.mul_one,
      diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    rw [UnitaryFieldData.bar_apply]
    calc ((d i : F4ˣ) : F4) ^ 2 ^ 1 * (d i : F4ˣ) = ((d i : F4ˣ) : F4) ^ 3 := by ring
      _ = 1 := pow_three_F4 (d i).ne_zero
  · rw [coe_dgl, det_diagonal, ← Units.coe_prod, mem_diagSU.mp hd, Units.val_one]

theorem u62_sign_cast (τ : Equiv.Perm (Fin 6)) : (((Equiv.Perm.sign τ : ℤˣ) : ℤ) : F4) = 1 := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign τ) with h | h
  · rw [h]
    simp
  · rw [h]
    simp only [Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one]
    linear_combination (-1 : F4) * two_eq_zero_F4

theorem pgl_transpose_mul (σ : Equiv.Perm (Fin 6)) :
    ((pgl σ : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4)ᵀ *
      ((pgl σ : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) = 1 := by
  have h : (permMatrixHom σ⁻¹ : Matrix (Fin 6) (Fin 6) F4) * permMatrixHom σ = 1 := by
    rw [← map_mul, inv_mul_cancel, map_one]
  change ((σ⁻¹).permMatrix F4)ᵀ * (σ⁻¹).permMatrix F4 = 1
  rw [Matrix.transpose_permMatrix, inv_inv]
  simpa [permMatrixHom_apply, inv_inv] using h

theorem pgl_mem_gramSU (σ : Equiv.Perm (Fin 6)) : pgl σ ∈ gramSU uData M6 := by
  refine ⟨?_, ?_⟩
  · have hmap : ((pgl σ : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4).map uData.bar =
        ((pgl σ : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) := by
      ext i j
      rw [Matrix.map_apply, pgl_apply]
      split_ifs <;> simp
    rw [hmap, M6_eq_one, Matrix.mul_one]
    exact pgl_transpose_mul σ
  · change Matrix.det ((σ⁻¹).permMatrix F4) = 1
    rw [Matrix.det_permutation]
    exact u62_sign_cast _

@[expose] noncomputable def diagS6 : diagSU →* S6 :=
  (dgl.comp diagSU.subtype).codRestrict _ fun d => dgl_mem_gramSU d.2

@[expose] noncomputable def permS6 : Equiv.Perm (Fin 6) →* S6 :=
  pgl.codRestrict _ pgl_mem_gramSU

@[expose] noncomputable def diagP6 : diagSU →* P6 :=
  mk6.comp diagS6

@[expose] noncomputable def permP6 : Equiv.Perm (Fin 6) →* P6 :=
  mk6.comp permS6

theorem coe_diagS6 (d : diagSU) : ((diagS6 d : S6) : GL (Fin 6) F4) = dgl d.1 :=
  rfl

theorem mk_eq_mk_iff6 (g h : S6) :
    mk6 g = mk6 h ↔ ∃ c : F4ˣ, (g : GL (Fin 6) F4) =
        GeneralLinearGroup.scalar (Fin 6) c * (h : GL (Fin 6) F4) := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
  constructor
  · rintro ⟨c, -, -, hc⟩
    refine ⟨c⁻¹, ?_⟩
    have h1 : (h : GL (Fin 6) F4) = (g : GL (Fin 6) F4) * GeneralLinearGroup.scalar (Fin 6) c := by
      have : ((g⁻¹ * h : S6) : GL (Fin 6) F4) = (g : GL (Fin 6) F4)⁻¹ * h := rfl
      rw [this] at hc
      rw [← hc]
      group
    rw [h1, map_inv, (commute_scalar c (g : GL (Fin 6) F4)).eq, inv_mul_cancel_left]
  · rintro ⟨c, hc⟩
    refine ⟨c⁻¹, norm_eq_one _, ?_, ?_⟩
    · rw [inv_pow, show (6 : ℕ) = 3 * 2 from rfl, pow_mul, u62_units_pow_three c, one_pow, inv_one]
    · have : ((g⁻¹ * h : S6) : GL (Fin 6) F4) = (g : GL (Fin 6) F4)⁻¹ * h := rfl
      have hcomm : (GeneralLinearGroup.scalar (Fin 6) c)⁻¹ * (h : GL (Fin 6) F4) =
          (h : GL (Fin 6) F4) * (GeneralLinearGroup.scalar (Fin 6) c)⁻¹ := by
        rw [← map_inv]
        exact (commute_scalar c⁻¹ _).eq.symm
      rw [this, hc, _root_.mul_inv_rev, map_inv, mul_assoc, hcomm, inv_mul_cancel_left]

theorem diagP6_eq_iff (d e : diagSU) :
    diagP6 d = diagP6 e ↔ ∃ c : F4ˣ, ∀ i, d.1 i = c * e.1 i := by
  change mk6 (diagS6 d) = mk6 (diagS6 e) ↔ _
  rw [mk_eq_mk_iff6]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c, fun i => ?_⟩
    rw [coe_diagS6, coe_diagS6, scalar_eq_dgl, ← map_mul] at hc
    exact congrFun (dgl_injective hc) i
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_⟩
    rw [coe_diagS6, coe_diagS6, scalar_eq_dgl, ← map_mul]
    congr 1
    funext i
    exact hc i

@[expose] def permAct (σ : Equiv.Perm (Fin 6)) (d : diagSU) : diagSU :=
  ⟨fun i => d.1 (σ⁻¹ i), by
    rw [mem_diagSU]
    exact (Equiv.prod_comp σ⁻¹ d.1).trans (mem_diagSU.mp d.2)⟩

theorem permP6_mul_diagP6 (σ : Equiv.Perm (Fin 6)) (d : diagSU) :
    permP6 σ * diagP6 d * (permP6 σ)⁻¹ = diagP6 (permAct σ d) := by
  have h : permS6 σ * diagS6 d * (permS6 σ)⁻¹ = diagS6 (permAct σ d) :=
    Subtype.ext (pgl_mul_dgl_mul_inv σ d.1)
  change mk6 (permS6 σ) * mk6 (diagS6 d) * (mk6 (permS6 σ))⁻¹ = mk6 (diagS6 (permAct σ d))
  rw [← map_inv, ← map_mul, ← map_mul, h]

@[expose] def cyc1 : Equiv.Perm (Fin 6) :=
  ⟨![1, 2, 0, 3, 4, 5], ![2, 0, 1, 3, 4, 5], by decide, by decide⟩

@[expose] def cyc2 : Equiv.Perm (Fin 6) :=
  ⟨![0, 1, 2, 4, 5, 3], ![0, 1, 2, 5, 3, 4], by decide, by decide⟩

theorem cyc1_pow_three : cyc1 ^ 3 = 1 := by decide

theorem cyc2_pow_three : cyc2 ^ 3 = 1 := by decide

theorem cyc1_mul_cyc2 : cyc1 * cyc2 = cyc2 * cyc1 := by decide

theorem exists_omega6 : ∃ ω : F4ˣ, ω ≠ 1 := by
  have : Nontrivial F4ˣ := Finite.one_lt_card_iff_nontrivial.mp (by rw [card_units_F4]; norm_num)
  exact exists_ne 1

theorem u62_omega_sq {ω : F4ˣ} (hω : ω ≠ 1) : (ω : F4) ^ 2 + ω + 1 = 0 := by
  have h3 : (ω : F4) ^ 3 = 1 := pow_three_F4 ω.ne_zero
  have h1 : (ω : F4) ≠ 1 := fun h => hω (Units.ext h)
  have : ((ω : F4) - 1) * ((ω : F4) ^ 2 + ω + 1) = 0 := by linear_combination h3
  exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr h1)

@[expose] noncomputable def testD (ω : F4ˣ) (i k : Fin 6) : Fin 6 → F4ˣ :=
  fun l => (if l = i then ω else 1) * (if l = k then ω ^ 2 else 1)

theorem testD_mem (ω : F4ˣ) (i k : Fin 6) : testD ω i k ∈ diagSU := by
  rw [mem_diagSU]
  unfold testD
  rw [Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.prod_ite_eq', if_pos (Finset.mem_univ _),
    if_pos (Finset.mem_univ _), ← pow_succ']
  exact u62_units_pow_three ω

theorem trace_testD {ω : F4ˣ} (hω : ω ≠ 1) {i k : Fin 6} (hik : i ≠ k) :
    ∑ l, ((testD ω i k l : F4ˣ) : F4) = 1 := by
  have hq := u62_omega_sq hω
  have h : ∀ l, ((testD ω i k l : F4ˣ) : F4) =
      1 + (if l = i then (ω : F4) - 1 else 0) + (if l = k then (ω : F4) ^ 2 - 1 else 0) := by
    intro l
    by_cases h1 : l = i
    · subst h1
      simp [testD, hik]
    · by_cases h2 : l = k
      · subst h2
        simp [testD, h1]
      · simp [testD, h1, h2]
  simp only [h, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, nsmul_eq_mul]
  push_cast
  linear_combination hq + two_eq_zero_F4

theorem u62_offdiag {X : GL (Fin 6) F4}
    (h1 : ∀ d ∈ diagSU, ∃ c : F4ˣ,
      X * dgl d = GeneralLinearGroup.scalar (Fin 6) c * (dgl d * X))
    {i j : Fin 6} (hij : i ≠ j) : (X : Matrix (Fin 6) (Fin 6) F4) i j = 0 := by
  obtain ⟨ω, hω⟩ := exists_omega6
  obtain ⟨k, hki⟩ := exists_ne i
  obtain ⟨c, hc⟩ := h1 (testD ω i k) (testD_mem ω i k)
  have hmat : (X : Matrix (Fin 6) (Fin 6) F4) * diagonal (fun l => ((testD ω i k l : F4ˣ) : F4)) =
      (c : F4) • (diagonal (fun l => ((testD ω i k l : F4ˣ) : F4)) *
        (X : Matrix (Fin 6) (Fin 6) F4)) := by
    have := congrArg (fun g : GL (Fin 6) F4 => (g : Matrix (Fin 6) (Fin 6) F4)) hc
    simpa [Units.val_mul, GeneralLinearGroup.coe_scalar, scalar_apply, smul_eq_diagonal_mul,
      coe_dgl] using this
  set D : Matrix (Fin 6) (Fin 6) F4 := diagonal (fun l => ((testD ω i k l : F4ˣ) : F4)) with hD
  have h2 : (X : Matrix (Fin 6) (Fin 6) F4) * D *
      ((X⁻¹ : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) = (c : F4) • D := by
    rw [hmat, Matrix.smul_mul, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.mul_one]
  have h3 := Matrix.trace_units_conj X D
  rw [h2, Matrix.trace_smul, smul_eq_mul, hD, Matrix.trace_diagonal,
    trace_testD hω hki.symm] at h3
  have hc1 : (c : F4) = 1 := by simpa using h3
  rw [hc1, one_smul] at hmat
  have hent := congrFun (congrFun hmat i) j
  rw [hD] at hent
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul] at hent
  have hfi : ((testD ω i k i : F4ˣ) : F4) = ω := by simp [testD, hki.symm]
  have hω1 : (ω : F4) ≠ 1 := fun h => hω (Units.ext h)
  have hfj : ((testD ω i k j : F4ˣ) : F4) ≠ ω := by
    by_cases hjk : j = k
    · have : ((testD ω i k j : F4ˣ) : F4) = (ω : F4) ^ 2 := by
        subst hjk
        simp [testD, hki]
      rw [this]
      intro h
      have h0 : (ω : F4) * ((ω : F4) - 1) = 0 := by linear_combination h
      rcases mul_eq_zero.mp h0 with h4 | h4
      · exact ω.ne_zero h4
      · exact hω1 (sub_eq_zero.mp h4)
    · have : ((testD ω i k j : F4ˣ) : F4) = 1 := by simp [testD, hij.symm, hjk]
      rw [this]
      exact fun h => hω1 h.symm
  rw [hfi] at hent
  have hmul : (X : Matrix (Fin 6) (Fin 6) F4) i j * (((testD ω i k j : F4ˣ) : F4) - ω) = 0 := by
    linear_combination hent
  exact (mul_eq_zero.mp hmul).resolve_right (sub_ne_zero.mpr hfj)

theorem u62_rel {β : Fin 6 → F4ˣ} {π : Equiv.Perm (Fin 6)} {c : F4ˣ}
    (h : dgl β * pgl π = GeneralLinearGroup.scalar (Fin 6) c * (pgl π * dgl β)) (i : Fin 6) :
    β i = c * β (π⁻¹ i) := by
  have h1 := congrArg (fun g : GL (Fin 6) F4 => (g : Matrix (Fin 6) (Fin 6) F4) i (π⁻¹ i)) h
  apply Units.ext
  simpa [Units.val_mul, GeneralLinearGroup.coe_scalar, scalar_apply, coe_dgl, pgl_apply,
    Matrix.diagonal_mul, Matrix.mul_diagonal] using h1

theorem u62_diag_block {X : GL (Fin 6) F4}
    (h1 : ∀ d ∈ diagSU, ∃ c : F4ˣ,
      X * dgl d = GeneralLinearGroup.scalar (Fin 6) c * (dgl d * X))
    (h2 : ∃ c : F4ˣ, X * pgl cyc1 = GeneralLinearGroup.scalar (Fin 6) c * (pgl cyc1 * X))
    (h3 : ∃ c : F4ˣ, X * pgl cyc2 = GeneralLinearGroup.scalar (Fin 6) c * (pgl cyc2 * X)) :
    ∃ a b : F4ˣ, X = dgl ![a, a, a, b, b, b] := by
  have hoff : ∀ i j, i ≠ j → (X : Matrix (Fin 6) (Fin 6) F4) i j = 0 :=
    fun i j h => u62_offdiag h1 h
  have hdiag : (X : Matrix (Fin 6) (Fin 6) F4) =
      diagonal fun i => (X : Matrix (Fin 6) (Fin 6) F4) i i := by
    ext i j
    by_cases h : i = j
    · subst h
      simp
    · rw [hoff i j h, diagonal_apply_ne _ h]
  have hdet : (X : Matrix (Fin 6) (Fin 6) F4).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp X.isUnit).ne_zero
  have hne : ∀ i, (X : Matrix (Fin 6) (Fin 6) F4) i i ≠ 0 := by
    intro i hi
    apply hdet
    rw [hdiag, det_diagonal]
    exact Finset.prod_eq_zero (Finset.mem_univ i) hi
  obtain ⟨β, hβ⟩ : ∃ β : Fin 6 → F4ˣ, X = dgl β :=
    ⟨fun i => Units.mk0 _ (hne i), Units.ext (by rw [coe_dgl]; exact hdiag)⟩
  obtain ⟨c, hc⟩ := h2
  obtain ⟨c', hc'⟩ := h3
  subst hβ
  have r1 := u62_rel hc
  have r2 := u62_rel hc'
  have i1 : cyc1⁻¹ 3 = 3 := by decide
  have i2 : cyc1⁻¹ 0 = 2 := by decide
  have i3 : cyc1⁻¹ 1 = 0 := by decide
  have j1 : cyc2⁻¹ 0 = 0 := by decide
  have j2 : cyc2⁻¹ 3 = 5 := by decide
  have j3 : cyc2⁻¹ 4 = 3 := by decide
  have e3 := r1 3
  rw [i1] at e3
  have hc1 : c = 1 := mul_right_cancel (b := β 3) (by rw [one_mul]; exact e3.symm)
  have e0 := r1 0
  have e1 := r1 1
  rw [i2, hc1, one_mul] at e0
  rw [i3, hc1, one_mul] at e1
  have f0 := r2 0
  rw [j1] at f0
  have hc2 : c' = 1 := mul_right_cancel (b := β 0) (by rw [one_mul]; exact f0.symm)
  have f3 := r2 3
  have f4 := r2 4
  rw [j2, hc2, one_mul] at f3
  rw [j3, hc2, one_mul] at f4
  refine ⟨β 0, β 3, ?_⟩
  congr 1
  funext i
  fin_cases i
  · rfl
  · exact e1
  · exact e0.symm
  · rfl
  · exact f4
  · exact f3.symm

end CFSG.RankThree.PartTwo.Sec4.RonanK432
