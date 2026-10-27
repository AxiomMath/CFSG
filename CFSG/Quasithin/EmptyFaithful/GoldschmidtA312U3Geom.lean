module

public import CFSG.ClassicalGroups.UnitaryFlag.GroupData

public section

namespace CFSG.Quasithin.A312U3

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag

variable {p f : ℕ} {F : Type} [Field F]

section Diag

variable (F)

@[expose] def dsign (k : Fin 3) : Matrix (Fin 3) (Fin 3) F :=
  Matrix.diagonal fun i => if i = k then 1 else -1

theorem dsign_mul_self (k : Fin 3) : dsign F k * dsign F k = 1 := by
  rw [dsign, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  by_cases h : i = k <;> simp [h]

theorem det_dsign (k : Fin 3) : (dsign F k).det = 1 := by
  fin_cases k <;> simp [dsign, Matrix.det_diagonal, Fin.prod_univ_three]

@[expose] def dsignGL (k : Fin 3) : GL (Fin 3) F :=
  ⟨dsign F k, dsign F k, dsign_mul_self F k, dsign_mul_self F k⟩

@[simp] theorem coe_dsignGL (k : Fin 3) :
    ((dsignGL F k : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = dsign F k := rfl

variable {F}

theorem dsignGL_mem (h : UnitaryFieldData p f F) (k : Fin 3) : dsignGL F k ∈ unitarySU p f F 3 := by
  rw [mem_unitarySU_iff h]
  refine ⟨det_dsign F k, ?_⟩
  have : ((dsign F k).map h.bar) = dsign F k := by
    ext i j
    by_cases hij : i = j
    · subst hij
      by_cases hik : i = k <;> simp [dsign, Matrix.diagonal, hik]
    · simp [dsign, Matrix.diagonal, hij]
  have hs : (dsign F k)ᵀ = dsign F k := Matrix.diagonal_transpose _
  rw [coe_dsignGL, this, hs, dsign_mul_self]

end Diag

section Coord

theorem coe_inv_eq_conjTr (h : UnitaryFieldData p f F) {g : GL (Fin 3) F}
    (hg : ((g : Matrix (Fin 3) (Fin 3) F).map h.bar)ᵀ * (g : Matrix (Fin 3) (Fin 3) F) = 1) :
    ((g⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      ((g : Matrix (Fin 3) (Fin 3) F).map h.bar)ᵀ := by
  rw [Matrix.coe_units_inv]
  exact Matrix.inv_eq_left_inv hg

theorem coord_mem (h2 : (2 : F) ≠ 0) {M : Subgroup (GL (Fin 3) F)} (hd : ∀ k, dsignGL F k ∈ M)
    {W : Submodule F (Fin 3 → F)}
    (hW : ∀ g ∈ M, ∀ w ∈ W, (g : Matrix (Fin 3) (Fin 3) F) *ᵥ w ∈ W)
    {w : Fin 3 → F} (hw : w ∈ W) (k : Fin 3) : Pi.single k (w k) ∈ W := by
  have h1 := hW _ (hd k) w hw
  have h3 : (2 : F)⁻¹ • (dsign F k *ᵥ w + w) = Pi.single k (w k) := by
    funext i
    by_cases hik : i = k
    · subst hik
      simp [dsign, Matrix.mulVec_diagonal]
      field_simp
      ring
    · simp [dsign, Matrix.mulVec_diagonal, hik]
  rw [← h3]
  exact W.smul_mem _ (W.add_mem h1 hw)

end Coord

section Block

theorem exists_block (h : UnitaryFieldData p f F) (h2 : (2 : F) ≠ 0)
    {M : Subgroup (GL (Fin 3) F)}
    (hM : ∀ g ∈ M,
      ((g : Matrix (Fin 3) (Fin 3) F).map h.bar)ᵀ * (g : Matrix (Fin 3) (Fin 3) F) = 1)
    (hd : ∀ k, dsignGL F k ∈ M) {W : Submodule F (Fin 3 → F)}
    (hW : ∀ g ∈ M, ∀ w ∈ W, (g : Matrix (Fin 3) (Fin 3) F) *ᵥ w ∈ W) (hbot : W ≠ ⊥)
    (htop : W ≠ ⊤) :
    ∃ k : Fin 3, ∀ g ∈ M, ∀ i, i ≠ k →
      (g : Matrix (Fin 3) (Fin 3) F) i k = 0 ∧ (g : Matrix (Fin 3) (Fin 3) F) k i = 0 := by
  classical
  set T : Finset (Fin 3) :=
    Finset.univ.filter fun i => (Pi.single i (1 : F) : Fin 3 → F) ∈ W with hTdef
  have hmemT : ∀ i, i ∈ T ↔ (Pi.single i (1 : F) : Fin 3 → F) ∈ W := fun i => by simp [hTdef]
  have hT0 : ∀ w ∈ W, ∀ i, i ∉ T → w i = 0 := by
    intro w hw i hi
    by_contra hne
    apply hi
    rw [hmemT]
    have h3 : (w i)⁻¹ • (Pi.single i (w i) : Fin 3 → F) = Pi.single i 1 := by
      funext j
      by_cases hj : j = i
      · subst hj
        simp [hne]
      · simp [hj]
    rw [← h3]
    exact W.smul_mem _ (coord_mem h2 hd hW hw i)
  have hne : T.Nonempty := by
    by_contra hempty
    rw [Finset.not_nonempty_iff_eq_empty] at hempty
    apply hbot
    rw [Submodule.eq_bot_iff]
    intro w hw
    funext i
    exact hT0 w hw i (by simp [hempty])
  have hnu : T ≠ Finset.univ := by
    intro hu
    apply htop
    rw [eq_top_iff]
    intro v _
    have hv : v = ∑ i, v i • (Pi.single i (1 : F) : Fin 3 → F) := by
      funext j
      simp [Finset.sum_apply, Pi.single_apply]
    rw [hv]
    exact W.sum_mem fun i _ => W.smul_mem _ ((hmemT i).mp (hu ▸ Finset.mem_univ i))
  have hblock : ∀ g ∈ M, ∀ i ∈ T, ∀ i' ∉ T,
      (g : Matrix (Fin 3) (Fin 3) F) i' i = 0 ∧ (g : Matrix (Fin 3) (Fin 3) F) i i' = 0 := by
    intro g hg i hi i' hi'
    refine ⟨?_, ?_⟩
    · have := hT0 _ (hW g hg _ ((hmemT i).mp hi)) i' hi'
      simpa [Matrix.mulVec_single] using this
    · have hginv := hW (g⁻¹) (M.inv_mem hg) _ ((hmemT i).mp hi)
      have h4 := hT0 _ hginv i' hi'
      rw [Matrix.mulVec_single, coe_inv_eq_conjTr h (hM g hg)] at h4
      simpa using h4
  have hcard : T.card = 1 ∨ T.card = 2 := by
    have h1 : 0 < T.card := hne.card_pos
    have h2' : T.card < 3 := by
      have := Finset.card_lt_card (Finset.ssubset_univ_iff.mpr hnu)
      simpa using this
    omega
  rcases hcard with h1 | h2'
  · obtain ⟨k, hk⟩ := Finset.card_eq_one.mp h1
    refine ⟨k, fun g hg i hik => ?_⟩
    have hkT : k ∈ T := by rw [hk]; simp
    have hiT : i ∉ T := by rw [hk]; simpa using hik
    exact hblock g hg k hkT i hiT
  · have hc : Tᶜ.card = 1 := by
      rw [Finset.card_compl, h2']
      rfl
    obtain ⟨k, hk⟩ := Finset.card_eq_one.mp hc
    refine ⟨k, fun g hg i hik => ?_⟩
    have hkT : k ∉ T := by
      have : k ∈ Tᶜ := by rw [hk]; simp
      simpa using this
    have hiT : i ∈ T := by
      by_contra hi'
      have : i ∈ Tᶜ := by simpa using hi'
      rw [hk] at this
      exact hik (Finset.mem_singleton.mp this)
    exact (hblock g hg i hiT k hkT).symm

theorem commute_dsign_of_block {g : Matrix (Fin 3) (Fin 3) F} {k : Fin 3}
    (hg : ∀ i, i ≠ k → g i k = 0 ∧ g k i = 0) : g * dsign F k = dsign F k * g := by
  ext i j
  simp only [dsign, Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hi : i = k <;> by_cases hj : j = k
  · simp [hi, hj]
  · obtain rfl : i = k := hi
    have := (hg j hj).2
    simp [hj, this]
  · obtain rfl : j = k := hj
    have := (hg i hi).1
    simp [hi, this]
  · simp [hi, hj, mul_comm]

theorem exists_central_dsign (h : UnitaryFieldData p f F) (h2 : (2 : F) ≠ 0)
    {M : Subgroup (GL (Fin 3) F)}
    (hM : ∀ g ∈ M,
      ((g : Matrix (Fin 3) (Fin 3) F).map h.bar)ᵀ * (g : Matrix (Fin 3) (Fin 3) F) = 1)
    (hd : ∀ k, dsignGL F k ∈ M) {W : Submodule F (Fin 3 → F)}
    (hW : ∀ g ∈ M, ∀ w ∈ W, (g : Matrix (Fin 3) (Fin 3) F) *ᵥ w ∈ W) (hbot : W ≠ ⊥)
    (htop : W ≠ ⊤) :
    ∃ k : Fin 3, dsignGL F k ∈ M ∧ ∀ g ∈ M, g * dsignGL F k = dsignGL F k * g := by
  obtain ⟨k, hk⟩ := exists_block h h2 hM hd hW hbot htop
  refine ⟨k, hd k, fun g hg => Units.ext ?_⟩
  rw [Units.val_mul, Units.val_mul, coe_dsignGL]
  exact commute_dsign_of_block (hk g hg)

end Block

end CFSG.Quasithin.A312U3
