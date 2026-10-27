module

public import CFSG.Open.StatedDefs

public section

namespace CFSG.Quasithin

open CFSG.Open Matrix

namespace F918V3T3

theorem three_dvd_card_of_cube {G : Type*} [Group G] (H : Subgroup G) {x : G} (hx : x ∈ H)
    (h3 : x ^ 3 = 1) (h1 : x ≠ 1) : 3 ∣ Nat.card H := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hx3 : (⟨x, hx⟩ : H) ^ 3 = 1 := Subtype.ext h3
  have hx1 : (⟨x, hx⟩ : H) ≠ 1 := fun h => h1 (congrArg Subtype.val h)
  rw [← orderOf_eq_prime hx3 hx1]
  exact orderOf_dvd_natCard _

theorem three_dvd_card_of_card_eq {G : Type*} [Group G] (H : Subgroup G) {k : ℕ} (hk : 1 ≤ k)
    (h : Nat.card H = 3 ^ k) : 3 ∣ Nat.card G :=
  (dvd_pow_self 3 (by omega)).trans (h ▸ Subgroup.card_subgroup_dvd_card H)

section Proj

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]

theorem three_dvd_card_statedProj {H : Subgroup (GL ι K)} {g : GL ι K} (hgH : g ∈ H)
    (hg3 : g ^ 3 = 1) (hgs : g ∉ StatedScalars ι K) : 3 ∣ Nat.card (StatedProj H) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hx3 : (QuotientGroup.mk (⟨g, hgH⟩ : H) : StatedProj H) ^ 3 = 1 := by
    rw [← QuotientGroup.mk_pow, ← QuotientGroup.mk_one]
    congr 1
    exact Subtype.ext hg3
  have hx1 : (QuotientGroup.mk (⟨g, hgH⟩ : H) : StatedProj H) ≠ 1 := by
    intro h
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h
    exact hgs h
  rw [← orderOf_eq_prime hx3 hx1]
  exact orderOf_dvd_natCard _

end Proj

section ThreeCycle

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]

@[expose] noncomputable def permGL (K : Type) [Field K] (σ : Equiv.Perm ι) : GL ι K :=
  (Matrix.permMatrixHom (R := K)).toHomUnits σ

theorem coe_permGL (σ : Equiv.Perm ι) :
    (permGL K σ : Matrix ι ι K) = (σ⁻¹).permMatrix K := rfl

theorem permGL_pow_three {σ : Equiv.Perm ι} (h : σ.IsThreeCycle) : permGL K σ ^ 3 = 1 := by
  have : σ ^ 3 = 1 := by rw [← h.orderOf]; exact pow_orderOf_eq_one σ
  rw [permGL, ← map_pow, this, map_one]

theorem det_permGL {σ : Equiv.Perm ι} (h : σ.IsThreeCycle) :
    (permGL K σ : Matrix ι ι K).det = 1 := by
  rw [coe_permGL, Matrix.det_permutation, Equiv.Perm.sign_inv, h.sign]
  simp

theorem permGL_not_mem_scalars {σ : Equiv.Perm ι} {a : ι} (ha : σ a ≠ a) :
    permGL K σ ∉ StatedScalars ι K := by
  rintro ⟨c, hc⟩
  have h := congrArg (fun g : GL ι K => (g : Matrix ι ι K) a a) hc
  have h1 : σ.symm a ≠ a := fun h' => ha (by simpa using (congrArg σ h').symm)
  simp [coe_permGL, Matrix.GeneralLinearGroup.coe_scalar, PEquiv.toMatrix_apply,
    Equiv.toPEquiv_apply, h1] at h

theorem exists_threeCycle_fin {n : ℕ} (hn : 3 ≤ n) :
    ∃ σ : Equiv.Perm (Fin n), σ.IsThreeCycle ∧ ∃ a : Fin n, σ a ≠ a := by
  have hab : (⟨0, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ := fun h => by simpa using congrArg Fin.val h
  have hac : (⟨0, by omega⟩ : Fin n) ≠ ⟨2, by omega⟩ := fun h => by simpa using congrArg Fin.val h
  have hbc : (⟨1, by omega⟩ : Fin n) ≠ ⟨2, by omega⟩ := fun h => by simpa using congrArg Fin.val h
  refine ⟨Equiv.swap ⟨0, by omega⟩ ⟨1, by omega⟩ * Equiv.swap ⟨0, by omega⟩ ⟨2, by omega⟩,
    Equiv.Perm.isThreeCycle_swap_mul_swap_same hab hac hbc, ⟨0, by omega⟩, ?_⟩
  rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hac.symm hbc.symm]
  exact hac.symm

theorem three_dvd_card_PSL_of_three_le {n : ℕ} (hn : 3 ≤ n) {K : Type} [Field K] :
    3 ∣ Nat.card (StatedProj (StatedSL n K)) := by
  obtain ⟨σ, h3, a, ha⟩ := exists_threeCycle_fin hn
  exact three_dvd_card_statedProj (g := permGL K σ) (Subgroup.subset_closure (det_permGL h3))
    (permGL_pow_three h3) (permGL_not_mem_scalars ha)

theorem three_dvd_card_PSU_of_three_le {n q : ℕ} (hn : 3 ≤ n) (hq : q ≠ 0) {K : Type} [Field K] :
    3 ∣ Nat.card (StatedProj (StatedSU n q K)) := by
  obtain ⟨σ, h3, a, ha⟩ := exists_threeCycle_fin hn
  have hmap : (permGL K σ : Matrix (Fin n) (Fin n) K).map (· ^ q) =
      (permGL K σ : Matrix (Fin n) (Fin n) K) := by
    ext i j
    simp only [Matrix.map_apply, coe_permGL, PEquiv.toMatrix_apply]
    split_ifs <;> simp [hq]
  refine three_dvd_card_statedProj (g := permGL K σ) (Subgroup.subset_closure ⟨det_permGL h3, ?_⟩)
    (permGL_pow_three h3) (permGL_not_mem_scalars ha)
  rw [hmap, coe_permGL, Matrix.transpose_permMatrix, inv_inv, ← Matrix.permMatrix_mul,
    inv_mul_cancel, Matrix.permMatrix_one]

end ThreeCycle

section Two

variable {K : Type} [Field K]

@[expose] def comp3 (K : Type) [Field K] : Matrix (Fin 2) (Fin 2) K := !![0, -1; 1, -1]

@[expose] def comp3Inv (K : Type) [Field K] : Matrix (Fin 2) (Fin 2) K := !![-1, -1; 1, 0]

theorem comp3_mul_cube : comp3 K * comp3 K * comp3 K = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [comp3, Matrix.mul_apply, Fin.sum_univ_two]

theorem comp3Inv_mul_cube : comp3Inv K * comp3Inv K * comp3Inv K = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [comp3Inv, Matrix.mul_apply, Fin.sum_univ_two]

@[expose] def comp3GL (K : Type) [Field K] : GL (Fin 2) K :=
  ⟨comp3 K, comp3 K * comp3 K, by rw [← mul_assoc]; exact comp3_mul_cube,
    comp3_mul_cube⟩

theorem comp3GL_pow_three : comp3GL K ^ 3 = 1 := by
  ext1
  simp only [Units.val_one, pow_succ, pow_zero, one_mul]
  exact comp3_mul_cube

theorem det_comp3 : (comp3 K).det = 1 := by
  simp [comp3, Matrix.det_fin_two_of]

theorem three_dvd_card_PSL_two {K : Type} [Field K] :
    3 ∣ Nat.card (StatedProj (StatedSL 2 K)) := by
  refine three_dvd_card_statedProj (g := comp3GL K) (Subgroup.subset_closure det_comp3)
    comp3GL_pow_three ?_
  rintro ⟨c, hc⟩
  have h := congrArg (fun g : GL (Fin 2) K => (g : Matrix (Fin 2) (Fin 2) K) 0 1) hc
  simp [Matrix.GeneralLinearGroup.coe_scalar, comp3GL, comp3] at h

end Two

section Symplectic

variable {K : Type} [Field K]

@[expose] def sp4Elt (K : Type) [Field K] : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K :=
  Matrix.fromBlocks (comp3 K) 0 0 (comp3Inv K)

theorem sp4Elt_cube : sp4Elt K * sp4Elt K * sp4Elt K = 1 := by
  simp only [sp4Elt, Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero,
    zero_add, comp3_mul_cube, comp3Inv_mul_cube, Matrix.fromBlocks_one]

theorem comp3_transpose_mul : (comp3 K)ᵀ * comp3Inv K = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [comp3, comp3Inv, Matrix.mul_apply, Fin.sum_univ_two]

theorem comp3Inv_transpose_mul : (comp3Inv K)ᵀ * comp3 K = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [comp3, comp3Inv, Matrix.mul_apply, Fin.sum_univ_two]

@[expose] def sp4GL (K : Type) [Field K] : GL (Fin 2 ⊕ Fin 2) K :=
  ⟨sp4Elt K, sp4Elt K * sp4Elt K, by rw [← mul_assoc]; exact sp4Elt_cube, sp4Elt_cube⟩

theorem sp4GL_pow_three : sp4GL K ^ 3 = 1 := by
  ext1
  simp only [Units.val_one, pow_succ, pow_zero, one_mul]
  exact sp4Elt_cube

theorem sp4Elt_symplectic :
    (sp4Elt K)ᵀ * Matrix.fromBlocks 0 1 (-1) 0 * sp4Elt K = Matrix.fromBlocks 0 1 (-1) 0 := by
  simp only [sp4Elt, Matrix.fromBlocks_transpose, Matrix.transpose_zero,
    Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
    Matrix.mul_one, Matrix.mul_neg, Matrix.neg_mul, zero_add, neg_zero,
    comp3_transpose_mul, comp3Inv_transpose_mul]

theorem three_dvd_card_PSp_two {K : Type} [Field K] :
    3 ∣ Nat.card (StatedProj (StatedSp 2 K)) := by
  refine three_dvd_card_statedProj (g := sp4GL K) (Subgroup.subset_closure sp4Elt_symplectic)
    sp4GL_pow_three ?_
  rintro ⟨c, hc⟩
  have h := congrArg
    (fun g : GL (Fin 2 ⊕ Fin 2) K => (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)
      (Sum.inl 0) (Sum.inl 0)) hc
  simp [Matrix.GeneralLinearGroup.coe_scalar, sp4GL, sp4Elt, comp3] at h

end Symplectic

theorem three_dvd_card_of_PSL {S : Type} [Group S] {n p f : ℕ}
    (h : StatedClassicalModel S .PSL n p f) : 3 ∣ Nat.card S := by
  obtain ⟨⟨-, -, hn, -⟩, K, _, _, -, ⟨e⟩⟩ := h
  rw [Nat.card_congr e.toEquiv]
  rcases Nat.lt_or_ge n 3 with h3 | h3
  · obtain rfl : n = 2 := by omega
    exact three_dvd_card_PSL_two
  · exact three_dvd_card_PSL_of_three_le h3

theorem three_dvd_card_of_PSU {S : Type} [Group S] {n p f : ℕ}
    (h : StatedClassicalModel S .PSU n p f) : 3 ∣ Nat.card S := by
  obtain ⟨⟨hp, -, hn, -⟩, K, _, _, -, ⟨e⟩⟩ := h
  rw [Nat.card_congr e.toEquiv]
  exact three_dvd_card_PSU_of_three_le hn (pow_ne_zero _ hp.ne_zero)

theorem three_dvd_card_of_PSp_two {S : Type} [Group S] {p f : ℕ}
    (h : StatedClassicalModel S .PSp 2 p f) : 3 ∣ Nat.card S := by
  obtain ⟨-, K, _, _, -, ⟨e⟩⟩ := h
  rw [Nat.card_congr e.toEquiv]
  exact three_dvd_card_PSp_two

theorem three_dvd_card_alternating {S : Type} [Group S] {n : ℕ} (h5 : 5 ≤ n) (h8 : n ≤ 8)
    (e : S ≃* alternatingGroup (Fin n)) : 3 ∣ Nat.card S := by
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
  rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
    Fintype.card_fin]
  interval_cases n <;> decide

end F918V3T3

end CFSG.Quasithin
