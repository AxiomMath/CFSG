module

public import CFSG.Quasithin.Vol2.KGFact4413L3

public section

namespace CFSG.Quasithin.H13.KG4413

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.QuasithinUnique.Setup.X7a CFSG.Quasithin.SteinbergBS CFSG.QuasithinUnique
open CFSG.ComponentClassification.CatalogueBHigherLinearAction (slConjugation)
open scoped MatrixGroups

section Cycle

variable {F : Type} [Field F]

@[expose] def cyc3Mat (F : Type) [Field F] : Matrix (Fin 3) (Fin 3) F :=
  !![0, 0, 1; 1, 0, 0; 0, 1, 0]

@[expose] def cyc3iMat (F : Type) [Field F] : Matrix (Fin 3) (Fin 3) F :=
  !![0, 1, 0; 0, 0, 1; 1, 0, 0]

@[expose] def cyc3SL (F : Type) [Field F] : SL(3, F) :=
  ⟨cyc3Mat F, by simp [cyc3Mat, Matrix.det_fin_three]⟩

@[expose] def cyc3iSL (F : Type) [Field F] : SL(3, F) :=
  ⟨cyc3iMat F, by simp [cyc3iMat, Matrix.det_fin_three]⟩

theorem cyc3SL_coe : ((cyc3SL F : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) = cyc3Mat F := rfl

theorem cyc3iSL_coe : ((cyc3iSL F : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) = cyc3iMat F := rfl

theorem cyc3SL_mul_cyc3iSL : cyc3SL F * cyc3iSL F = 1 := by
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one, cyc3SL_coe,
    cyc3iSL_coe]
  fin_cases i <;> fin_cases j <;> simp [cyc3Mat, cyc3iMat, Matrix.mul_apply, Fin.sum_univ_three]

theorem cyc3SL_inv : (cyc3SL F)⁻¹ = cyc3iSL F :=
  inv_eq_of_mul_eq_one_right cyc3SL_mul_cyc3iSL

theorem cyc3SL_mul_self : cyc3SL F * cyc3SL F = cyc3iSL F := by
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, cyc3SL_coe, cyc3iSL_coe]
  fin_cases i <;> fin_cases j <;> simp [cyc3Mat, cyc3iMat, Matrix.mul_apply, Fin.sum_univ_three]

theorem cyc3SL_pow_three : cyc3SL F ^ 3 = 1 := by
  rw [pow_succ, pow_two, cyc3SL_mul_self, ← cyc3SL_inv, inv_mul_cancel]

theorem cyc3SL_mul_dg3_mul_cyc3iSL (x y : Fˣ) :
    cyc3SL F * dg3 (x, y) * cyc3iSL F = dg3 ((x * y)⁻¹, x) := by
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, cyc3SL_coe,
    cyc3iSL_coe, coe_dg3, coe_dg3]
  simp only [Matrix.mul_apply, Fin.sum_univ_three]
  fin_cases i <;> fin_cases j <;> simp [cyc3Mat, cyc3iMat, mul_comm]

theorem cyc3iSL_transpose : (cyc3iSL F).transpose = cyc3SL F := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_transpose, cyc3SL_coe, cyc3iSL_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

variable [CharP F 2]

theorem wJ_mul_cyc3SL_mul_wJ : (wJ : SL(3, F)) * cyc3SL F * wJ = cyc3iSL F := by
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, cyc3SL_coe,
    cyc3iSL_coe, wJ_coe]
  simp only [Matrix.mul_apply, Fin.sum_univ_three]
  fin_cases i <;> fin_cases j <;> simp [cyc3Mat, cyc3iMat, wJMat]

theorem wJ_mul_cyc3iSL_mul_wJ : (wJ : SL(3, F)) * cyc3iSL F * wJ = cyc3SL F := by
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, cyc3SL_coe,
    cyc3iSL_coe, wJ_coe]
  simp only [Matrix.mul_apply, Fin.sum_univ_three]
  fin_cases i <;> fin_cases j <;> simp [cyc3Mat, cyc3iMat, wJMat]

theorem wJ_transpose : (wJ : SL(3, F)).transpose = wJ := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_transpose, wJ_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

@[expose] noncomputable def cyc3L3 (F : Type) [Field F] : projectiveSL 3 F := proj 3 F (cyc3SL F)

omit [CharP F 2] in
theorem cyc3L3_inv : (cyc3L3 F)⁻¹ = proj 3 F (cyc3iSL F) := by
  rw [cyc3L3, ← map_inv, cyc3SL_inv]

theorem w0L3_inv : (w0L3 F)⁻¹ = w0L3 F := by
  rw [w0L3, ← map_inv, wJ_inv]

theorem w0L3_mul_cyc3L3_mul_w0L3 : w0L3 F * cyc3L3 F * w0L3 F = (cyc3L3 F)⁻¹ := by
  rw [cyc3L3_inv, w0L3, cyc3L3, ← map_mul, ← map_mul, wJ_mul_cyc3SL_mul_wJ]

theorem w0L3_mul_cyc3L3_inv_mul_w0L3 : w0L3 F * (cyc3L3 F)⁻¹ * w0L3 F = cyc3L3 F := by
  rw [cyc3L3_inv, w0L3, cyc3L3, ← map_mul, ← map_mul, wJ_mul_cyc3iSL_mul_wJ]

omit [CharP F 2] in
theorem cyc3L3_pow_three : cyc3L3 F ^ 3 = 1 := by
  rw [cyc3L3, ← map_pow, cyc3SL_pow_three, map_one]

omit [CharP F 2] in
theorem cyc3L3_conj_mem_dL3 {d : projectiveSL 3 F} (hd : d ∈ dL3 F) :
    cyc3L3 F * d * (cyc3L3 F)⁻¹ ∈ dL3 F := by
  obtain ⟨_, ⟨⟨x, y⟩, rfl⟩, rfl⟩ := hd
  refine ⟨dg3 ((x * y)⁻¹, x), ⟨_, rfl⟩, ?_⟩
  rw [cyc3L3_inv, cyc3L3, ← map_mul, ← map_mul, cyc3SL_mul_dg3_mul_cyc3iSL]

omit [CharP F 2] in
theorem cyc3L3_inv_conj_mem_dL3 {d : projectiveSL 3 F} (hd : d ∈ dL3 F) :
    (cyc3L3 F)⁻¹ * d * cyc3L3 F ∈ dL3 F := by
  have h1 := cyc3L3_conj_mem_dL3 (cyc3L3_conj_mem_dL3 hd)
  have hc2 : cyc3L3 F * cyc3L3 F = (cyc3L3 F)⁻¹ :=
    eq_inv_of_mul_eq_one_left (by rw [← pow_three', cyc3L3_pow_three])
  have e : cyc3L3 F * (cyc3L3 F * d * (cyc3L3 F)⁻¹) * (cyc3L3 F)⁻¹ =
      (cyc3L3 F * cyc3L3 F) * d * (cyc3L3 F * cyc3L3 F)⁻¹ := by
    simp only [_root_.mul_inv_rev, mul_assoc]
  rw [e, hc2, inv_inv] at h1
  exact h1

theorem w0L3_inv_conj_mem_dL3 {d : projectiveSL 3 F} (hd : d ∈ dL3 F) :
    (w0L3 F)⁻¹ * d * w0L3 F ∈ dL3 F := by
  have h := w0L3_conj_mem_dL3 hd
  rw [w0L3_inv] at h ⊢
  exact h

omit [CharP F 2] in
theorem proj_not_mem_projUpperTriangular {g : SL(3, F)} {i j : Fin 3} (hij : j < i)
    (hg : (g : Matrix (Fin 3) (Fin 3) F) i j ≠ 0) : proj 3 F g ∉ projUpperTriangular 3 F := by
  intro h
  have h1 : g ∈ ((upperTriangular 3 F).map (proj 3 F)).comap (proj 3 F) := h
  rw [Subgroup.comap_map_eq, ker_proj, sup_eq_left.2 (scalars_le_upperTriangular 3 F)] at h1
  exact hg (h1 i j hij)

omit [CharP F 2] in
theorem cyc3L3_not_mem_projUpperTriangular : cyc3L3 F ∉ projUpperTriangular 3 F :=
  proj_not_mem_projUpperTriangular (i := 1) (j := 0) (by decide)
    (by rw [cyc3SL_coe]; simp [cyc3Mat])

omit [CharP F 2] in
theorem dL3_le_projUpperTriangular : dL3 F ≤ projUpperTriangular 3 F :=
  Subgroup.map_mono fun _ ⟨t, ht⟩ => ht ▸ dg3_mem_upperTriangular t

omit [CharP F 2] in
theorem cyc3L3_not_mem_dL3 : cyc3L3 F ∉ dL3 F :=
  fun h => cyc3L3_not_mem_projUpperTriangular (dL3_le_projUpperTriangular h)

omit [CharP F 2] in
theorem cyc3L3_ne_one : cyc3L3 F ≠ 1 :=
  fun h => cyc3L3_not_mem_dL3 (h ▸ (dL3 F).one_mem)

omit [CharP F 2] in
theorem orderOf_cyc3L3 : orderOf (cyc3L3 F) = 3 :=
  orderOf_eq_prime cyc3L3_pow_three cyc3L3_ne_one

omit [CharP F 2] in
theorem relIndex_dL3_sup_zpowers [Finite F] :
    (dL3 F).relIndex (dL3 F ⊔ Subgroup.zpowers (cyc3L3 F)) = 3 := by
  have hN : Subgroup.zpowers (cyc3L3 F) ≤
      Subgroup.normalizer ((dL3 F : Subgroup (projectiveSL 3 F)) : Set (projectiveSL 3 F)) := by
    rw [Subgroup.zpowers_le]
    exact A4.mem_normalizer_of_conj_mem fun d hd => cyc3L3_conj_mem_dL3 hd
  rw [sup_comm, A4.relIndex_sup_eq_of_le_normalizer' hN]
  have h1 : (dL3 F).relIndex (Subgroup.zpowers (cyc3L3 F)) ∣ 3 := by
    have := Subgroup.relIndex_dvd_card (dL3 F) (Subgroup.zpowers (cyc3L3 F))
    rwa [Nat.card_zpowers, orderOf_cyc3L3] at this
  rcases (Nat.dvd_prime Nat.prime_three).mp h1 with h | h
  · exfalso
    rw [Subgroup.relIndex_eq_one] at h
    exact cyc3L3_not_mem_dL3 (h (Subgroup.mem_zpowers _))
  · exact h

theorem dg3_eq_commutator_mul (a b : Fˣ) :
    dg3 (a, b) = (dg3 (1, b) * cyc3SL F * (dg3 (1, b))⁻¹ * (cyc3SL F)⁻¹) *
      (dg3 (1, a * b⁻¹) * wJ * (dg3 (1, a * b⁻¹))⁻¹ * (wJ : SL(3, F))⁻¹) := by
  have hc : ∀ t : Fˣ × Fˣ, cyc3SL F * (dg3 t)⁻¹ * (cyc3SL F)⁻¹ =
      dg3 ((t.1⁻¹ * t.2⁻¹)⁻¹, t.1⁻¹) := by
    intro t
    rw [cyc3SL_inv, ← map_inv, cyc3SL_mul_dg3_mul_cyc3iSL]
    rfl
  have hw : ∀ t : Fˣ × Fˣ, (wJ : SL(3, F)) * (dg3 t)⁻¹ * (wJ : SL(3, F))⁻¹ =
      dg3 ((t.1⁻¹ * t.2⁻¹)⁻¹, t.2⁻¹) := by
    intro t
    rw [wJ_inv, ← map_inv, wJ_mul_dg3_mul_wJ]
    rfl
  have e1 : dg3 (1, b) * cyc3SL F * (dg3 (1, b))⁻¹ * (cyc3SL F)⁻¹ =
      dg3 (1, b) * (cyc3SL F * (dg3 (1, b))⁻¹ * (cyc3SL F)⁻¹) := by group
  have e2 : dg3 (1, a * b⁻¹) * wJ * (dg3 (1, a * b⁻¹))⁻¹ * (wJ : SL(3, F))⁻¹ =
      dg3 (1, a * b⁻¹) * ((wJ : SL(3, F)) * (dg3 (1, a * b⁻¹))⁻¹ * (wJ : SL(3, F))⁻¹) := by
    group
  rw [e1, e2, hc, hw, ← map_mul, ← map_mul, ← map_mul]
  congr 1
  ext <;> simp

theorem exists_commutator_mul_of_mem_dL3 {d : projectiveSL 3 F} (hd : d ∈ dL3 F) :
    ∃ e₁ ∈ dL3 F, ∃ e₂ ∈ dL3 F,
      d = (e₁ * cyc3L3 F * e₁⁻¹ * (cyc3L3 F)⁻¹) * (e₂ * w0L3 F * e₂⁻¹ * (w0L3 F)⁻¹) := by
  obtain ⟨_, ⟨⟨a, b⟩, rfl⟩, rfl⟩ := hd
  refine ⟨proj 3 F (dg3 (1, b)), ⟨_, ⟨_, rfl⟩, rfl⟩, proj 3 F (dg3 (1, a * b⁻¹)),
    ⟨_, ⟨_, rfl⟩, rfl⟩, ?_⟩
  rw [dg3_eq_commutator_mul a b]
  simp only [map_mul, map_inv, cyc3L3, w0L3]

end Cycle

section Index

variable {F : Type} [Field F] [Finite F] [CharP F 2]

omit [CharP F 2] in
theorem index_upperTriangular_dvd :
    (upperTriangular 3 F).index ∣ (1 + Nat.card F) * (1 + Nat.card F + Nat.card F ^ 2) := by
  set q := Nat.card F with hq
  have hq1 : 1 ≤ q := Nat.card_pos
  have hU : Nat.card (unitriangular 3 F) = q ^ 3 := by
    rw [card_unitriangular]
  have hinj : Function.Injective (dg3 : Fˣ × Fˣ →* SL(3, F)) := by
    intro s t hst
    have h0 := congrFun (congrFun (congrArg Subtype.val hst) 0) 0
    have h1 := congrFun (congrFun (congrArg Subtype.val hst) 1) 1
    rw [coe_dg3, coe_dg3] at h0 h1
    simp at h0 h1
    exact Prod.ext (Units.ext h0) (Units.ext h1)
  have hD : Nat.card (dg3 : Fˣ × Fˣ →* SL(3, F)).range = (q - 1) ^ 2 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_prod, Nat.card_units,
      sq]
  have hUB : Nat.card (unitriangular 3 F) ∣ Nat.card (upperTriangular 3 F) :=
    Subgroup.card_dvd_of_le (unitriangular_le_upperTriangular 3 F)
  have hDB : Nat.card (dg3 : Fˣ × Fˣ →* SL(3, F)).range ∣ Nat.card (upperTriangular 3 F) :=
    Subgroup.card_dvd_of_le fun _ ⟨t, ht⟩ => ht ▸ dg3_mem_upperTriangular t
  have hcop : Nat.Coprime (q ^ 3) ((q - 1) ^ 2) := by
    refine Nat.Coprime.pow 3 2 ?_
    have : Nat.Coprime (q - 1 + 1) (q - 1) := Nat.coprime_self_add_left.mpr (Nat.coprime_one_left _)
    rwa [Nat.sub_add_cancel hq1] at this
  rw [hU] at hUB
  rw [hD] at hDB
  obtain ⟨k, hk⟩ := hcop.mul_dvd_of_dvd_of_dvd hUB hDB
  have hprod : ∏ j ∈ Finset.Icc 2 3, ∑ i ∈ Finset.range j, q ^ i =
      (1 + q) * (1 + q + q ^ 2) := by
    rw [show Finset.Icc 2 3 = {2, 3} by decide, Finset.prod_pair (by norm_num)]
    simp [Finset.sum_range_succ]
  have hSL : Nat.card SL(3, F) = q ^ 3 * (q - 1) ^ 2 * ((1 + q) * (1 + q + q ^ 2)) := by
    have h3 : (3 : ℕ) * (3 - 1) / 2 = 3 := by norm_num
    rw [RankThree.PartOne.K159.card_SL_eq_mul (K := F) (m := 3) (by norm_num), h3,
      show (3 : ℕ) - 1 = 2 from rfl, ← hq, hprod]
  have hmul := (upperTriangular 3 F).card_mul_index
  rw [hk] at hmul
  have hq2 : 1 < q := Finite.one_lt_card
  have hpos : 0 < q ^ 3 * (q - 1) ^ 2 := by
    have : 0 < q - 1 := by omega
    positivity
  refine ⟨k, ?_⟩
  apply Nat.eq_of_mul_eq_mul_left hpos
  rw [← hSL, ← hmul]
  ring

omit [Finite F] [CharP F 2] in
theorem not_nine_dvd {q : ℕ} (hq : 1 ≤ q) (h3 : 3 ∣ q - 1) :
    ¬ 9 ∣ (1 + q) * (1 + q + q ^ 2) := by
  obtain ⟨k, hk⟩ := h3
  have hq' : q = 3 * k + 1 := by omega
  have e : (1 + q) * (1 + q + q ^ 2) = 9 * (3 * k ^ 3 + 5 * k ^ 2 + 3 * k) + 6 := by
    subst hq'
    ring
  rw [e]
  omega

theorem not_three_dvd_index_dL3_sup (h3 : 3 ∣ Nat.card F - 1) :
    ¬ 3 ∣ (dL3 F ⊔ Subgroup.zpowers (cyc3L3 F)).index := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set q := Nat.card F with hq
  have hq1 : 1 ≤ q := Nat.card_pos
  intro hdvd
  have h1 := Subgroup.relIndex_mul_index (le_sup_left : dL3 F ≤ dL3 F ⊔ Subgroup.zpowers (cyc3L3 F))
  rw [relIndex_dL3_sup_zpowers] at h1
  have hDB : dL3 F ≤ projUpperTriangular 3 F := dL3_le_projUpperTriangular
  have h2 := Subgroup.relIndex_mul_index hDB
  have hB : projUpperTriangular 3 F = dL3 F ⊔ projUnitriangular 3 F :=
    le_antisymm projUpperTriangular_le (sup_le hDB
      (Subgroup.map_mono (unitriangular_le_upperTriangular 3 F)))
  have hcardB : Nat.card (projUpperTriangular 3 F) = Nat.card (dL3 F) * q ^ 3 := by
    have h := E2.BorelLift.card_sup_mul_card_inf (dL3_le_normalizer (F := F))
    rw [dL3_inf, Subgroup.card_bot, mul_one, card_projUnitriangular] at h
    rw [hB, h]
  have hrel : (dL3 F).relIndex (projUpperTriangular 3 F) = q ^ 3 := by
    have h := Subgroup.relIndex_mul_card (dL3 F) (projUpperTriangular 3 F)
    rw [inf_eq_left.mpr hDB, hcardB] at h
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos (h.trans (mul_comm _ _))
  rw [hrel] at h2
  have hBidx : (projUpperTriangular 3 F).index = (upperTriangular 3 F).index := by
    rw [projUpperTriangular, Subgroup.index_map_eq _ (proj_surjective 3 F)
      (by rw [ker_proj]; exact scalars_le_upperTriangular 3 F)]
  rw [hBidx] at h2
  obtain ⟨r, hr⟩ := hdvd
  have h9 : 9 ∣ q ^ 3 * (upperTriangular 3 F).index := by
    rw [h2, ← h1, hr]
    exact ⟨r, by ring⟩
  have hcop : Nat.Coprime 9 (q ^ 3) := by
    have h3q : ¬ 3 ∣ q := by
      intro h
      obtain ⟨k, hk⟩ := h3
      omega
    exact Nat.Coprime.pow_right 3 (Nat.Coprime.pow_left 2
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3q) |>.symm.symm)
  have h9' : 9 ∣ (upperTriangular 3 F).index := hcop.dvd_of_dvd_mul_left h9
  exact not_nine_dvd hq1 h3 (h9'.trans index_upperTriangular_dvd)

end Index

section Aut

variable {F : Type} [Field F] [Finite F] [CharP F 2]

omit [Finite F] [CharP F 2] in
theorem mem_range_dg3_of_diag {h : SL(3, F)}
    (hd : ∀ i j : Fin 3, i ≠ j → (h : Matrix (Fin 3) (Fin 3) F) i j = 0) :
    h ∈ (dg3 : Fˣ × Fˣ →* SL(3, F)).range := by
  have hdet : (h : Matrix (Fin 3) (Fin 3) F) 0 0 * (h : Matrix (Fin 3) (Fin 3) F) 1 1 *
      (h : Matrix (Fin 3) (Fin 3) F) 2 2 = 1 := by
    have h1 := h.2
    rw [Matrix.det_fin_three, hd 0 1 (by decide), hd 0 2 (by decide), hd 1 0 (by decide),
      hd 1 2 (by decide), hd 2 0 (by decide), hd 2 1 (by decide)] at h1
    simpa using h1
  have h0 : (h : Matrix (Fin 3) (Fin 3) F) 0 0 ≠ 0 := fun e => by
    rw [e, zero_mul, zero_mul] at hdet; exact zero_ne_one hdet
  have h1 : (h : Matrix (Fin 3) (Fin 3) F) 1 1 ≠ 0 := fun e => by
    rw [e, mul_zero, zero_mul] at hdet; exact zero_ne_one hdet
  refine ⟨(Units.mk0 _ h0, Units.mk0 _ h1), ?_⟩
  ext i j
  rw [coe_dg3]
  fin_cases i <;> fin_cases j
  · simp
  · simp [hd 0 1 (by decide)]
  · simp [hd 0 2 (by decide)]
  · simp [hd 1 0 (by decide)]
  · simp
  · simp [hd 1 2 (by decide)]
  · simp [hd 2 0 (by decide)]
  · simp [hd 2 1 (by decide)]
  · have e : (h : Matrix (Fin 3) (Fin 3) F) 2 2 *
        ((h : Matrix (Fin 3) (Fin 3) F) 0 0 * (h : Matrix (Fin 3) (Fin 3) F) 1 1) = 1 := by
      linear_combination hdet
    have e' := (eq_inv_of_mul_eq_one_left e).symm
    simpa using e'

omit [Finite F] in
theorem isDiag_of_conjAut_fix {B : GL (Fin 3) F}
    (hB : ∀ i j : Fin 3, j < i → (B : Matrix (Fin 3) (Fin 3) F) i j = 0) {a : Fˣ} (ha : a ≠ 1)
    (hfix : LinearFlag.conjAut 3 F B (proj 3 F (dg3 (a, 1))) = proj 3 F (dg3 (a, 1))) :
    ∀ i j : Fin 3, i ≠ j → (B : Matrix (Fin 3) (Fin 3) F) i j = 0 := by
  set g : SL(3, F) := dg3 (a, 1) with hg
  rw [conjAut_proj, proj_eq_proj_iff] at hfix
  obtain ⟨c, -, hc⟩ := hfix
  set h := slConjugation 3 F B g with hh
  have hB' : (B : Matrix (Fin 3) (Fin 3) F).IsUpperTriangular := fun _ _ e => hB _ _ e
  have hBi : ((B⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).IsUpperTriangular := by
    rw [Matrix.coe_units_inv]
    exact Matrix.blockTriangular_inv_of_blockTriangular hB'
  have hgU := mem_upperTriangular_iff_isUpperTriangular.1 (dg3_mem_upperTriangular (F := F) (a, 1))
  have hBB : ∀ i : Fin 3, (B : Matrix (Fin 3) (Fin 3) F) i i *
      ((B⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) i i = 1 := by
    intro i
    have h1 : (B : Matrix (Fin 3) (Fin 3) F) * ((B⁻¹ : GL (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have h2 := mul_apply_self_of_isUpperTriangular hB' hBi i
    rw [h1, one_apply_eq] at h2
    exact h2.symm
  have hdiag : ∀ i : Fin 3, (h : Matrix (Fin 3) (Fin 3) F) i i =
      (g : Matrix (Fin 3) (Fin 3) F) i i := by
    intro i
    rw [hh, coe_slConjugation, mul_apply_self_of_isUpperTriangular (hB'.mul hgU) hBi,
      mul_apply_self_of_isUpperTriangular hB' hgU]
    calc (B : Matrix (Fin 3) (Fin 3) F) i i * (g : Matrix (Fin 3) (Fin 3) F) i i *
          ((B⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) i i =
        ((B : Matrix (Fin 3) (Fin 3) F) i i *
          ((B⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) i i) *
            (g : Matrix (Fin 3) (Fin 3) F) i i := by ring
      _ = _ := by rw [hBB, one_mul]
  have hgh : (g : Matrix (Fin 3) (Fin 3) F) = (h : Matrix (Fin 3) (Fin 3) F) *
      scalar (Fin 3) (c : F) := by
    rw [← hc, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel_left]
  have hentry : ∀ i j : Fin 3, (g : Matrix (Fin 3) (Fin 3) F) i j =
      (h : Matrix (Fin 3) (Fin 3) F) i j * c := by
    intro i j
    rw [hgh, scalar_apply, mul_diagonal]
  have hd : (g : Matrix (Fin 3) (Fin 3) F) = diagonal ![(a : F), 1, (a : F)⁻¹] := by
    rw [hg, coe_dg3]
    congr 1
    ext i
    fin_cases i <;> simp
  have ha0 : (a : F) ≠ 0 := a.ne_zero
  have ha1 : (a : F) ≠ 1 := fun e => ha (Units.ext e)
  have hc1 : (c : F) = 1 := by
    have e := hentry 0 0
    rw [hdiag 0, hd] at e
    simp only [diagonal_apply_eq, Matrix.cons_val_zero] at e
    have e' : (a : F) * ((c : F) - 1) = 0 := by linear_combination -e
    rcases mul_eq_zero.mp e' with h0 | h0
    · exact absurd h0 ha0
    · exact sub_eq_zero.mp h0
  have hhg : (h : Matrix (Fin 3) (Fin 3) F) = g := by
    ext i j
    rw [hentry, hc1, mul_one]
  have hcomm : (B : Matrix (Fin 3) (Fin 3) F) * g = g * B := by
    have e := hhg
    rw [hh, coe_slConjugation] at e
    have hBiB : ((B⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
        (B : Matrix (Fin 3) (Fin 3) F) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    calc (B : Matrix (Fin 3) (Fin 3) F) * g =
        (B : Matrix (Fin 3) (Fin 3) F) * g * (((B⁻¹ : GL (Fin 3) F) :
          Matrix (Fin 3) (Fin 3) F) * B) := by rw [hBiB, Matrix.mul_one]
      _ = ((B : Matrix (Fin 3) (Fin 3) F) * g * ((B⁻¹ : GL (Fin 3) F) :
          Matrix (Fin 3) (Fin 3) F)) * B := (Matrix.mul_assoc _ _ _).symm
      _ = g * B := by rw [e]
  set v : Fin 3 → F := ![(a : F), 1, (a : F)⁻¹] with hv
  have hkey : ∀ i j : Fin 3, (B : Matrix (Fin 3) (Fin 3) F) i j * (v j - v i) = 0 := by
    intro i j
    have e := congrFun (congrFun hcomm i) j
    rw [hd, mul_diagonal, diagonal_mul] at e
    rw [mul_sub, e]
    ring
  have hainv : (a : F) ≠ (a : F)⁻¹ := by
    intro e
    have e2 : (a : F) * (a : F) = 1 := by
      calc (a : F) * (a : F) = (a : F) * (a : F)⁻¹ := by rw [← e]
        _ = 1 := mul_inv_cancel₀ ha0
    have e3 : ((a : F) + 1) * ((a : F) + 1) = 0 := by
      have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
      linear_combination e2 + ((a : F) + 1) * h2
    have e4 : (a : F) + 1 = 0 := mul_self_eq_zero.mp e3
    apply ha1
    have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
    linear_combination e4 - h2
  have hinv1 : (a : F)⁻¹ ≠ 1 := fun e => ha1 (inv_eq_one.mp e)
  have hvne : ∀ i j : Fin 3, i ≠ j → v j - v i ≠ 0 := by
    intro i j hij
    rw [sub_ne_zero]
    fin_cases i <;> fin_cases j <;> simp at hij <;>
      simp [hv, ha1, Ne.symm ha1, hainv, Ne.symm hainv, hinv1, Ne.symm hinv1]
  intro i j hij
  exact (mul_eq_zero.mp (hkey i j)).resolve_right (hvne i j hij)

omit [Finite F] [CharP F 2] in
theorem conjAut_proj_mem_of_diag {B : GL (Fin 3) F} {g : SL(3, F)}
    (hg : ∀ i j : Fin 3, i ≠ j →
      ((g⁻¹ * slConjugation 3 F B g : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) i j = 0) :
    (proj 3 F g)⁻¹ * LinearFlag.conjAut 3 F B (proj 3 F g) ∈ dL3 F := by
  rw [conjAut_proj, ← map_inv, ← map_mul]
  exact ⟨_, mem_range_dg3_of_diag hg, rfl⟩

omit [Finite F] in
theorem diag_of_perm {B : GL (Fin 3) F}
    (hB : ∀ i j : Fin 3, i ≠ j → (B : Matrix (Fin 3) (Fin 3) F) i j = 0) {g : SL(3, F)}
    (hg : g = wJ ∨ g = cyc3iSL F) :
    ∀ i j : Fin 3, i ≠ j →
      ((g⁻¹ * slConjugation 3 F B g : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) i j = 0 := by
  set b : Fin 3 → F := fun i => (B : Matrix (Fin 3) (Fin 3) F) i i with hb
  have hBd : (B : Matrix (Fin 3) (Fin 3) F) = diagonal b := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [hb]
    · rw [hB i j hij, diagonal_apply_ne _ hij]
  have hBid : ((B⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = diagonal (Ring.inverse b) := by
    rw [Matrix.coe_units_inv, hBd, Matrix.inv_diagonal]
  intro i j hij
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_slConjugation, hBd, hBid]
  rcases hg with rfl | rfl
  · rw [wJ_inv, wJ_coe]
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, wJMat, diagonal_apply] at hij ⊢
  · rw [← cyc3SL_inv, inv_inv, cyc3SL_coe, cyc3SL_inv, cyc3iSL_coe]
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, cyc3Mat, cyc3iMat, diagonal_apply] at hij ⊢

omit [Finite F] in
theorem fieldAut_perm (σ : F ≃+* F) {g : SL(3, F)} (hg : g = wJ ∨ g = cyc3iSL F) :
    LinearFlag.fieldAut 3 F σ (proj 3 F g) = proj 3 F g := by
  rw [fieldAut_proj]
  congr 1
  ext i j
  rw [SpecialLinearGroup.map_apply_coe]
  rcases hg with rfl | rfl
  · rw [wJ_coe]
    fin_cases i <;> fin_cases j <;> simp [wJMat, RingHom.mapMatrix_apply]
  · rw [cyc3iSL_coe]
    fin_cases i <;> fin_cases j <;> simp [cyc3iMat, RingHom.mapMatrix_apply]

omit [Finite F] in
theorem gammaZero_eq (x : projectiveSL 3 F) :
    gammaZero F x = w0L3 F * LinearFlag.dualAut 3 F x * (w0L3 F)⁻¹ := by
  rw [gammaZero, MulAut.mul_apply, ← conj_proj_eq_conjAut, MulAut.conj_apply]
  rfl

omit [Finite F] in
theorem gammaZero_w0L3 : gammaZero F (w0L3 F) = w0L3 F := by
  rw [gammaZero_eq, w0L3, dualAut_proj, wJ_inv, wJ_transpose]
  group

omit [Finite F] in
theorem gammaZero_cyc3L3 : gammaZero F (cyc3L3 F) = (cyc3L3 F)⁻¹ := by
  rw [gammaZero_eq, cyc3L3, dualAut_proj, cyc3SL_inv, cyc3iSL_transpose, ← cyc3L3,
    w0L3_inv, w0L3_mul_cyc3L3_mul_w0L3]

theorem exists_zpow_of_not_semilinear (hF : 2 < Nat.card F) {α : MulAut (projectiveSL 3 F)}
    (hαU : (projUnitriangular 3 F).map α.toMonoidHom = projUnitriangular 3 F)
    (hαD : ∀ d ∈ dL3 F, α d ∈ dL3 F) (hαs : α ∉ LinearFlag.semilinearAutGroup 3 F) :
    ∃ m : ℤ, (∀ d ∈ dL3 F, (w0L3 F)⁻¹ * α d * w0L3 F = d ^ m) ∧
      (w0L3 F)⁻¹ * ((w0L3 F)⁻¹ * α (w0L3 F) * w0L3 F) ∈ dL3 F ∧
      (cyc3L3 F)⁻¹ * ((w0L3 F)⁻¹ * α (cyc3L3 F) * w0L3 F) ∈ dL3 F := by
  obtain ⟨B, σ, hB, hαeq⟩ := exists_eq_semilinear_mul_gammaZero hαU hαs
  obtain ⟨m₀, hm₀⟩ := exists_fieldAut_dL3 (F := F) σ
  set ε : MulAut (projectiveSL 3 F) := LinearFlag.fieldAut 3 F σ * gammaZero F with hεdef
  have hα : ∀ x, α x = LinearFlag.conjAut 3 F B (ε x) := by
    intro x
    rw [hαeq, hεdef, mul_assoc]
    rfl
  have hw0 : LinearFlag.fieldAut 3 F σ (w0L3 F) = w0L3 F := fieldAut_perm σ (Or.inl rfl)
  have hεd : ∀ d ∈ dL3 F, ε d = w0L3 F * d ^ (-m₀) * (w0L3 F)⁻¹ := by
    intro d hd
    rw [hεdef, MulAut.mul_apply, gammaZero_dL3 hd, map_mul, map_mul, map_inv, map_inv, hw0,
      hm₀ d hd, _root_.zpow_neg]
  have hεD : ∀ d ∈ dL3 F, ε d ∈ dL3 F := fun d hd => by
    rw [hεd d hd]
    exact w0L3_conj_mem_dL3 (zpow_mem hd _)
  have hεsurj : ∀ e ∈ dL3 F, ∃ d ∈ dL3 F, ε d = e := by
    have hle : (dL3 F).map ε.toMonoidHom ≤ dL3 F := by
      rintro _ ⟨d, hd, rfl⟩
      exact hεD d hd
    have hcard : Nat.card ((dL3 F).map ε.toMonoidHom) = Nat.card (dL3 F) :=
      Subgroup.card_map_of_injective ε.injective
    have heq := Subgroup.eq_of_le_of_card_ge hle hcard.ge
    intro e he
    rw [← heq] at he
    obtain ⟨d, hd, rfl⟩ := he
    exact ⟨d, hd, rfl⟩
  have hfixB : ∀ e ∈ dL3 F, LinearFlag.conjAut 3 F B e = e := by
    intro e he
    obtain ⟨d, hd, rfl⟩ := hεsurj e he
    have h1 := conjAut_dL3_mem hB (hεD d hd)
    rw [← hα] at h1 ⊢
    have h4 : (ε d)⁻¹ * α d ∈ dL3 F ⊓ projUnitriangular 3 F :=
      ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ (hεD d hd)) (hαD d hd), h1⟩
    rw [dL3_inf, Subgroup.mem_bot, inv_mul_eq_one] at h4
    exact h4.symm
  have hnt : Nontrivial Fˣ := by
    rw [← Finite.one_lt_card_iff_nontrivial, Nat.card_units]
    omega
  obtain ⟨a, ha⟩ := exists_ne (1 : Fˣ)
  have hBd := isDiag_of_conjAut_fix hB ha (hfixB _ ⟨_, ⟨(a, 1), rfl⟩, rfl⟩)
  refine ⟨-m₀, fun d hd => ?_, ?_, ?_⟩
  · rw [hα, hfixB _ (hεD d hd), hεd d hd]
    group
  · have hεw : ε (w0L3 F) = w0L3 F := by
      rw [hεdef, MulAut.mul_apply, gammaZero_w0L3, hw0]
    have h1 := conjAut_proj_mem_of_diag (diag_of_perm hBd (Or.inl rfl))
    rw [← w0L3, ← hεw, ← hα, hεw] at h1
    have e : (w0L3 F)⁻¹ * ((w0L3 F)⁻¹ * α (w0L3 F) * w0L3 F) =
        (w0L3 F)⁻¹ * ((w0L3 F)⁻¹ * α (w0L3 F)) * w0L3 F := by group
    rw [e]
    exact w0L3_inv_conj_mem_dL3 h1
  · have hεc : ε (cyc3L3 F) = (cyc3L3 F)⁻¹ := by
      rw [hεdef, MulAut.mul_apply, gammaZero_cyc3L3, cyc3L3_inv,
        fieldAut_perm σ (Or.inr rfl)]
    have h1 := conjAut_proj_mem_of_diag (diag_of_perm hBd (Or.inr rfl))
    rw [← cyc3L3_inv, ← hεc, ← hα, hεc, inv_inv] at h1
    have e : (cyc3L3 F)⁻¹ * ((w0L3 F)⁻¹ * α (cyc3L3 F) * w0L3 F) =
        ((cyc3L3 F)⁻¹ * (w0L3 F)⁻¹ * (cyc3L3 F)⁻¹ * w0L3 F) *
          ((w0L3 F)⁻¹ * (cyc3L3 F * α (cyc3L3 F)) * w0L3 F) := by group
    have e2 : (cyc3L3 F)⁻¹ * (w0L3 F)⁻¹ * (cyc3L3 F)⁻¹ * w0L3 F = 1 := by
      rw [w0L3_inv, mul_assoc (cyc3L3 F)⁻¹, mul_assoc (cyc3L3 F)⁻¹,
        w0L3_mul_cyc3L3_inv_mul_w0L3, inv_mul_cancel]
    rw [e, e2, one_mul]
    exact w0L3_inv_conj_mem_dL3 h1

end Aut

end CFSG.Quasithin.H13.KG4413
