module

public import CFSG.Quasithin.H13.U4ParPoint
public import CFSG.Quasithin.Background.A3ComponentsBasic

public section

namespace CFSG.Quasithin.H13.U4Par

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.Quasithin (perfectCore perfectCore_le perfectCore_le_derivedSeriesOf
  le_perfectCore_of_perfect normalizer_le_normalizer_perfectCore)
open scoped Pointwise

variable {m : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 m K)

noncomputable abbrev parP2 : Subgroup (hypSU h 2 0) :=
  UnitaryHigher.isoStabilizer h 2 0 (hypFlag h 2 0 2)

theorem mem_parP2_iff (g : hypSU h 2 0) :
    g ∈ parP2 h ↔ ((g : GL Ix K) : Matrix Ix Ix K) if1 ie1 = 0 ∧
      ((g : GL Ix K) : Matrix Ix Ix K) if1 ie2 = 0 ∧
      ((g : GL Ix K) : Matrix Ix Ix K) if2 ie1 = 0 ∧
      ((g : GL Ix K) : Matrix Ix Ix K) if2 ie2 = 0 := by
  have hF : hypFlag h 2 0 2 = posFlag 2 0 K 2 := hypFlag_eq_posFlag h (by norm_num) (by norm_num)
  have hmem : ∀ (M : Matrix Ix Ix K), M if1 ie1 = 0 → M if1 ie2 = 0 → M if2 ie1 = 0 →
      M if2 ie2 = 0 → ∀ v ∈ posFlag 2 0 K 2, M *ᵥ v ∈ posFlag 2 0 K 2 := by
    intro M h11 h12 h21 h22 v hv a ha
    have h3 : v if1 = 0 := hv if1 (by simp)
    have h4 : v if2 = 0 := hv if2 (by simp)
    rcases ix_cases a with rfl | rfl | rfl | rfl
    · simp at ha
    · simp at ha
    · rw [mulVec, dotProduct, sum_ix, h3, h4, h11, h12]; ring
    · rw [mulVec, dotProduct, sum_ix, h3, h4, h21, h22]; ring
  have hsingle : ∀ b : Ix, (b = ie1 ∨ b = ie2) → (Pi.single b 1 : Ix → K) ∈ posFlag 2 0 K 2 := by
    rintro b hb a ha
    have : a ≠ b := by
      rintro rfl
      rcases hb with rfl | rfl <;> simp at ha
    simp [this]
  rw [UnitaryHigher.mem_isoStabilizer, hF]
  constructor
  · intro hg
    have key : ∀ a b, (b = ie1 ∨ b = ie2) → 2 ≤ fullPos a →
        ((g : GL Ix K) : Matrix Ix Ix K) a b = 0 := by
      intro a b hb ha
      have h1 : (g : GL Ix K) • (Pi.single b 1 : Ix → K) ∈ (g : GL Ix K) • posFlag 2 0 K 2 :=
        Submodule.smul_mem_pointwise_smul _ _ _ (hsingle b hb)
      rw [← Subgroup.smul_def, hg] at h1
      have h2 := h1 a ha
      change (((g : GL Ix K) : Matrix Ix Ix K) *ᵥ Pi.single b 1) a = 0 at h2
      rwa [mulVec_single_one, col_apply] at h2
    exact ⟨key _ _ (Or.inl rfl) (by simp), key _ _ (Or.inr rfl) (by simp),
      key _ _ (Or.inl rfl) (by simp), key _ _ (Or.inr rfl) (by simp)⟩
  · rintro ⟨h11, h12, h21, h22⟩
    rw [Subgroup.smul_def]
    refine smul_eq_of_mulVec_mem (hmem _ h11 h12 h21 h22) ?_
    have i11 := inv_apply h g if1 ie1
    have i12 := inv_apply h g if1 ie2
    have i21 := inv_apply h g if2 ie1
    have i22 := inv_apply h g if2 ie2
    simp only [hypPartner_ie1, hypPartner_ie2, hypPartner_if1, hypPartner_if2, h11, h12, h21,
      h22, map_zero] at i11 i12 i21 i22
    exact hmem _ i11 i12 i21 i22

@[expose] noncomputable def rho2 (g : hypSU h 2 0) : Matrix (Fin 2) (Fin 2) K :=
  !![((g : GL Ix K) : Matrix Ix Ix K) ie1 ie1, ((g : GL Ix K) : Matrix Ix Ix K) ie1 ie2;
    ((g : GL Ix K) : Matrix Ix Ix K) ie2 ie1, ((g : GL Ix K) : Matrix Ix Ix K) ie2 ie2]

theorem rho2_mul {g g' : hypSU h 2 0} (hg' : g' ∈ parP2 h) :
    rho2 h (g * g') = rho2 h g * rho2 h g' := by
  obtain ⟨c1, c2, c3, c4⟩ := (mem_parP2_iff h g').mp hg'
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [rho2, coe_mul_hypSU, mul_apply, sum_ix, Fin.sum_univ_two, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one, c1, c2, c3, c4, mul_zero, add_zero, Fin.zero_eta, Fin.isValue,
      Fin.mk_one]

theorem rho2_one : rho2 h 1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rho2, one_apply]

@[expose] def IsQ2Mat (M : Matrix Ix Ix K) : Prop :=
  M ie1 ie1 = 1 ∧ M ie1 ie2 = 0 ∧ M ie2 ie1 = 0 ∧ M ie2 ie2 = 1 ∧
  M if1 ie1 = 0 ∧ M if1 ie2 = 0 ∧ M if1 if1 = 1 ∧ M if1 if2 = 0 ∧
  M if2 ie1 = 0 ∧ M if2 ie2 = 0 ∧ M if2 if1 = 0 ∧ M if2 if2 = 1

theorem IsQ2Mat.mul {M M' : Matrix Ix Ix K} (hM : IsQ2Mat M) (hM' : IsQ2Mat M') :
    IsQ2Mat (M * M') := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩ := hM
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12⟩ := hM'
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [mul_apply, sum_ix] <;>
    simp [a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, b1, b2, b3, b4, b5, b6, b7, b8, b9,
      b10, b11, b12]

theorem IsQ2Mat.comm {M M' : Matrix Ix Ix K} (hM : IsQ2Mat M) (hM' : IsQ2Mat M') :
    M * M' = M' * M := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩ := hM
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12⟩ := hM'
  ext i j
  rw [mul_apply, sum_ix, mul_apply, sum_ix]
  rcases ix_cases i with rfl | rfl | rfl | rfl <;> rcases ix_cases j with rfl | rfl | rfl | rfl <;>
    simp [a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, b1, b2, b3, b4, b5, b6, b7, b8, b9,
      b10, b11, b12] <;> ring

theorem isQ2Mat_one : IsQ2Mat (1 : Matrix Ix Ix K) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [one_apply]

@[expose] noncomputable def radQ2 : Subgroup (hypSU h 2 0) where
  carrier := {g | IsQ2Mat ((g : GL Ix K) : Matrix Ix Ix K)}
  mul_mem' hg hg' := by
    simp only [Set.mem_ofPred_eq, coe_mul_hypSU]
    exact IsQ2Mat.mul hg hg'
  one_mem' := isQ2Mat_one
  inv_mem' := by
    intro g hg
    obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩ := hg
    have e := inv_apply h g
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [e] <;>
      simp [a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12]

theorem radQ2_comm {g g' : hypSU h 2 0} (hg : g ∈ radQ2 h) (hg' : g' ∈ radQ2 h) :
    g * g' = g' * g := by
  apply hypSU_ext
  rw [coe_mul_hypSU, coe_mul_hypSU]
  exact IsQ2Mat.comm hg hg'

theorem radQ2_le_parP2 : radQ2 h ≤ parP2 h := by
  intro g hg
  obtain ⟨-, -, -, -, a5, a6, -, -, a9, a10, -, -⟩ := hg
  exact (mem_parP2_iff h g).mpr ⟨a5, a6, a9, a10⟩

theorem mem_radQ2_of_rho2 {g : hypSU h 2 0} (hg : g ∈ parP2 h) (hrho : rho2 h g = 1) :
    g ∈ radQ2 h := by
  obtain ⟨c1, c2, c3, c4⟩ := (mem_parP2_iff h g).mp hg
  have p00 := congrFun (congrFun hrho 0) 0
  have p01 := congrFun (congrFun hrho 0) 1
  have p10 := congrFun (congrFun hrho 1) 0
  have p11 := congrFun (congrFun hrho 1) 1
  simp only [rho2, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, one_apply_eq,
    Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
    Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide)] at p00 p01 p10 p11
  have hgram := (mem_gramSU.mp g.2).1
  have entry : ∀ i j, ∑ k, h.bar ((((g : GL Ix K) : Matrix Ix Ix K)) (hypPartner k) i) *
      ((g : GL Ix K) : Matrix Ix Ix K) k j = hypGram 2 0 K i j := by
    intro i j
    have := congrFun (congrFun hgram i) j
    rw [mul_apply] at this
    simpa only [mul_hypGram_apply, transpose_apply, map_apply] using this
  have e11 := entry ie1 if1
  have e12 := entry ie1 if2
  have e21 := entry ie2 if1
  have e22 := entry ie2 if2
  rw [sum_ix, hypGram_apply] at e11 e12 e21 e22
  simp [c1, c2, c3, c4, p00, p01, p10, p11] at e11 e12 e21 e22
  exact ⟨p00, p01, p10, p11, c1, c2, e11, e12, c3, c4, e21, e22⟩

theorem parP2_le_normalizer_radQ2 :
    parP2 h ≤ Subgroup.normalizer (radQ2 h : Set (hypSU h 2 0)) := by
  have hrq : ∀ g ∈ radQ2 h, rho2 h g = 1 := by
    intro g hg
    obtain ⟨a1, a2, a3, a4, -⟩ := hg
    ext i j
    fin_cases i <;> fin_cases j <;> simp [rho2, a1, a2, a3, a4]
  have key : ∀ p ∈ parP2 h, ∀ g ∈ radQ2 h, p * g * p⁻¹ ∈ radQ2 h := by
    intro p hp g hg
    have hgP := radQ2_le_parP2 h hg
    have hpi := (parP2 h).inv_mem hp
    refine mem_radQ2_of_rho2 h ((parP2 h).mul_mem ((parP2 h).mul_mem hp hgP) hpi) ?_
    rw [rho2_mul h hpi, rho2_mul h hgP, hrq g hg, mul_one, ← rho2_mul h hpi, mul_inv_cancel,
      rho2_one]
  intro p hp
  rw [Subgroup.mem_normalizer_iff]
  intro g
  constructor
  · exact key p hp g
  · intro hg
    have := key p⁻¹ ((parP2 h).inv_mem hp) _ hg
    simpa [mul_assoc] using this

section SL2

variable (F : Type) [Field F] [CharP F 2]

theorem center_sl2_eq_bot_of_charTwo :
    Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) = ⊥ := by
  rw [eq_bot_iff]
  intro A hA
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
  rw [Fintype.card_fin] at hr
  have hr1 : r = 1 := by
    have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
    have h1 : (r + 1) * (r + 1) = 0 := by linear_combination hr + (r + 1) * h2
    have h3 := mul_self_eq_zero.mp h1
    rw [add_eq_zero_iff_eq_neg, CharTwo.neg_eq] at h3
    exact h3
  rw [Subgroup.mem_bot]
  ext i j
  rw [← hrA, hr1]
  simp

@[expose] noncomputable def sl2U : Matrix.SpecialLinearGroup (Fin 2) F :=
  ⟨!![1, 1; 0, 1], by simp [det_fin_two]⟩

@[expose] noncomputable def sl2L : Matrix.SpecialLinearGroup (Fin 2) F :=
  ⟨!![1, 0; 1, 1], by simp [det_fin_two]⟩

omit [CharP F 2] in
theorem exists_sl2_ne_comm : ∃ A B : Matrix.SpecialLinearGroup (Fin 2) F, A * B ≠ B * A := by
  refine ⟨sl2U F, sl2L F, fun hc => ?_⟩
  have hm := congrArg (fun A : Matrix.SpecialLinearGroup (Fin 2) F =>
    (A : Matrix (Fin 2) (Fin 2) F)) hc
  simp only [Matrix.SpecialLinearGroup.coe_mul] at hm
  have := congrFun (congrFun hm 0) 0
  simp [sl2U, sl2L, mul_apply, Fin.sum_univ_two] at this

theorem isSimpleGroup_sl2_of_charTwo (h4 : 4 ≤ Nat.card F) :
    IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) F) := by
  have hs : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple h4
  let e : Matrix.SpecialLinearGroup (Fin 2) F ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F :=
    QuotientGroup.quotientBot.symm.trans
      (QuotientGroup.quotientMulEquivOfEq (center_sl2_eq_bot_of_charTwo F).symm)
  exact e.isSimpleGroup

theorem commutator_sl2_eq_top_of_charTwo (h4 : 4 ≤ Nat.card F) :
    ⁅(⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)),
      (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F))⁆ =
      (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)) := by
  have := isSimpleGroup_sl2_of_charTwo F h4
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
    ⁅(⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)),
      (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F))⁆ with h0 | h0
  · exfalso
    obtain ⟨A, B, hAB⟩ := exists_sl2_ne_comm F
    have hmem := Subgroup.commutator_mem_commutator (Subgroup.mem_top A) (Subgroup.mem_top B)
    rw [h0, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
    exact hAB hmem
  · exact h0

theorem not_isPGroup_sl2_of_charTwo [Finite F] :
    ¬ IsPGroup 2 (Matrix.SpecialLinearGroup (Fin 2) F) := by
  intro hp
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨A, B, hAB⟩ := exists_sl2_ne_comm F
  have : Nontrivial (Matrix.SpecialLinearGroup (Fin 2) F) := ⟨⟨A * B, B * A, hAB⟩⟩
  have hc := hp.center_nontrivial
  rw [center_sl2_eq_bot_of_charTwo] at hc
  exact (Subgroup.nontrivial_iff_ne_bot _).mp hc rfl

end SL2

@[expose] noncomputable def lev2Mat (A : Matrix (Fin 2) (Fin 2) K) : Matrix Ix Ix K :=
  single ie1 ie1 (A 0 0) + single ie1 ie2 (A 0 1) + single ie2 ie1 (A 1 0) +
    single ie2 ie2 (A 1 1) + single if1 if1 (h.bar (A 1 1)) + single if1 if2 (h.bar (A 1 0)) +
    single if2 if1 (h.bar (A 0 1)) + single if2 if2 (h.bar (A 0 0))

theorem lev2Mat_apply (A : Matrix (Fin 2) (Fin 2) K) (i j : Ix) :
    lev2Mat h A i j = (if ie1 = i ∧ ie1 = j then A 0 0 else 0) +
      (if ie1 = i ∧ ie2 = j then A 0 1 else 0) + (if ie2 = i ∧ ie1 = j then A 1 0 else 0) +
      (if ie2 = i ∧ ie2 = j then A 1 1 else 0) +
      (if if1 = i ∧ if1 = j then h.bar (A 1 1) else 0) +
      (if if1 = i ∧ if2 = j then h.bar (A 1 0) else 0) +
      (if if2 = i ∧ if1 = j then h.bar (A 0 1) else 0) +
      (if if2 = i ∧ if2 = j then h.bar (A 0 0) else 0) := by
  simp only [lev2Mat, Matrix.add_apply, Matrix.single_apply]

theorem lev2Mat_mul (A B : Matrix (Fin 2) (Fin 2) K) :
    lev2Mat h A * lev2Mat h B = lev2Mat h (A * B) := by
  ext i j
  rw [mul_apply, sum_ix]
  rcases ix_cases i with rfl | rfl | rfl | rfl <;> rcases ix_cases j with rfl | rfl | rfl | rfl <;>
    simp [lev2Mat_apply, Matrix.mul_apply, Fin.sum_univ_two, map_add, map_mul] <;> ring

theorem lev2Mat_one : lev2Mat h (1 : Matrix (Fin 2) (Fin 2) K) = 1 := by
  ext i j
  rcases ix_cases i with rfl | rfl | rfl | rfl <;> rcases ix_cases j with rfl | rfl | rfl | rfl <;>
    simp [lev2Mat_apply, one_apply]

@[expose] def ixEF : Ix ≃ Fin 2 ⊕ Fin 2 where
  toFun a := if a = ie1 then .inl 0 else if a = ie2 then .inl 1 else if a = if1 then .inr 0
    else .inr 1
  invFun b := match b with
    | .inl i => if i = 0 then ie1 else ie2
    | .inr i => if i = 0 then if1 else if2
  left_inv a := by
    rcases ix_cases a with rfl | rfl | rfl | rfl <;> decide
  right_inv b := by
    rcases b with i | i <;> fin_cases i <;> decide

theorem det_lev2Mat {A : Matrix (Fin 2) (Fin 2) K} (hA : A.det = 1) : (lev2Mat h A).det = 1 := by
  have := h.charP
  rw [← det_reindex_self ixEF]
  have : reindex ixEF ixEF (lev2Mat h A) =
      fromBlocks A 0 0 !![h.bar (A 1 1), h.bar (A 1 0); h.bar (A 0 1), h.bar (A 0 0)] := by
    ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;> simp [lev2Mat_apply, ixEF]
  rw [this, det_fromBlocks_zero₂₁, hA, one_mul, det_fin_two_of]
  rw [det_fin_two] at hA
  have hb := congrArg h.bar hA
  simp only [map_sub, map_mul, map_one] at hb
  grind

theorem lev2Mat_gram {A : Matrix (Fin 2) (Fin 2) K} (hA : A.det = 1) :
    ((lev2Mat h A).map h.bar)ᵀ * hypGram 2 0 K * lev2Mat h A = hypGram 2 0 K := by
  have := h.charP
  rw [det_fin_two] at hA
  have hb := congrArg h.bar hA
  simp only [map_sub, map_mul, map_one] at hb
  ext i j
  rw [mul_apply, sum_ix]
  simp only [mul_hypGram_apply, transpose_apply, map_apply]
  rcases ix_cases i with rfl | rfl | rfl | rfl <;> rcases ix_cases j with rfl | rfl | rfl | rfl <;>
    simp [lev2Mat_apply, hypGram_apply, h.bar_bar] <;> grind

@[expose] noncomputable def lev2Elt (A : Matrix.SpecialLinearGroup (Fin 2) K) : hypSU h 2 0 :=
  ⟨⟨lev2Mat h A, lev2Mat h (A⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K),
    by rw [lev2Mat_mul, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.SpecialLinearGroup.coe_one, lev2Mat_one],
    by rw [lev2Mat_mul, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one, lev2Mat_one]⟩,
    mem_gramSU.mpr ⟨lev2Mat_gram h A.2, det_lev2Mat h A.2⟩⟩

@[expose] noncomputable def lev2Hom : Matrix.SpecialLinearGroup (Fin 2) K →* hypSU h 2 0 where
  toFun := lev2Elt h
  map_one' := hypSU_ext h (by
    change lev2Mat h ((1 : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = 1
    rw [Matrix.SpecialLinearGroup.coe_one, lev2Mat_one])
  map_mul' A B := hypSU_ext h (by
    change lev2Mat h ((A * B : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      lev2Mat h A * lev2Mat h B
    rw [lev2Mat_mul, Matrix.SpecialLinearGroup.coe_mul])

theorem coe_lev2Hom (A : Matrix.SpecialLinearGroup (Fin 2) K) :
    (((lev2Hom h A : hypSU h 2 0) : GL Ix K) : Matrix Ix Ix K) = lev2Mat h A :=
  rfl

theorem lev2Hom_le_parP2 : (lev2Hom h).range ≤ parP2 h := by
  rintro _ ⟨A, rfl⟩
  rw [mem_parP2_iff, coe_lev2Hom]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [lev2Mat_apply]

theorem rho2_lev2Hom (A : Matrix.SpecialLinearGroup (Fin 2) K) :
    rho2 h (lev2Hom h A) = A := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rho2, coe_lev2Hom, lev2Mat_apply]

@[expose] noncomputable def parH2 : Subgroup (hypSU h 2 0) where
  carrier := {g | g ∈ parP2 h ∧ (rho2 h g).det = 1}
  mul_mem' := by
    rintro g g' ⟨hg, hdg⟩ ⟨hg', hdg'⟩
    exact ⟨(parP2 h).mul_mem hg hg', by rw [rho2_mul h hg', det_mul, hdg, hdg', mul_one]⟩
  one_mem' := ⟨(parP2 h).one_mem, by rw [rho2_one, det_one]⟩
  inv_mem' := by
    rintro g ⟨hg, hdg⟩
    refine ⟨(parP2 h).inv_mem hg, ?_⟩
    have := congrArg Matrix.det (rho2_mul h (g := g) ((parP2 h).inv_mem hg))
    rw [mul_inv_cancel, rho2_one, det_one, det_mul, hdg, one_mul] at this
    exact this.symm

theorem parH2_le_parP2 : parH2 h ≤ parP2 h := fun _ hg => hg.1

theorem commutator_parP2_le : ⁅parP2 h, parP2 h⁆ ≤ parH2 h := by
  rw [Subgroup.commutator_le]
  intro g hg g' hg'
  have hgi := (parP2 h).inv_mem hg
  have hgi' := (parP2 h).inv_mem hg'
  refine ⟨(parP2 h).mul_mem ((parP2 h).mul_mem ((parP2 h).mul_mem hg hg') hgi) hgi', ?_⟩
  have h1 := congrArg Matrix.det (rho2_mul h (g := g) hgi)
  have h2 := congrArg Matrix.det (rho2_mul h (g := g') hgi')
  rw [mul_inv_cancel, rho2_one, det_one, det_mul] at h1 h2
  rw [commutatorElement_def, rho2_mul h hgi', rho2_mul h hgi, rho2_mul h hg', det_mul, det_mul,
    det_mul]
  calc (rho2 h g).det * (rho2 h g').det * (rho2 h g⁻¹).det * (rho2 h g'⁻¹).det
      = ((rho2 h g).det * (rho2 h g⁻¹).det) * ((rho2 h g').det * (rho2 h g'⁻¹).det) := by ring
    _ = 1 := by rw [← h1, ← h2, mul_one]

theorem perfectCore_parP2_le_parH2 : perfectCore (parP2 h) ≤ parH2 h :=
  (perfectCore_le_derivedSeriesOf (parP2 h) 1).trans (commutator_parP2_le h)

@[expose] noncomputable def rho2F : parH2 h →* Matrix.SpecialLinearGroup (Fin 2) K where
  toFun g := ⟨rho2 h g, g.2.2⟩
  map_one' := by
    ext i j
    change rho2 h (1 : parH2 h) i j = _
    rw [OneMemClass.coe_one, rho2_one]
    rfl
  map_mul' g g' := by
    ext i j
    change rho2 h (g * g' : parH2 h) i j = _
    rw [Subgroup.coe_mul, rho2_mul h (parH2_le_parP2 h g'.2)]
    rfl

theorem lev2Hom_le_parH2 : (lev2Hom h).range ≤ parH2 h := by
  rintro _ ⟨A, rfl⟩
  exact ⟨lev2Hom_le_parP2 h ⟨A, rfl⟩, by rw [rho2_lev2Hom]; exact A.2⟩

theorem rho2F_lev2Hom (A : Matrix.SpecialLinearGroup (Fin 2) K) :
    rho2F h ⟨lev2Hom h A, lev2Hom_le_parH2 h ⟨A, rfl⟩⟩ = A := by
  ext i j
  change rho2 h (lev2Hom h A) i j = _
  rw [rho2_lev2Hom]

include h in
theorem four_le_card : 4 ≤ Nat.card K := by
  rw [h.card]
  calc 4 = 2 ^ (2 * 1) := by norm_num
    _ ≤ 2 ^ (2 * m) := Nat.pow_le_pow_right (by norm_num) (by have := h.one_le; omega)

theorem lev2Hom_range_le_perfectCore : (lev2Hom h).range ≤ perfectCore (parP2 h) := by
  have := h.charP
  refine le_perfectCore_of_perfect (lev2Hom_le_parP2 h) ?_
  rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator,
    commutator_sl2_eq_top_of_charTwo K (four_le_card h)]

theorem pCoreOf_perfectCore_parP2_le_radQ2 :
    CFSG.Open.pCoreOf 2 (perfectCore (parP2 h)) ≤ radQ2 h := by
  have := h.finite
  have := h.charP
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O := CFSG.Open.pCoreOf 2 (perfectCore (parP2 h)) with hOdef
  have hOH : O ≤ parH2 h :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans (perfectCore_parP2_le_parH2 h)
  have hOp : IsPGroup 2 O := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hOn : parP2 h ≤ Subgroup.normalizer (O : Set (hypSU h 2 0)) :=
    (Subgroup.le_normalizer.trans (normalizer_le_normalizer_perfectCore (parP2 h))).trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _)
  obtain ⟨N, hNdef⟩ : ∃ N : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K),
      N = (O.subgroupOf (parH2 h)).map (rho2F h) := ⟨_, rfl⟩
  have hNn : N.Normal := by
    refine ⟨fun n hn A => ?_⟩
    rw [hNdef] at hn ⊢
    obtain ⟨o, ho, rfl⟩ := hn
    have hl := lev2Hom_le_parH2 h ⟨A, rfl⟩
    have hmem : (lev2Hom h A) * (o : hypSU h 2 0) * (lev2Hom h A)⁻¹ ∈ O :=
      (Subgroup.mem_normalizer_iff.mp (hOn (parH2_le_parP2 h hl)) o).mp ho
    refine ⟨⟨lev2Hom h A, hl⟩ * o * ⟨lev2Hom h A, hl⟩⁻¹, ?_, ?_⟩
    · rw [SetLike.mem_coe, Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_mul,
        Subgroup.coe_inv]
      exact hmem
    · rw [map_mul, map_mul, map_inv, rho2F_lev2Hom]
  have hOp' : IsPGroup 2 (O.subgroupOf (parH2 h)) :=
    hOp.of_equiv (Subgroup.subgroupOfEquivOfLe hOH).symm
  have hNp : IsPGroup 2 N := by
    rw [hNdef]
    exact IsPGroup.map hOp' (rho2F h)
  have := isSimpleGroup_sl2_of_charTwo K (four_le_card h)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with hN | hN
  · intro o ho
    have h1 : rho2F h ⟨o, hOH ho⟩ = 1 := by
      have : rho2F h ⟨o, hOH ho⟩ ∈ N := by
        rw [hNdef]
        exact ⟨⟨o, hOH ho⟩, ho, rfl⟩
      rwa [hN, Subgroup.mem_bot] at this
    have hrho : rho2 h o = 1 := by
      have := congrArg (fun A : Matrix.SpecialLinearGroup (Fin 2) K =>
        (A : Matrix (Fin 2) (Fin 2) K)) h1
      exact this
    exact mem_radQ2_of_rho2 h (hOH ho).1 hrho
  · exfalso
    rw [hN] at hNp
    exact not_isPGroup_sl2_of_charTwo K (hNp.of_equiv Subgroup.topEquiv)

theorem pCoreOf_perfectCore_parP2_comm {x y : hypSU h 2 0}
    (hx : x ∈ CFSG.Open.pCoreOf 2 (perfectCore (parP2 h)))
    (hy : y ∈ CFSG.Open.pCoreOf 2 (perfectCore (parP2 h))) : x * y = y * x :=
  radQ2_comm h (pCoreOf_perfectCore_parP2_le_radQ2 h hx) (pCoreOf_perfectCore_parP2_le_radQ2 h hy)

end CFSG.Quasithin.H13.U4Par
