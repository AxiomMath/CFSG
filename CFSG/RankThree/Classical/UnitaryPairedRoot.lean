module

public import CFSG.RankThree.Classical.UnitaryEvenSummand

public section

namespace CFSG.RankThree.Classical

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag
open scoped Matrix

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

section Transport

variable {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] {G : Matrix ι ι K}
  {P : Matrix (Fin n) ι K}
  (hGG : G * G = 1) (hGadj : hadj h G = G) (hP : hadj h P * P = G)
  (hcard : Fintype.card ι = n)

@[expose] noncomputable def gConj (G : Matrix ι ι K) (P : Matrix (Fin n) ι K)
    (T : Matrix ι ι K) : Matrix (Fin n) (Fin n) K :=
  P * T * (G * hadj h P)

include hGG hP in
theorem gframe_inv_mul : G * hadj h P * P = 1 := by
  rw [Matrix.mul_assoc, hP, hGG]

include hGG hP hcard in
theorem gframe_mul_inv : P * (G * hadj h P) = 1 := by
  have e : ι ≃ Fin n := Fintype.equivOfCardEq (by simp [hcard])
  exact (Matrix.mul_eq_one_comm_of_equiv e).mp (gframe_inv_mul h hGG hP)

include hGG hP in
theorem gConj_mul (T T' : Matrix ι ι K) :
    gConj h G P T * gConj h G P T' = gConj h G P (T * T') := by
  rw [gConj, gConj, gConj]
  calc P * T * (G * hadj h P) * (P * T' * (G * hadj h P))
      = P * T * (G * hadj h P * P) * T' * (G * hadj h P) := by
        simp only [Matrix.mul_assoc]
    _ = P * (T * T') * (G * hadj h P) := by
        rw [gframe_inv_mul h hGG hP, Matrix.mul_one]
        simp only [Matrix.mul_assoc]

include hGG hP hcard in
theorem gConj_one : gConj h G P 1 = 1 := by
  rw [gConj, Matrix.mul_one, gframe_mul_inv h hGG hP hcard]

include hGG hP in
theorem gConj_mul_frame (T : Matrix ι ι K) : gConj h G P T * P = P * T := by
  rw [gConj, Matrix.mul_assoc, gframe_inv_mul h hGG hP, Matrix.mul_one]

include hGG hGadj hP hcard in
theorem hadj_gConj_mul {T : Matrix ι ι K} (hT : hadj h T * G * T = G) :
    hadj h (gConj h G P T) * gConj h G P T = 1 := by
  rw [gConj, hadj_mul, hadj_mul, hadj_mul, hadj_hadj, hGadj]
  calc P * G * (hadj h T * hadj h P) * (P * T * (G * hadj h P))
      = P * G * (hadj h T * (hadj h P * P) * T) * G * hadj h P := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by
        rw [hP, hT]
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc G G, hGG, Matrix.one_mul, gframe_mul_inv h hGG hP hcard]

include hGG hP hcard in
theorem det_gConj (T : Matrix ι ι K) : (gConj h G P T).det = T.det := by
  have e : ι ≃ Fin n := Fintype.equivOfCardEq (by simp [hcard])
  set Q := G * hadj h P
  have hPQ : P * Q = 1 := gframe_mul_inv h hGG hP hcard
  have hsplit : gConj h G P T =
      P.submatrix id e.symm * T.submatrix e.symm e.symm * Q.submatrix e.symm id := by
    rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]
    rfl
  have hPQ' : P.submatrix id e.symm * Q.submatrix e.symm id = 1 := by
    rw [Matrix.submatrix_mul_equiv, hPQ, Matrix.submatrix_id_id]
  rw [hsplit, Matrix.det_mul, Matrix.det_mul, Matrix.det_submatrix_equiv_self, mul_comm _ T.det,
    mul_assoc, ← Matrix.det_mul, hPQ', Matrix.det_one, mul_one]

include hGG hP in
theorem eq_smul_of_gConj_eq_scalar {T : Matrix ι ι K} {c : K}
    (hT : gConj h G P T = Matrix.scalar (Fin n) c) : T = c • 1 := by
  have := congrArg (fun A => G * hadj h P * A * P) hT
  simp only [gConj] at this
  calc T = G * hadj h P * P * T * (G * hadj h P * P) := by
        rw [gframe_inv_mul h hGG hP, Matrix.one_mul, Matrix.mul_one]
    _ = G * hadj h P * (P * T * (G * hadj h P)) * P := by
        simp only [Matrix.mul_assoc]
    _ = c • 1 := by
        rw [this, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul,
          Matrix.mul_one, Matrix.smul_mul, gframe_inv_mul h hGG hP]

@[expose] noncomputable def gSU (T : Matrix ι ι K) (hT : hadj h T * G * T = G) (hdet : T.det = 1) :
    unitarySU p f K n :=
  ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero (gConj h G P T)
      (by rw [det_gConj h hGG hP hcard, hdet]; exact one_ne_zero),
    (mem_unitarySU_iff h).mpr ⟨by rw [Matrix.GeneralLinearGroup.val_mkOfDetNeZero,
      det_gConj h hGG hP hcard, hdet], hadj_gConj_mul h hGG hGadj hP hcard hT⟩⟩

theorem coe_gSU (T : Matrix ι ι K) (hT : hadj h T * G * T = G) (hdet : T.det = 1) :
    ((gSU h hGG hGadj hP hcard T hT hdet : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      gConj h G P T :=
  rfl

theorem gSU_mul (T T' : Matrix ι ι K) (hT : hadj h T * G * T = G) (hdet : T.det = 1)
    (hT' : hadj h T' * G * T' = G) (hdet' : T'.det = 1) (hTT : hadj h (T * T') * G * (T * T') = G)
    (hdetTT : (T * T').det = 1) :
    gSU h hGG hGadj hP hcard (T * T') hTT hdetTT =
      gSU h hGG hGadj hP hcard T hT hdet * gSU h hGG hGadj hP hcard T' hT' hdet' := by
  apply Subtype.ext
  apply Units.ext
  rw [Subgroup.coe_mul, Units.val_mul, coe_gSU, coe_gSU, coe_gSU, gConj_mul h hGG hP]

end Transport

section Roots

theorem hypGram2_mul_self (r : ℕ) : hypGram2 r K * hypGram2 r K = 1 := by
  rw [hypGram2, Matrix.fromBlocks_multiply]
  simp [← Matrix.fromBlocks_one]

theorem hadj_hypGram2 (r : ℕ) : hadj h (hypGram2 r K) = hypGram2 r K := by
  simp only [hypGram2, hadj_fromBlocks, hadj_one, hadj_zero]

@[expose] def rootMat (η a b : K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K :=
  siegelMat (Matrix.diagonal ![η * a, η * b])

theorem rootMat_mul (η a b a' b' : K) :
    rootMat η a b * rootMat η a' b' = rootMat η (a + a') (b + b') := by
  rw [rootMat, rootMat, rootMat, siegelMat_mul, Matrix.diagonal_add]
  congr 2
  funext i
  fin_cases i <;> simp [mul_add]

theorem rootMat_zero (η : K) : rootMat η 0 0 = 1 := by
  rw [rootMat, mul_zero]
  convert siegelMat_zero (F := K) (r := 2)
  ext i j
  fin_cases i <;> fin_cases j <;> simp

variable {h}

theorem diag_mem_skewHerm {η a b : K} (hη : h.bar η = -η) (ha : a ∈ h.fixedField)
    (hb : b ∈ h.fixedField) : Matrix.diagonal ![η * a, η * b] ∈ skewHermMatrices h 2 := by
  rw [mem_skewHermMatrices_iff]
  intro k l
  by_cases hkl : k = l
  · subst hkl
    fin_cases k <;>
    simp [map_mul, hη, (h.mem_fixedField).mp ha, (h.mem_fixedField).mp hb]
  · simp [Matrix.diagonal_apply_ne _ hkl, Matrix.diagonal_apply_ne _ (Ne.symm hkl)]

theorem rootMat_isometry {η a b : K} (hη : h.bar η = -η) (ha : a ∈ h.fixedField)
    (hb : b ∈ h.fixedField) : hadj h (rootMat η a b) * hypGram2 2 K * rootMat η a b =
      hypGram2 2 K :=
  siegelMat_isometry h (diag_mem_skewHerm hη ha hb)

theorem det_rootMat (η a b : K) : (rootMat η a b).det = 1 := by
  rw [rootMat, siegelMat, Matrix.det_fromBlocks_zero₂₁]
  simp

theorem torusGL_isometry {a : Fin 2 → Kˣ} (ha : ∀ i, h.bar (a i) = a i) :
    hadj h (torusGL a : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) * hypGram2 2 K *
      (torusGL a : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = hypGram2 2 K :=
  ((mem_gramSU).mp (torusGL_mem_gramSU h ha)).1

theorem det_torusGL' {a : Fin 2 → Kˣ} (ha : ∀ i, h.bar (a i) = a i) :
    (torusGL a : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K).det = 1 :=
  ((mem_gramSU).mp (torusGL_mem_gramSU h ha)).2

theorem torusGL_mul_rootMat (a : Fin 2 → Kˣ) (η x y : K) :
    (torusGL a : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) * rootMat η x y =
      rootMat η ((a 0 : K) ^ 2 * x) ((a 1 : K) ^ 2 * y) *
        (torusGL a : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) := by
  have hconj := congrArg Units.val (torusGL_conj_siegelGL a (Matrix.diagonal ![η * x, η * y]))
  rw [Units.val_mul, Units.val_mul, coe_siegelGL, coe_siegelGL] at hconj
  have hD : (Matrix.diagonal fun i => ((a i : Kˣ) : K)) * Matrix.diagonal ![η * x, η * y] *
      (Matrix.diagonal fun i => ((a i : Kˣ) : K)) =
        Matrix.diagonal ![η * ((a 0 : K) ^ 2 * x), η * ((a 1 : K) ^ 2 * y)] := by
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    fin_cases i <;> simp <;> ring
  rw [hD] at hconj
  rw [rootMat, rootMat, ← hconj, Matrix.mul_assoc, Matrix.mul_assoc, ← Units.val_mul,
    inv_mul_cancel, Units.val_one, Matrix.mul_one]

end Roots

section Paired

@[expose] def pairedRootRadical (P : Matrix (Fin 4) (Fin 2 ⊕ Fin 2) K) (η : K) :
    Subgroup (unitarySU p f K 4) where
  carrier := {g | ∃ a ∈ h.fixedField, ∃ b ∈ h.fixedField,
    ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * P = P * rootMat η a b}
  mul_mem' {g g'} hg hg' := by
    obtain ⟨a, ha, b, hb, hgab⟩ := hg
    obtain ⟨a', ha', b', hb', hgab'⟩ := hg'
    refine ⟨a + a', h.fixedField.add_mem ha ha', b + b', h.fixedField.add_mem hb hb', ?_⟩
    rw [Subgroup.coe_mul, Units.val_mul, Matrix.mul_assoc, hgab', ← Matrix.mul_assoc, hgab,
      Matrix.mul_assoc, rootMat_mul]
  one_mem' := ⟨0, h.fixedField.zero_mem, 0, h.fixedField.zero_mem, by
    rw [rootMat_zero, Matrix.mul_one, Subgroup.coe_one, Units.val_one, Matrix.one_mul]⟩
  inv_mem' {g} hg := by
    obtain ⟨a, ha, b, hb, hgab⟩ := hg
    refine ⟨-a, h.fixedField.neg_mem ha, -b, h.fixedField.neg_mem hb, ?_⟩
    have hinv : ((g⁻¹ : unitarySU p f K 4) : GL (Fin 4) K).val *
        ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = 1 := by
      rw [Subgroup.coe_inv, ← Units.val_mul, inv_mul_cancel, Units.val_one]
    calc ((g⁻¹ : unitarySU p f K 4) : GL (Fin 4) K).val * P
        = ((g⁻¹ : unitarySU p f K 4) : GL (Fin 4) K).val * (P * rootMat η a b) *
            rootMat η (-a) (-b) := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, rootMat_mul, add_neg_cancel, add_neg_cancel,
            rootMat_zero, Matrix.mul_one]
      _ = P * rootMat η (-a) (-b) := by
          rw [← hgab, ← Matrix.mul_assoc, hinv, Matrix.one_mul]

@[expose] def pairedRoot (P : Matrix (Fin 4) (Fin 2 ⊕ Fin 2) K) (η : K) :
    Subgroup (unitaryPSU h 4) :=
  (pairedRootRadical h P η).map (unitaryProj h 4)

variable {P : Matrix (Fin 4) (Fin 2 ⊕ Fin 2) K} (hP : hadj h P * P = hypGram2 2 K) {η : K}
  (hη : h.bar η = -η)

theorem card_two_sum_two : Fintype.card (Fin 2 ⊕ Fin 2) = 4 := by
  simp

@[expose] noncomputable def pairedSUHom :
    Multiplicative (h.fixedField × h.fixedField) →* unitarySU p f K 4 where
  toFun v := gSU h (hypGram2_mul_self 2) (hadj_hypGram2 h 2) hP card_two_sum_two
    (rootMat η (v.toAdd.1 : K) (v.toAdd.2 : K)) (rootMat_isometry hη v.toAdd.1.2 v.toAdd.2.2)
    (det_rootMat _ _ _)
  map_one' := Subtype.ext (Units.ext (by
    rw [Subgroup.coe_one, Units.val_one, coe_gSU]
    change gConj h (hypGram2 2 K) P (rootMat η 0 0) = 1
    rw [rootMat_zero, gConj_one h (hypGram2_mul_self 2) hP card_two_sum_two]))
  map_mul' v v' := Subtype.ext (Units.ext (by
    rw [Subgroup.coe_mul, Units.val_mul, coe_gSU, coe_gSU, coe_gSU,
      gConj_mul h (hypGram2_mul_self 2) hP, rootMat_mul]
    rfl))

theorem coe_pairedSUHom (v : Multiplicative (h.fixedField × h.fixedField)) :
    ((pairedSUHom h hP hη v : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      gConj h (hypGram2 2 K) P (rootMat η (v.toAdd.1 : K) (v.toAdd.2 : K)) :=
  rfl

theorem pairedRootRadical_eq_range : pairedRootRadical h P η = (pairedSUHom h hP hη).range := by
  ext g
  constructor
  · rintro ⟨a, ha, b, hb, hgab⟩
    refine ⟨Multiplicative.ofAdd (⟨a, ha⟩, ⟨b, hb⟩), Subtype.ext (Units.ext ?_)⟩
    rw [coe_pairedSUHom]
    change P * rootMat η a b * (hypGram2 2 K * hadj h P) = _
    rw [← hgab, Matrix.mul_assoc, gframe_mul_inv h (hypGram2_mul_self 2) hP card_two_sum_two,
      Matrix.mul_one]
  · rintro ⟨v, rfl⟩
    exact ⟨_, v.toAdd.1.2, _, v.toAdd.2.2,
      gConj_mul_frame h (hypGram2_mul_self 2) hP _⟩

@[expose] noncomputable def pairedRootHom :
    Multiplicative (h.fixedField × h.fixedField) →* unitaryPSU h 4 :=
  (unitaryProj h 4).comp (pairedSUHom h hP hη)

theorem pairedRoot_eq_range : pairedRoot h P η = (pairedRootHom h hP hη).range := by
  rw [pairedRoot, pairedRootRadical_eq_range h hP hη, MonoidHom.map_range]
  rfl

theorem pairedRootHom_injective (hη0 : η ≠ 0) : Function.Injective (pairedRootHom h hP hη) := by
  rw [injective_iff_map_eq_one]
  intro v hv
  have hmem : pairedSUHom h hP hη v ∈ unitaryScalars h 4 := by
    rw [← ker_unitaryProj]
    exact hv
  obtain ⟨c, -, -, hc⟩ := hmem
  have hT := eq_smul_of_gConj_eq_scalar h (hypGram2_mul_self 2) hP
    (T := rootMat η (v.toAdd.1 : K) (v.toAdd.2 : K)) (c := (c : K)) (by
      rw [← coe_pairedSUHom h hP hη, hc, Matrix.GeneralLinearGroup.coe_scalar])
  have h12 := congrArg Matrix.toBlocks₁₂ hT
  simp only [rootMat, siegelMat, Matrix.toBlocks_fromBlocks₁₂] at h12
  have h0 : ∀ i : Fin 2, Matrix.diagonal ![η * (v.toAdd.1 : K), η * (v.toAdd.2 : K)] i i = 0 := by
    intro i
    rw [h12]
    simp [Matrix.toBlocks₁₂]
  have ha := h0 0
  have hb := h0 1
  simp only [Matrix.diagonal_apply_eq, Matrix.cons_val_zero, Matrix.cons_val_one,
    mul_eq_zero, hη0, false_or] at ha hb
  exact Multiplicative.toAdd.injective (Prod.ext (Subtype.ext ha) (Subtype.ext hb))

theorem bar_vec_two {s t : Kˣ} (hs : h.bar s = s) (ht : h.bar t = t) :
    ∀ i, h.bar ((![s, t] i : Kˣ) : K) = ((![s, t] i : Kˣ) : K) := by
  intro i
  fin_cases i
  · exact hs
  · exact ht

@[expose] noncomputable def pairedTorusSU {s t : Kˣ} (hs : h.bar s = s) (ht : h.bar t = t) :
    unitarySU p f K 4 :=
  gSU h (hypGram2_mul_self 2) (hadj_hypGram2 h 2) hP card_two_sum_two (torusGL ![s, t])
    (torusGL_isometry (bar_vec_two h hs ht)) (det_torusGL' (bar_vec_two h hs ht))

theorem pairedRootHom_conj {s t : Kˣ} (hs : h.bar s = s) (ht : h.bar t = t)
    (v : h.fixedField × h.fixedField) :
    unitaryProj h 4 (pairedTorusSU h hP hs ht) * pairedRootHom h hP hη (Multiplicative.ofAdd v) *
      (unitaryProj h 4 (pairedTorusSU h hP hs ht))⁻¹ =
    pairedRootHom h hP hη (Multiplicative.ofAdd
      (⟨(s : K) ^ 2 * (v.1 : K), h.fixedField.mul_mem (h.fixedField.pow_mem
        ((h.mem_fixedField).mpr hs) 2) v.1.2⟩,
       ⟨(t : K) ^ 2 * (v.2 : K), h.fixedField.mul_mem (h.fixedField.pow_mem
        ((h.mem_fixedField).mpr ht) 2) v.2.2⟩)) := by
  have hSU : pairedTorusSU h hP hs ht * pairedSUHom h hP hη (Multiplicative.ofAdd v) =
      pairedSUHom h hP hη (Multiplicative.ofAdd
      (⟨(s : K) ^ 2 * (v.1 : K), h.fixedField.mul_mem (h.fixedField.pow_mem
        ((h.mem_fixedField).mpr hs) 2) v.1.2⟩,
       ⟨(t : K) ^ 2 * (v.2 : K), h.fixedField.mul_mem (h.fixedField.pow_mem
        ((h.mem_fixedField).mpr ht) 2) v.2.2⟩)) * pairedTorusSU h hP hs ht := by
    apply Subtype.ext
    apply Units.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, coe_pairedSUHom,
      coe_pairedSUHom, pairedTorusSU, coe_gSU, gConj_mul h (hypGram2_mul_self 2) hP,
      gConj_mul h (hypGram2_mul_self 2) hP, torusGL_mul_rootMat]
    rfl
  rw [pairedRootHom, MonoidHom.comp_apply, MonoidHom.comp_apply, ← map_mul, ← map_inv,
    ← map_mul, hSU, mul_inv_cancel_right]

theorem pairedRootHom_conj' {s t : Kˣ} (hs : h.bar s = s) (ht : h.bar t = t)
    {v v' : h.fixedField × h.fixedField} (h1 : (v'.1 : K) = (s : K) ^ 2 * v.1)
    (h2 : (v'.2 : K) = (t : K) ^ 2 * v.2) :
    unitaryProj h 4 (pairedTorusSU h hP hs ht) * pairedRootHom h hP hη (Multiplicative.ofAdd v) *
      (unitaryProj h 4 (pairedTorusSU h hP hs ht))⁻¹ =
    pairedRootHom h hP hη (Multiplicative.ofAdd v') := by
  rw [pairedRootHom_conj h hP hη hs ht v]
  congr 2
  exact Prod.ext (Subtype.ext h1.symm) (Subtype.ext h2.symm)

end Paired

section Main

theorem coe_fst_nsmul (n : ℕ) (v : h.fixedField × h.fixedField) :
    (((n • v).1 : h.fixedField) : K) = (n : K) * (v.1 : K) := by
  rw [Prod.smul_fst, AddSubmonoidClass.coe_nsmul, nsmul_eq_mul]

theorem coe_snd_nsmul (n : ℕ) (v : h.fixedField × h.fixedField) :
    (((n • v).2 : h.fixedField) : K) = (n : K) * (v.2 : K) := by
  rw [Prod.smul_snd, AddSubmonoidClass.coe_nsmul, nsmul_eq_mul]

theorem nsmul_fixedField_prod_eq_zero [CharP K p] (v : h.fixedField × h.fixedField) :
    p • v = 0 := by
  refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
  · rw [coe_fst_nsmul, CharP.cast_eq_zero, zero_mul]
    rfl
  · rw [coe_snd_nsmul, CharP.cast_eq_zero, zero_mul]
    rfl

theorem unitary_four_paired_root (P : Matrix (Fin 4) (Fin 2 ⊕ Fin 2) K)
    (hP : (P.map h.bar)ᵀ * P = Matrix.fromBlocks 0 1 1 0) {η : K} (hη0 : η ≠ 0)
    (hη : h.bar η = -η) :
    IsElemAbelian p (pairedRoot h P η) ∧ Nat.card (pairedRoot h P η) = p ^ (2 * f) := by
  have hP' : hadj h P * P = hypGram2 2 K := hP
  have : Fact p.Prime := ⟨h.prime⟩
  have : CharP K p := h.charP
  rw [pairedRoot_eq_range h hP' hη]
  refine ⟨isElemAbelian_range (nsmul_fixedField_prod_eq_zero h) _, ?_⟩
  rw [MonoidHom.range_eq_map,
    Subgroup.card_map_of_injective (pairedRootHom_injective h hP' hη hη0), Subgroup.card_top,
    Nat.card_congr Multiplicative.toAdd, Nat.card_prod, h.card_fixedField, ← pow_add, two_mul]

theorem unitary_four_paired_root_preimage_comm (hp3 : 3 < p)
    (P : Matrix (Fin 4) (Fin 2 ⊕ Fin 2) K) (hP : (P.map h.bar)ᵀ * P = Matrix.fromBlocks 0 1 1 0)
    {η : K} (_hη0 : η ≠ 0) (hη : h.bar η = -η) {Y : Type*} [Group Y] (φ : Y →* unitaryPSU h 4)
    (hφ : Function.Surjective φ) (hZ : φ.ker ≤ Subgroup.center Y) :
    ∀ x ∈ (pairedRoot h P η).comap φ, ∀ y ∈ (pairedRoot h P η).comap φ, x * y = y * x := by
  have hP' : hadj h P * P = hypGram2 2 K := hP
  have : Fact p.Prime := ⟨h.prime⟩
  have : CharP K p := h.charP
  have := h.finite
  have hp2 : p ≠ 2 := by omega
  have h9 : p ^ f ≠ 9 := by
    intro h9
    have h3 : p ∣ 9 := h9 ▸ dvd_pow_self p (by have := h.one_le; omega)
    have := (Nat.prime_dvd_prime_iff_eq h.prime Nat.prime_three).mp
      (h.prime.dvd_of_dvd_pow (show p ∣ 3 ^ 2 by simpa using h3))
    omega
  have h2 : (2 : K) ≠ 0 := by
    intro h0
    have := (CharP.cast_eq_zero_iff K p 2).mp (by exact_mod_cast h0)
    have := Nat.le_of_dvd (by norm_num) this
    omega
  have hcop : ¬ p ∣ 4 * 1 - 1 := by
    intro hd
    have := Nat.le_of_dvd (by norm_num) hd
    omega
  set ρ := pairedRootHom h hP' hη
  have hb1 : h.bar ((1 : Kˣ) : K) = ((1 : Kˣ) : K) := by rw [Units.val_one, map_one]
  have hb2 : h.bar ((Units.mk0 (2 : K) h2 : Kˣ) : K) = ((Units.mk0 (2 : K) h2 : Kˣ) : K) := by
    rw [Units.val_mk0, map_ofNat]
  have hsq : ∀ (i : Fin 2) (x y : h.fixedField),
      liftPair hφ ρ (if i = 0 then (x, 0) else (0, x)) (if i = 0 then (y, 0) else (0, y)) = 1 := by
    intro i x y
    let _ := centerCommGroup Y
    let δ : h.fixedField → h.fixedField × h.fixedField := fun z => if i = 0 then (z, 0) else (0, z)
    have hδ : ∀ z z', δ (z + z') = δ z + δ z' := fun z z' => by
      simp only [δ]
      split_ifs <;> simp
    let b : h.fixedField → h.fixedField → Additive (Subgroup.center Y) := fun z z' =>
      liftPairAdd hφ ρ hZ (δ z) (δ z')
    have hb := CFSG.SectionRank.OddCover.square_invariant_alternating_eq_zero hp2
      h.card_fixedField b
      (fun z z' w => by simp only [b, hδ, liftPairAdd_add_left])
      (fun z w w' => by simp only [b, hδ, liftPairAdd_add_right])
      (fun z => liftPairAdd_self hφ ρ hZ (δ z))
      (fun c hc z w => by
        have hc' : (c : K) ≠ 0 := fun h0 => hc (Subtype.ext h0)
        have hbc : h.bar ((Units.mk0 (c : K) hc' : Kˣ) : K) =
            ((Units.mk0 (c : K) hc' : Kˣ) : K) := by
          rw [Units.val_mk0]
          exact (h.mem_fixedField).mp c.2
        by_cases hi : i = 0
        · refine liftPairAdd_congr hφ ρ hZ (liftPair_conj' hφ ρ hZ _
            (pairedRootHom_conj' h hP' hη hbc hb1 ?_ ?_)
            (pairedRootHom_conj' h hP' hη hbc hb1 ?_ ?_)) <;>
            simp [δ, hi]
        · refine liftPairAdd_congr hφ ρ hZ (liftPair_conj' hφ ρ hZ _
            (pairedRootHom_conj' h hP' hη hb1 hbc ?_ ?_)
            (pairedRootHom_conj' h hP' hη hb1 hbc ?_ ?_)) <;>
            simp [δ, hi])
      h9 x y
    exact (liftPairAdd_eq_zero_iff hφ ρ hZ _ _).mp hb
  have hcross1 : ∀ x y : h.fixedField, liftPair hφ ρ (x, 0) (0, y) = 1 := by
    intro x y
    refine liftPair_eq_one_of_weight hφ ρ hZ h.prime (nsmul_fixedField_prod_eq_zero h _)
      (s := 4) (t := 1) (by norm_num) hcop (liftPair_conj' hφ ρ hZ _
        (pairedRootHom_conj' h hP' hη hb2 hb1 ?_ ?_) (pairedRootHom_conj' h hP' hη hb2 hb1 ?_ ?_))
    all_goals first | rw [coe_fst_nsmul] | rw [coe_snd_nsmul]
    all_goals simp only [Units.val_mk0, Units.val_one]
    all_goals norm_num
  have hcross2 : ∀ x y : h.fixedField, liftPair hφ ρ (0, y) (x, 0) = 1 := by
    intro x y
    refine liftPair_eq_one_of_weight hφ ρ hZ h.prime (nsmul_fixedField_prod_eq_zero h _)
      (s := 4) (t := 1) (by norm_num) hcop (liftPair_conj' hφ ρ hZ _
        (pairedRootHom_conj' h hP' hη hb1 hb2 ?_ ?_) (pairedRootHom_conj' h hP' hη hb1 hb2 ?_ ?_))
    all_goals first | rw [coe_fst_nsmul] | rw [coe_snd_nsmul]
    all_goals simp only [Units.val_mk0, Units.val_one]
    all_goals norm_num
  have hvanish : ∀ v w, liftPair hφ ρ v w = 1 := by
    intro v w
    have hv : v = (v.1, 0) + (0, v.2) := by simp
    have hw : w = (w.1, 0) + (0, w.2) := by simp
    rw [hv, hw, liftPair_add_left hφ ρ hZ, liftPair_add_right hφ ρ hZ,
      liftPair_add_right hφ ρ hZ, hcross1, hcross2]
    have h0 := hsq 0 v.1 w.1
    have h1 := hsq 1 v.2 w.2
    simp only [ite_true, Fin.one_eq_zero_iff, OfNat.ofNat_ne_one, ite_false] at h0 h1
    rw [h0, h1]
    simp
  have hrange := pairedRoot_eq_range h hP' hη
  intro x hx y hy
  refine mul_comm_of_liftPair_eq_one hφ ρ hZ hvanish ?_ ?_
  · rw [← hrange]
    exact hx
  · rw [← hrange]
    exact hy

end Main

end CFSG.RankThree.Classical
