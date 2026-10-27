module

public import CFSG.Quasithin.Vol2.Asc94.TSModel6

public section

namespace CFSG.Quasithin.A94.L52

open Matrix CFSG.CGT.M24S

@[expose] def NAm (f : Fin 6 → ZMod 2) : Mt :=
  Matrix.single 0 2 (f 0) + Matrix.single 0 3 (f 1) + Matrix.single 0 4 (f 2) +
    Matrix.single 1 2 (f 3) + Matrix.single 1 3 (f 4) + Matrix.single 1 4 (f 5)

theorem NAm_up (f : Fin 6 → ZMod 2) : ∀ i j : Fin 5, j ≤ i → NAm f i j = 0 := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [NAm, Matrix.single_apply] <;> revert h <;> decide

theorem NAm_c0 (f : Fin 6 → ZMod 2) : ∀ i : Fin 5, NAm f i 0 = 0 := by
  intro i
  fin_cases i <;> simp [NAm, Matrix.single_apply]

theorem NAm_r4 (f : Fin 6 → ZMod 2) : ∀ j : Fin 5, NAm f 4 j = 0 := by
  intro j
  fin_cases j <;> simp [NAm, Matrix.single_apply]

theorem NAm_supp (f : Fin 6 → ZMod 2) : SuppIn SA (NAm f) := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [NAm, Matrix.single_apply, SA]

@[expose] def eltA (f : Fin 6 → ZMod 2) : Hc :=
  unipH (NAm f) (NAm_up f) (NAm_c0 f) (NAm_r4 f)

theorem cm_eltA (f : Fin 6 → ZMod 2) : cm (eltA f) = 1 + NAm f := rfl

theorem eltA_mem (f : Fin 6 → ZMod 2) : eltA f ∈ A1 := by
  rw [mem_A1, cm_eltA]
  have : (1 + NAm f - 1 : Mt) = NAm f := by abel
  rw [this]
  exact NAm_supp f

theorem eA_NAm (f : Fin 6 → ZMod 2) : eA (NAm f) = f := by
  funext k
  fin_cases k <;> simp [eA, NAm, Matrix.single_apply]

theorem eA_eltA (f : Fin 6 → ZMod 2) : eA (cm (eltA f)) = f := by
  rw [cm_eltA, eA_one_add, eA_NAm]


theorem exists_eltA {a : Hc} (ha : a ∈ A1) : a = eltA (eA (cm a)) := by
  apply Subtype.ext
  apply Subtype.ext
  show cm a = 1 + NAm (eA (cm a))
  rw [mem_A1] at ha
  ext i j
  by_cases h : SA i j
  · have hi : i = 0 ∨ i = 1 := by
      have h1 : i.val ≤ 1 := h.1
      clear h
      revert h1
      revert i
      decide
    have hj : j = 2 ∨ j = 3 ∨ j = 4 := by
      have h1 : 2 ≤ j.val := h.2
      clear h
      revert h1
      revert j
      decide
    rcases hi with rfl | rfl <;> rcases hj with rfl | rfl | rfl <;>
      simp [eA, NAm, Matrix.single_apply, Matrix.one_apply]
  · have h1 := ha i j h
    rw [Matrix.sub_apply] at h1
    have h2 := sub_eq_zero.1 h1
    rw [Matrix.add_apply, NAm_supp _ i j h, add_zero, h2]

theorem eA_inj {a b : Hc} (ha : a ∈ A1) (hb : b ∈ A1) (h : eA (cm a) = eA (cm b)) : a = b := by
  rw [exists_eltA ha, exists_eltA hb, h]

theorem eltA_zero : eltA 0 = 1 := by
  apply Subtype.ext
  apply Subtype.ext
  show 1 + NAm 0 = (1 : Mt)
  ext i j
  simp [NAm]

theorem eA_one : eA (cm (1 : Hc)) = 0 := by
  rw [cm_one]
  funext k
  fin_cases k <;> simp [eA, Matrix.one_apply]

theorem eq_one_iff_eA {a : Hc} (ha : a ∈ A1) : a = 1 ↔ eA (cm a) = 0 := by
  constructor
  · rintro rfl
    exact eA_one
  · intro h
    rw [exists_eltA ha, h, eltA_zero]

theorem eA_zt : eA (cm zt) = ![0, 0, 1, 0, 0, 0] := by
  rw [cm_zt]
  funext k
  fin_cases k <;> simp [eA, tt, Matrix.single_apply, Matrix.one_apply]


theorem suppIn_S1_NAm (f : Fin 6 → ZMod 2) :
    SuppIn S1 (NAm f) ↔ f 3 = 0 ∧ f 4 = 0 ∧ f 5 = 0 := by
  constructor
  · intro h
    have h3 := h 1 2 (by decide)
    have h4 := h 1 3 (by decide)
    have h5 := h 1 4 (by decide)
    simp [NAm, Matrix.single_apply] at h3 h4 h5
    exact ⟨h3, h4, h5⟩
  · rintro ⟨h3, h4, h5⟩ i j hij
    fin_cases i <;> fin_cases j <;> simp_all [NAm, Matrix.single_apply, S1]

theorem suppIn_S2_NAm (f : Fin 6 → ZMod 2) :
    SuppIn S2 (NAm f) ↔ f 0 = 0 ∧ f 1 = 0 ∧ f 3 = 0 ∧ f 4 = 0 := by
  constructor
  · intro h
    have h0 := h 0 2 (by decide)
    have h1 := h 0 3 (by decide)
    have h3 := h 1 2 (by decide)
    have h4 := h 1 3 (by decide)
    simp [NAm, Matrix.single_apply] at h0 h1 h3 h4
    exact ⟨h0, h1, h3, h4⟩
  · rintro ⟨h0, h1, h3, h4⟩ i j hij
    fin_cases i <;> fin_cases j <;> simp_all [NAm, Matrix.single_apply, S2]

theorem suppIn_SQ_NAm (f : Fin 6 → ZMod 2) :
    SuppIn SQ (NAm f) ↔ f 3 = 0 ∧ f 4 = 0 := by
  constructor
  · intro h
    have h3 := h 1 2 (by decide)
    have h4 := h 1 3 (by decide)
    simp [NAm, Matrix.single_apply] at h3 h4
    exact ⟨h3, h4⟩
  · rintro ⟨h3, h4⟩ i j hij
    fin_cases i <;> fin_cases j <;> simp_all [NAm, Matrix.single_apply, SQ, inB]

theorem cm_sub_one_eltA (f : Fin 6 → ZMod 2) : cm (eltA f) - 1 = NAm f := by
  rw [cm_eltA]
  abel

theorem mem_U1_iff_eA {a : Hc} (ha : a ∈ A1) :
    a ∈ U1 ↔ eA (cm a) 3 = 0 ∧ eA (cm a) 4 = 0 ∧ eA (cm a) 5 = 0 := by
  have e := exists_eltA ha
  generalize eA (cm a) = f at e ⊢
  subst e
  rw [← suppIn_S1_NAm, ← cm_sub_one_eltA]
  exact mem_patSub hS1

theorem mem_U2_iff_eA {a : Hc} (ha : a ∈ A1) :
    a ∈ U2 ↔ eA (cm a) 0 = 0 ∧ eA (cm a) 1 = 0 ∧ eA (cm a) 3 = 0 ∧ eA (cm a) 4 = 0 := by
  have e := exists_eltA ha
  generalize eA (cm a) = f at e ⊢
  subst e
  rw [← suppIn_S2_NAm, ← cm_sub_one_eltA]
  exact mem_patSub hS2

theorem mem_Qh_iff_eA {a : Hc} (ha : a ∈ A1) :
    a ∈ Qh ↔ eA (cm a) 3 = 0 ∧ eA (cm a) 4 = 0 := by
  have e := exists_eltA ha
  generalize eA (cm a) = f at e ⊢
  subst e
  rw [← suppIn_SQ_NAm, ← cm_sub_one_eltA]
  exact mem_Qh_iff _


@[expose] def mP (p s22 s23 s24 s32 s33 s34 : ZMod 2) : Mt :=
  !![1, p, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, s22, s23, s24; 0, 0, s32, s33, s34; 0, 0, 0, 0, 1]

theorem mP_det : ∀ p s22 s23 s24 s32 s33 s34 : ZMod 2, s22 * s33 + s23 * s32 = 1 →
    (mP p s22 s23 s24 s32 s33 s34).det = 1 := by decide +kernel

theorem mP_col : ∀ p s22 s23 s24 s32 s33 s34 : ZMod 2, ∀ i : Fin 5,
    mP p s22 s23 s24 s32 s33 s34 i 0 = (1 : Mt) i 0 := by decide +kernel

theorem mP_row : ∀ p s22 s23 s24 s32 s33 s34 : ZMod 2, ∀ j : Fin 5,
    mP p s22 s23 s24 s32 s33 s34 4 j = (1 : Mt) 4 j := by decide +kernel

@[expose] def xP (p s22 s23 s24 s32 s33 s34 : ZMod 2) (h : s22 * s33 + s23 * s32 = 1) : Hc :=
  mkH (mP p s22 s23 s24 s32 s33 s34) (mP_det _ _ _ _ _ _ _ h) (mP_col _ _ _ _ _ _ _)
    (mP_row _ _ _ _ _ _ _)

theorem cm_xP (p s22 s23 s24 s32 s33 s34 : ZMod 2) (h : s22 * s33 + s23 * s32 = 1) :
    cm (xP p s22 s23 s24 s32 s33 s34 h) = mP p s22 s23 s24 s32 s33 s34 := rfl

theorem xP_mem (p s22 s23 s24 s32 s33 s34 : ZMod 2) (h : s22 * s33 + s23 * s32 = 1) :
    xP p s22 s23 s24 s32 s33 s34 h ∈ NH1 := by
  refine ⟨?_, ?_⟩ <;> simp [cm_xP, mP]


@[expose] def DeltaA (k : ℕ) : Set Hc := {a | a ∈ A1 ∧ a ≠ 1 ∧ lab (eA (cm a)) = k}

theorem DeltaA_conj {k : ℕ} {a x : Hc} (ha : a ∈ DeltaA k) (hx : x ∈ NH1) :
    x⁻¹ * a * x ∈ DeltaA k := by
  obtain ⟨haA, ha1, hal⟩ := ha
  have hxi : x⁻¹ ∈ NH1 := NH1.inv_mem hx
  refine ⟨?_, ?_, ?_⟩
  · have h := conj_NH1_A1 hxi haA
    rwa [inv_inv] at h
  · intro h
    apply ha1
    have : a = x * (x⁻¹ * a * x) * x⁻¹ := by group
    rw [this, h]
    group
  · rw [eA_conj hx haA, lab_actF _ _ _ _ _ _ _ (S'_det hx), hal]

theorem exists_conj_rep {k : Fin 7} {a : Hc} (ha : a ∈ DeltaA k.val) :
    ∃ x ∈ NH1, a = x⁻¹ * eltA (labRep k) * x := by
  obtain ⟨haA, ha1, hal⟩ := ha
  have hf0 : eA (cm a) ≠ 0 := fun h => ha1 ((eq_one_iff_eA haA).2 h)
  obtain ⟨p, s22, s23, s24, s32, s33, s34, hdet, hact⟩ := lab_trans k (eA (cm a)) hf0 hal
  refine ⟨xP p s22 s23 s24 s32 s33 s34 hdet, xP_mem _ _ _ _ _ _ _ hdet, ?_⟩
  have hxm := xP_mem p s22 s23 s24 s32 s33 s34 hdet
  have hcm : ∀ x, x = xP p s22 s23 s24 s32 s33 s34 hdet → cm x 0 1 = p ∧ cm x 2 2 = s22 ∧
      cm x 2 3 = s23 ∧ cm x 2 4 = s24 ∧ cm x 3 2 = s32 ∧ cm x 3 3 = s33 ∧ cm x 3 4 = s34 := by
    rintro x rfl
    simp [cm_xP, mP]
  obtain ⟨c1, c2, c3, c4, c5, c6, c7⟩ := hcm _ rfl
  apply eA_inj haA
  · have h := conj_NH1_A1 (NH1.inv_mem hxm) (eltA_mem (labRep k))
    rwa [inv_inv] at h
  · rw [eA_conj hxm (eltA_mem _), eA_eltA, c1, c2, c3, c4, c5, c6, c7, hact]


theorem deltaA_trans {k : Fin 7} {a b : Hc} (ha : a ∈ DeltaA k.val) (hb : b ∈ DeltaA k.val) :
    ∃ x ∈ NH1, b = x⁻¹ * a * x := by
  obtain ⟨xa, hxa, ea⟩ := exists_conj_rep ha
  obtain ⟨xb, hxb, eb⟩ := exists_conj_rep hb
  refine ⟨xa⁻¹ * xb, NH1.mul_mem (NH1.inv_mem hxa) hxb, ?_⟩
  rw [eb, ea]
  group

theorem lab_zero_iff : ∀ f : Fin 6 → ZMod 2, f ≠ 0 →
    (lab f = 0 ↔ f = ![0, 0, 1, 0, 0, 0]) := by decide +kernel

theorem lab_one_iff : ∀ f : Fin 6 → ZMod 2, f ≠ 0 →
    (lab f = 1 ↔ (f 3 = 0 ∧ f 4 = 0 ∧ f 5 = 0 ∧ f ≠ ![0, 0, 1, 0, 0, 0])) := by decide +kernel

theorem lab_two_iff : ∀ f : Fin 6 → ZMod 2, f ≠ 0 →
    (lab f = 2 ↔ (f 0 = 0 ∧ f 1 = 0 ∧ f 3 = 0 ∧ f 4 = 0 ∧ f ≠ ![0, 0, 1, 0, 0, 0])) := by
  decide +kernel

theorem lab_three_iff : ∀ f : Fin 6 → ZMod 2, f ≠ 0 →
    (lab f = 3 ↔ (f 3 = 0 ∧ f 4 = 0 ∧ ¬ f 5 = 0 ∧ ¬ (f 0 = 0 ∧ f 1 = 0))) := by decide +kernel

theorem DeltaA_zero : DeltaA 0 = {zt} := by
  ext a
  constructor
  · rintro ⟨haA, ha1, hal⟩
    have hf0 : eA (cm a) ≠ 0 := fun h => ha1 ((eq_one_iff_eA haA).2 h)
    have h := (lab_zero_iff _ hf0).1 hal
    exact eA_inj haA zt_mem_A1 (h.trans eA_zt.symm)
  · rintro rfl
    refine ⟨zt_mem_A1, zt_ne_one, ?_⟩
    rw [eA_zt]
    decide +kernel

theorem DeltaA_one : DeltaA 1 = ((A1 ⊓ U1 : Subgroup Hc) : Set Hc) \ {1, zt} := by
  ext a
  simp only [DeltaA, Set.mem_setOf_eq, Set.mem_diff, SetLike.mem_coe, Subgroup.mem_inf,
    Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
  constructor
  · rintro ⟨haA, ha1, hal⟩
    have hf0 : eA (cm a) ≠ 0 := fun h => ha1 ((eq_one_iff_eA haA).2 h)
    obtain ⟨h3, h4, h5, hz⟩ := (lab_one_iff _ hf0).1 hal
    refine ⟨⟨haA, (mem_U1_iff_eA haA).2 ⟨h3, h4, h5⟩⟩, ha1, fun h => hz ?_⟩
    rw [h, eA_zt]
  · rintro ⟨⟨haA, haU⟩, ha1, haz⟩
    have hf0 : eA (cm a) ≠ 0 := fun h => ha1 ((eq_one_iff_eA haA).2 h)
    obtain ⟨h3, h4, h5⟩ := (mem_U1_iff_eA haA).1 haU
    refine ⟨haA, ha1, (lab_one_iff _ hf0).2 ⟨h3, h4, h5, fun h => haz ?_⟩⟩
    exact eA_inj haA zt_mem_A1 (h.trans eA_zt.symm)

theorem DeltaA_two : DeltaA 2 = ((A1 ⊓ U2 : Subgroup Hc) : Set Hc) \ {1, zt} := by
  ext a
  simp only [DeltaA, Set.mem_setOf_eq, Set.mem_diff, SetLike.mem_coe, Subgroup.mem_inf,
    Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
  constructor
  · rintro ⟨haA, ha1, hal⟩
    have hf0 : eA (cm a) ≠ 0 := fun h => ha1 ((eq_one_iff_eA haA).2 h)
    obtain ⟨h0, h1, h3, h4, hz⟩ := (lab_two_iff _ hf0).1 hal
    refine ⟨⟨haA, (mem_U2_iff_eA haA).2 ⟨h0, h1, h3, h4⟩⟩, ha1, fun h => hz ?_⟩
    rw [h, eA_zt]
  · rintro ⟨⟨haA, haU⟩, ha1, haz⟩
    have hf0 : eA (cm a) ≠ 0 := fun h => ha1 ((eq_one_iff_eA haA).2 h)
    obtain ⟨h0, h1, h3, h4⟩ := (mem_U2_iff_eA haA).1 haU
    refine ⟨haA, ha1, (lab_two_iff _ hf0).2 ⟨h0, h1, h3, h4, fun h => haz ?_⟩⟩
    exact eA_inj haA zt_mem_A1 (h.trans eA_zt.symm)

theorem DeltaA_three :
    DeltaA 3 = {a | a ∈ A1 ∧ a ∈ Qh ∧ a ≠ 1 ∧ a ∉ U1 ∧ a ∉ U2} := by
  ext a
  simp only [DeltaA, Set.mem_setOf_eq]
  constructor
  · rintro ⟨haA, ha1, hal⟩
    have hf0 : eA (cm a) ≠ 0 := fun h => ha1 ((eq_one_iff_eA haA).2 h)
    obtain ⟨h3, h4, h5, h01⟩ := (lab_three_iff _ hf0).1 hal
    refine ⟨haA, (mem_Qh_iff_eA haA).2 ⟨h3, h4⟩, ha1, fun h => h5 ?_, fun h => h01 ?_⟩
    · exact ((mem_U1_iff_eA haA).1 h).2.2
    · have := (mem_U2_iff_eA haA).1 h
      exact ⟨this.1, this.2.1⟩
  · rintro ⟨haA, haQ, ha1, haU1, haU2⟩
    have hf0 : eA (cm a) ≠ 0 := fun h => ha1 ((eq_one_iff_eA haA).2 h)
    obtain ⟨h3, h4⟩ := (mem_Qh_iff_eA haA).1 haQ
    refine ⟨haA, ha1, (lab_three_iff _ hf0).2 ⟨h3, h4, fun h5 => haU1 ?_, fun h01 => haU2 ?_⟩⟩
    · exact (mem_U1_iff_eA haA).2 ⟨h3, h4, h5⟩
    · exact (mem_U2_iff_eA haA).2 ⟨h01.1, h01.2, h3, h4⟩


theorem ncard_DeltaA (k : Fin 7) : (DeltaA k.val).ncard = labSize k := by
  have himg : (fun a : Hc => eA (cm a)) '' DeltaA k.val =
      {f : Fin 6 → ZMod 2 | f ≠ 0 ∧ lab f = k.val} := by
    ext f
    constructor
    · rintro ⟨a, ⟨haA, ha1, hal⟩, rfl⟩
      exact ⟨fun h => ha1 ((eq_one_iff_eA haA).2 h), hal⟩
    · rintro ⟨hf0, hl⟩
      refine ⟨eltA f, ⟨eltA_mem f, ?_, ?_⟩, eA_eltA f⟩
      · intro h
        apply hf0
        have := eA_eltA f
        rw [h, eA_one] at this
        exact this.symm
      · rw [eA_eltA]
        exact hl
  have hinj : Set.InjOn (fun a : Hc => eA (cm a)) (DeltaA k.val) := fun a ha b hb h =>
    eA_inj ha.1 hb.1 h
  rw [← hinj.ncard_image, himg]
  have hc := lab_card k
  rw [← hc, ← Set.ncard_coe_finset]
  congr 1
  ext f
  simp

theorem A1_orbits : ∃ Δ : Fin 7 → Set Hc,
    (∀ i j, i ≠ j → Disjoint (Δ i) (Δ j)) ∧
    (⋃ i, Δ i) = (A1 : Set Hc) \ {1} ∧
    (∀ i, ∀ a ∈ Δ i, ∀ x ∈ NH1, x⁻¹ * a * x ∈ Δ i) ∧
    (∀ i, ∀ a ∈ Δ i, ∀ b ∈ Δ i, ∃ x ∈ NH1, b = x⁻¹ * a * x) ∧
    (∀ i, (Δ i).ncard = labSize i) ∧
    Δ 0 = {zt} ∧
    Δ 1 = ((A1 ⊓ U1 : Subgroup Hc) : Set Hc) \ {1, zt} ∧
    Δ 2 = ((A1 ⊓ U2 : Subgroup Hc) : Set Hc) \ {1, zt} ∧
    Δ 3 = {a | a ∈ A1 ∧ a ∈ Qh ∧ a ≠ 1 ∧ a ∉ U1 ∧ a ∉ U2} := by
  refine ⟨fun k => DeltaA k.val, ?_, ?_, ?_, ?_, ?_, DeltaA_zero, DeltaA_one, DeltaA_two,
    DeltaA_three⟩
  · intro i j hij
    rw [Set.disjoint_left]
    intro a ha hb
    exact hij (Fin.ext (ha.2.2.symm.trans hb.2.2))
  · ext a
    simp only [Set.mem_iUnion, Set.mem_diff, SetLike.mem_coe, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, haA, ha1, -⟩
      exact ⟨haA, ha1⟩
    · rintro ⟨haA, ha1⟩
      exact ⟨⟨lab (eA (cm a)), lab_lt _⟩, haA, ha1, rfl⟩
  · intro i a ha x hx
    exact DeltaA_conj ha hx
  · intro i a ha b hb
    exact deltaA_trans ha hb
  · intro i
    exact ncard_DeltaA i

end CFSG.Quasithin.A94.L52
