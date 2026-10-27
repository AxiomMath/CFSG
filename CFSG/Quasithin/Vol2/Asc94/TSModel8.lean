module

public import CFSG.Quasithin.Vol2.Asc94.TSModel7

public section

namespace CFSG.Quasithin.A94.L52

open Matrix CFSG.CGT.M24S

@[expose] def labBList : List ℕ :=
  [0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 4, 0, 5, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    2, 0, 3, 0, 2, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 5, 0, 5, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0]

@[expose] def labB (f : Fin 6 → ZMod 2) : ℕ := labBList.getD (codeF f) 0

@[expose] def labBSize : Fin 6 → ℕ := ![1, 2, 2, 2, 4, 4]

@[expose] def labBRep : Fin 6 → (Fin 6 → ZMod 2) :=
  ![![0, 0, 1, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1], ![0, 1, 0, 0, 0, 1],
    ![0, 0, 0, 0, 1, 0], ![0, 0, 1, 0, 1, 0]]

@[expose] def InB (f : Fin 6 → ZMod 2) : Prop := f 0 = 0 ∧ f 3 = 0

instance : DecidablePred InB := fun f => inferInstanceAs (Decidable (f 0 = 0 ∧ f 3 = 0))

theorem labB_lt : ∀ f : Fin 6 → ZMod 2, labB f < 6 ∨ ¬ InB f := by decide +kernel

theorem inB_actT : ∀ p s23 s24 s34 : ZMod 2, ∀ f : Fin 6 → ZMod 2, InB f →
    InB (actF p 1 s23 s24 0 1 s34 f) := by decide +kernel

theorem labB_actT : ∀ p s23 s24 s34 : ZMod 2, ∀ f : Fin 6 → ZMod 2, InB f →
    labB (actF p 1 s23 s24 0 1 s34 f) = labB f := by decide +kernel

theorem labB_trans : ∀ k : Fin 6, ∀ f : Fin 6 → ZMod 2, InB f → f ≠ 0 → labB f = k.val →
    ∃ p s23 s24 s34 : ZMod 2, actF p 1 s23 s24 0 1 s34 (labBRep k) = f := by decide +kernel

theorem labB_card : ∀ k : Fin 6,
    (Finset.univ.filter (fun f : Fin 6 → ZMod 2 => InB f ∧ f ≠ 0 ∧ labB f = k.val)).card =
      labBSize k := by decide +kernel

theorem labB_zero_iff : ∀ f : Fin 6 → ZMod 2, InB f → f ≠ 0 →
    (labB f = 0 ↔ f = ![0, 0, 1, 0, 0, 0]) := by decide +kernel

theorem labB_one_iff : ∀ f : Fin 6 → ZMod 2, InB f → f ≠ 0 →
    (labB f = 1 ↔ (f 3 = 0 ∧ f 4 = 0 ∧ f 5 = 0 ∧ f ≠ ![0, 0, 1, 0, 0, 0])) := by decide +kernel

theorem labB_two_iff : ∀ f : Fin 6 → ZMod 2, InB f → f ≠ 0 →
    (labB f = 2 ↔ (f 0 = 0 ∧ f 1 = 0 ∧ f 3 = 0 ∧ f 4 = 0 ∧ f ≠ ![0, 0, 1, 0, 0, 0])) := by
  decide +kernel

theorem labB_three_iff : ∀ f : Fin 6 → ZMod 2, InB f → f ≠ 0 →
    (labB f = 3 ↔ (f 3 = 0 ∧ f 4 = 0 ∧ ¬ f 5 = 0 ∧ ¬ (f 0 = 0 ∧ f 1 = 0))) := by decide +kernel

theorem suppIn_SA2_NAm (f : Fin 6 → ZMod 2) :
    SuppIn SA2 (NAm f) ↔ f 0 = 0 ∧ f 3 = 0 := by
  constructor
  · intro h
    have h0 := h 0 2 (by decide)
    have h3 := h 1 2 (by decide)
    simp [NAm, Matrix.single_apply] at h0 h3
    exact ⟨h0, h3⟩
  · rintro ⟨h0, h3⟩ i j hij
    fin_cases i <;> fin_cases j <;> simp_all [NAm, Matrix.single_apply, SA2]

theorem mem_A2_iff_eA {a : Hc} (ha : a ∈ A1) :
    a ∈ A2 ↔ eA (cm a) 0 = 0 ∧ eA (cm a) 3 = 0 := by
  have e := exists_eltA ha
  generalize eA (cm a) = f at e ⊢
  subst e
  rw [← suppIn_SA2_NAm, ← cm_sub_one_eltA]
  exact mem_patSub hSA2

theorem Tm_le_NH1 : Tm ≤ NH1 := fun x hx =>
  ⟨Tm_entry_zero hx (by decide), Tm_entry_zero hx (by decide)⟩

theorem Tm_diag {x : Hc} (hx : x ∈ Tm) (i : Fin 5) : cm x i i = 1 := by
  have h := (mem_Tm.1 hx) i i (lt_irrefl i)
  rw [Matrix.sub_apply, Matrix.one_apply_eq] at h
  exact sub_eq_zero.1 h

theorem eA_conj_Tm {x a : Hc} (hx : x ∈ Tm) (ha : a ∈ A1) :
    eA (cm (x⁻¹ * a * x)) = actF (cm x 0 1) 1 (cm x 2 3) (cm x 2 4) 0 1 (cm x 3 4) (eA (cm a)) := by
  have h := eA_conj (Tm_le_NH1 hx) ha
  rw [Tm_diag hx 2, Tm_diag hx 3, Tm_entry_zero hx (by decide : (2 : Fin 5) < 3)] at h
  exact h

@[expose] def xT (p s23 s24 s34 : ZMod 2) : Hc :=
  xP p 1 s23 s24 0 1 s34 (by simp)

theorem cm_xT (p s23 s24 s34 : ZMod 2) : cm (xT p s23 s24 s34) = mP p 1 s23 s24 0 1 s34 := rfl

theorem mP_unitri' : ∀ p s23 s24 s34 : ZMod 2, ∀ q : Fin 5 × Fin 5, q.2 ≤ q.1 →
    mP p 1 s23 s24 0 1 s34 q.1 q.2 = (1 : Mt) q.1 q.2 := by decide +kernel

theorem mP_unitri (p s23 s24 s34 : ZMod 2) (i j : Fin 5) (h : j ≤ i) :
    mP p 1 s23 s24 0 1 s34 i j = (1 : Mt) i j := mP_unitri' p s23 s24 s34 (i, j) h

theorem xT_mem (p s23 s24 s34 : ZMod 2) : xT p s23 s24 s34 ∈ Tm := by
  rw [mem_Tm, cm_xT]
  intro i j h
  rw [Matrix.sub_apply, mP_unitri p s23 s24 s34 i j (not_lt.1 h)]
  exact sub_self _

theorem xT_entries (p s23 s24 s34 : ZMod 2) :
    cm (xT p s23 s24 s34) 0 1 = p ∧ cm (xT p s23 s24 s34) 2 3 = s23 ∧
      cm (xT p s23 s24 s34) 2 4 = s24 ∧ cm (xT p s23 s24 s34) 3 4 = s34 := by
  simp [cm_xT, mP]

@[expose] def GammaB (k : ℕ) : Set Hc :=
  {a | a ∈ A1 ∧ a ∈ A2 ∧ a ≠ 1 ∧ labB (eA (cm a)) = k}

theorem GammaB_conj {k : ℕ} {a x : Hc} (ha : a ∈ GammaB k) (hx : x ∈ Tm) :
    x⁻¹ * a * x ∈ GammaB k := by
  obtain ⟨haA, haB, ha1, hal⟩ := ha
  have hxi : x⁻¹ ∈ NH1 := NH1.inv_mem (Tm_le_NH1 hx)
  have hA : x⁻¹ * a * x ∈ A1 := by
    have h := conj_NH1_A1 hxi haA
    rwa [inv_inv] at h
  have hB := (mem_A2_iff_eA haA).1 haB
  have hf := eA_conj_Tm hx haA
  refine ⟨hA, ?_, ?_, ?_⟩
  · rw [mem_A2_iff_eA hA, hf]
    have := inB_actT (cm x 0 1) (cm x 2 3) (cm x 2 4) (cm x 3 4) (eA (cm a)) hB
    exact this
  · intro h
    apply ha1
    have : a = x * (x⁻¹ * a * x) * x⁻¹ := by group
    rw [this, h]
    group
  · rw [hf, labB_actT _ _ _ _ _ hB, hal]

theorem exists_conjB_rep {k : Fin 6} {a : Hc} (ha : a ∈ GammaB k.val) :
    ∃ x ∈ Tm, a = x⁻¹ * eltA (labBRep k) * x := by
  obtain ⟨haA, haB, ha1, hal⟩ := ha
  have hB := (mem_A2_iff_eA haA).1 haB
  have hf0 : eA (cm a) ≠ 0 := fun h => ha1 ((eq_one_iff_eA haA).2 h)
  obtain ⟨p, s23, s24, s34, hact⟩ := labB_trans k (eA (cm a)) hB hf0 hal
  refine ⟨xT p s23 s24 s34, xT_mem p s23 s24 s34, ?_⟩
  obtain ⟨c1, c2, c3, c4⟩ := xT_entries p s23 s24 s34
  apply eA_inj haA
  · have h := conj_NH1_A1 (NH1.inv_mem (Tm_le_NH1 (xT_mem p s23 s24 s34))) (eltA_mem (labBRep k))
    rwa [inv_inv] at h
  · rw [eA_conj_Tm (xT_mem p s23 s24 s34) (eltA_mem _), eA_eltA, c1, c2, c3, c4, hact]

theorem gammaB_trans {k : Fin 6} {a b : Hc} (ha : a ∈ GammaB k.val) (hb : b ∈ GammaB k.val) :
    ∃ x ∈ Tm, b = x⁻¹ * a * x := by
  obtain ⟨xa, hxa, ea⟩ := exists_conjB_rep ha
  obtain ⟨xb, hxb, eb⟩ := exists_conjB_rep hb
  refine ⟨xa⁻¹ * xb, Tm.mul_mem (Tm.inv_mem hxa) hxb, ?_⟩
  rw [eb, ea]
  group

theorem ncard_GammaB (k : Fin 6) : (GammaB k.val).ncard = labBSize k := by
  have himg : (fun a : Hc => eA (cm a)) '' GammaB k.val =
      {f : Fin 6 → ZMod 2 | InB f ∧ f ≠ 0 ∧ labB f = k.val} := by
    ext f
    constructor
    · rintro ⟨a, ⟨haA, haB, ha1, hal⟩, rfl⟩
      exact ⟨(mem_A2_iff_eA haA).1 haB, fun h => ha1 ((eq_one_iff_eA haA).2 h), hal⟩
    · rintro ⟨hB, hf0, hl⟩
      refine ⟨eltA f, ⟨eltA_mem f, ?_, ?_, ?_⟩, eA_eltA f⟩
      · rw [mem_A2_iff_eA (eltA_mem f), eA_eltA]
        exact hB
      · intro h
        apply hf0
        have := eA_eltA f
        rw [h, eA_one] at this
        exact this.symm
      · rw [eA_eltA]
        exact hl
  have hinj : Set.InjOn (fun a : Hc => eA (cm a)) (GammaB k.val) := fun a ha b hb h =>
    eA_inj ha.1 hb.1 h
  rw [← hinj.ncard_image, himg]
  have hc := labB_card k
  rw [← hc, ← Set.ncard_coe_finset]
  congr 1
  ext f
  simp

theorem GammaB_zero : GammaB 0 = {zt} := by
  ext a
  constructor
  · rintro ⟨haA, haB, ha1, hal⟩
    have hf0 : eA (cm a) ≠ 0 := fun h => ha1 ((eq_one_iff_eA haA).2 h)
    have h := (labB_zero_iff _ ((mem_A2_iff_eA haA).1 haB) hf0).1 hal
    exact eA_inj haA zt_mem_A1 (h.trans eA_zt.symm)
  · rintro rfl
    refine ⟨zt_mem_A1, zt_mem_A2, zt_ne_one, ?_⟩
    rw [eA_zt]
    decide +kernel

theorem GammaB_one : GammaB 1 = ((A1 ⊓ A2 ⊓ U1 : Subgroup Hc) : Set Hc) \ {1, zt} := by
  ext a
  simp only [GammaB, Set.mem_setOf_eq, Set.mem_diff, SetLike.mem_coe, Subgroup.mem_inf,
    Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
  constructor
  · rintro ⟨haA, haB, ha1, hal⟩
    have hf0 : eA (cm a) ≠ 0 := fun h => ha1 ((eq_one_iff_eA haA).2 h)
    obtain ⟨h3, h4, h5, hz⟩ := (labB_one_iff _ ((mem_A2_iff_eA haA).1 haB) hf0).1 hal
    refine ⟨⟨⟨haA, haB⟩, (mem_U1_iff_eA haA).2 ⟨h3, h4, h5⟩⟩, ha1, fun h => hz ?_⟩
    rw [h, eA_zt]
  · rintro ⟨⟨⟨haA, haB⟩, haU⟩, ha1, haz⟩
    have hf0 : eA (cm a) ≠ 0 := fun h => ha1 ((eq_one_iff_eA haA).2 h)
    obtain ⟨h3, h4, h5⟩ := (mem_U1_iff_eA haA).1 haU
    refine ⟨haA, haB, ha1, (labB_one_iff _ ((mem_A2_iff_eA haA).1 haB) hf0).2
      ⟨h3, h4, h5, fun h => haz ?_⟩⟩
    exact eA_inj haA zt_mem_A1 (h.trans eA_zt.symm)

theorem GammaB_two : GammaB 2 = ((A1 ⊓ A2 ⊓ U2 : Subgroup Hc) : Set Hc) \ {1, zt} := by
  ext a
  simp only [GammaB, Set.mem_setOf_eq, Set.mem_diff, SetLike.mem_coe, Subgroup.mem_inf,
    Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
  constructor
  · rintro ⟨haA, haB, ha1, hal⟩
    have hf0 : eA (cm a) ≠ 0 := fun h => ha1 ((eq_one_iff_eA haA).2 h)
    obtain ⟨h0, h1, h3, h4, hz⟩ := (labB_two_iff _ ((mem_A2_iff_eA haA).1 haB) hf0).1 hal
    refine ⟨⟨⟨haA, haB⟩, (mem_U2_iff_eA haA).2 ⟨h0, h1, h3, h4⟩⟩, ha1, fun h => hz ?_⟩
    rw [h, eA_zt]
  · rintro ⟨⟨⟨haA, haB⟩, haU⟩, ha1, haz⟩
    have hf0 : eA (cm a) ≠ 0 := fun h => ha1 ((eq_one_iff_eA haA).2 h)
    obtain ⟨h0, h1, h3, h4⟩ := (mem_U2_iff_eA haA).1 haU
    refine ⟨haA, haB, ha1, (labB_two_iff _ ((mem_A2_iff_eA haA).1 haB) hf0).2
      ⟨h0, h1, h3, h4, fun h => haz ?_⟩⟩
    exact eA_inj haA zt_mem_A1 (h.trans eA_zt.symm)

theorem GammaB_three :
    GammaB 3 = {a | a ∈ A1 ∧ a ∈ A2 ∧ a ∈ Qh ∧ a ≠ 1 ∧ a ∉ U1 ∧ a ∉ U2} := by
  ext a
  simp only [GammaB, Set.mem_setOf_eq]
  constructor
  · rintro ⟨haA, haB, ha1, hal⟩
    have hf0 : eA (cm a) ≠ 0 := fun h => ha1 ((eq_one_iff_eA haA).2 h)
    obtain ⟨h3, h4, h5, h01⟩ := (labB_three_iff _ ((mem_A2_iff_eA haA).1 haB) hf0).1 hal
    refine ⟨haA, haB, (mem_Qh_iff_eA haA).2 ⟨h3, h4⟩, ha1, fun h => h5 ?_, fun h => h01 ?_⟩
    · exact ((mem_U1_iff_eA haA).1 h).2.2
    · have := (mem_U2_iff_eA haA).1 h
      exact ⟨this.1, this.2.1⟩
  · rintro ⟨haA, haB, haQ, ha1, haU1, haU2⟩
    have hf0 : eA (cm a) ≠ 0 := fun h => ha1 ((eq_one_iff_eA haA).2 h)
    obtain ⟨h3, h4⟩ := (mem_Qh_iff_eA haA).1 haQ
    refine ⟨haA, haB, ha1, (labB_three_iff _ ((mem_A2_iff_eA haA).1 haB) hf0).2
      ⟨h3, h4, fun h5 => haU1 ?_, fun h01 => haU2 ?_⟩⟩
    · exact (mem_U1_iff_eA haA).2 ⟨h3, h4, h5⟩
    · exact (mem_U2_iff_eA haA).2 ⟨h01.1, h01.2, h3, h4⟩

theorem B_orbits : ∃ Γ : Fin 6 → Set Hc,
    (∀ i j, i ≠ j → Disjoint (Γ i) (Γ j)) ∧
    (⋃ i, Γ i) = ((A1 ⊓ A2 : Subgroup Hc) : Set Hc) \ {1} ∧
    (∀ i, ∀ a ∈ Γ i, ∀ x ∈ Tm, x⁻¹ * a * x ∈ Γ i) ∧
    (∀ i, ∀ a ∈ Γ i, ∀ b ∈ Γ i, ∃ x ∈ Tm, b = x⁻¹ * a * x) ∧
    (∀ i, (Γ i).ncard = labBSize i) ∧
    Γ 0 = {zt} ∧
    Γ 1 = ((A1 ⊓ A2 ⊓ U1 : Subgroup Hc) : Set Hc) \ {1, zt} ∧
    Γ 2 = ((A1 ⊓ A2 ⊓ U2 : Subgroup Hc) : Set Hc) \ {1, zt} ∧
    Γ 3 = {a | a ∈ A1 ∧ a ∈ A2 ∧ a ∈ Qh ∧ a ≠ 1 ∧ a ∉ U1 ∧ a ∉ U2} := by
  refine ⟨fun k => GammaB k.val, ?_, ?_, ?_, ?_, ?_, GammaB_zero, GammaB_one, GammaB_two,
    GammaB_three⟩
  · intro i j hij
    rw [Set.disjoint_left]
    intro a ha hb
    exact hij (Fin.ext (ha.2.2.2.symm.trans hb.2.2.2))
  · ext a
    simp only [Set.mem_iUnion, Set.mem_diff, SetLike.mem_coe, Subgroup.mem_inf,
      Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, haA, haB, ha1, -⟩
      exact ⟨⟨haA, haB⟩, ha1⟩
    · rintro ⟨⟨haA, haB⟩, ha1⟩
      have hf0 : eA (cm a) ≠ 0 := fun h => ha1 ((eq_one_iff_eA haA).2 h)
      have hB := (mem_A2_iff_eA haA).1 haB
      have hlt : labB (eA (cm a)) < 6 := by
        rcases labB_lt (eA (cm a)) with h | h
        · exact h
        · exact absurd hB h
      exact ⟨⟨labB (eA (cm a)), hlt⟩, haA, haB, ha1, rfl⟩
  · intro i a ha x hx
    exact GammaB_conj ha hx
  · intro i a ha b hb
    exact gammaB_trans ha hb
  · intro i
    exact ncard_GammaB i

abbrev SJ (i j : Fin 5) : Prop := i.val ≤ 2 ∧ 2 ≤ j.val ∧ i < j

theorem lt_SJ : ∀ i j, SJ i j → i < j := fun _ _ h => h.2.2

theorem trans_SJ : ∀ i k j, SJ i k → SJ k j → SJ i j := by decide

theorem Jm_le_patSubJ : Jm ≤ patSubT SJ lt_SJ trans_SJ := by
  refine sup_le ?_ ?_
  · intro x hx
    rw [mem_A1] at hx
    rw [mem_patSubT]
    intro i j hij
    apply hx i j
    intro h
    refine hij ⟨by omega, by omega, ?_⟩
    show i.val < j.val
    omega
  · intro x hx
    rw [mem_A2] at hx
    rw [mem_patSubT]
    intro i j hij
    apply hx i j
    intro h
    refine hij ⟨by omega, by omega, ?_⟩
    show i.val < j.val
    omega

theorem mul_single_mul_apply (M N : Mt) (i j a b : Fin 5) :
    (M * Matrix.single i j (1 : ZMod 2) * N) a b = M a i * N j b := by
  rw [Matrix.mul_apply, Finset.sum_eq_single j]
  · rw [Matrix.mul_single_apply_same, mul_one]
  · intro m _ hm
    rw [Matrix.mul_single_apply_of_ne _ _ _ _ _ hm, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ j) h

theorem conj_unipS_apply (y : Hc) (i j : Fin 5) (hij : i < j) (a b : Fin 5) :
    cm (y * unipS i j hij 1 * y⁻¹) a b = (1 : Mt) a b + cm y a i * cm y⁻¹ j b := by
  have e : cm (y * unipS i j hij 1 * y⁻¹) = 1 + cm y * Matrix.single i j 1 * cm y⁻¹ := by
    have h1 : cm y * cm y⁻¹ = 1 := cm_mul_inv y
    rw [cm_mul, cm_mul, cm_unipS]
    calc cm y * (1 + Matrix.single i j 1) * cm y⁻¹
        = cm y * cm y⁻¹ + cm y * Matrix.single i j 1 * cm y⁻¹ := by noncomm_ring
      _ = 1 + cm y * Matrix.single i j 1 * cm y⁻¹ := by rw [h1]
  rw [e, Matrix.add_apply, mul_single_mul_apply]

theorem conj_Jm_Tm {x h : Hc} (hx : x ∈ Tm) (hh : h ∈ Jm) : x * h * x⁻¹ ∈ Jm := by
  have hmap : Jm.map (MulAut.conj x).toMonoidHom ≤ Jm := by
    show (A1 ⊔ A2).map _ ≤ A1 ⊔ A2
    rw [Subgroup.map_sup]
    refine sup_le_sup ?_ ?_
    · rintro _ ⟨a, ha, rfl⟩
      exact A1_conj_Tm hx ha
    · rintro _ ⟨a, ha, rfl⟩
      exact A2_conj_Tm hx ha
  exact hmap ⟨h, hh, rfl⟩

theorem normalizer_Jm_eq : Subgroup.normalizer (Jm : Set Hc) = Tm := by
  apply le_antisymm
  · intro x hx
    have hxi : x⁻¹ ∈ Subgroup.normalizer (Jm : Set Hc) := Subgroup.inv_mem _ hx
    have hconj : ∀ y : Hc, y ∈ Subgroup.normalizer (Jm : Set Hc) → ∀ (i j : Fin 5) (hij : i < j),
        unipS i j hij 1 ∈ Jm → ∀ a b : Fin 5, ¬ SJ a b → cm y a i * cm y⁻¹ j b = 0 := by
      intro y hy i j hij hu a b hab
      have h1 : y * unipS i j hij 1 * y⁻¹ ∈ Jm := (Subgroup.mem_normalizer_iff.1 hy _).1 hu
      have h3 := Jm_le_patSubJ h1 a b hab
      rw [Matrix.sub_apply, conj_unipS_apply] at h3
      generalize (1 : Mt) a b = r at h3
      generalize cm y a i * cm y⁻¹ j b = p at h3 ⊢
      revert h3
      revert r p
      decide
    have m02 : unipS 0 2 (by decide) 1 ∈ Jm :=
      Subgroup.mem_sup_left (unipS_mem_patSub hSA _ 1 ⟨by decide, by decide⟩)
    have m03 : unipS 0 3 (by decide) 1 ∈ Jm :=
      Subgroup.mem_sup_left (unipS_mem_patSub hSA _ 1 ⟨by decide, by decide⟩)
    have m24 : unipS 2 4 (by decide) 1 ∈ Jm :=
      Subgroup.mem_sup_right (unipS_mem_patSub hSA2 _ 1 ⟨by decide, by decide⟩)
    have x21 : cm x 2 1 = 0 := by
      have h := hconj x⁻¹ hxi 0 2 (by decide) m02 0 1 (by decide)
      rw [cm_00, one_mul, inv_inv] at h
      exact h
    have x31 : cm x 3 1 = 0 := by
      have h := hconj x⁻¹ hxi 0 3 (by decide) m03 0 1 (by decide)
      rw [cm_00, one_mul, inv_inv] at h
      exact h
    have x32 : cm x 3 2 = 0 := by
      have h := hconj x hx 2 4 (by decide) m24 3 4 (by decide)
      rw [cm_44, mul_one] at h
      exact h
    have low : ∀ i j : Fin 5, j < i → cm x i j = 0 := by
      intro i j hji
      by_cases hj : j = 0
      · subst hj
        rw [cm_col0 x i, Matrix.one_apply_ne (ne_of_gt hji)]
      · by_cases hi : i = 4
        · subst hi
          rw [cm_row4 x j, Matrix.one_apply_ne (ne_of_gt hji)]
        · have hc : (i = 2 ∧ j = 1) ∨ (i = 3 ∧ j = 1) ∨ (i = 3 ∧ j = 2) := by
            revert hj hi hji
            revert i j
            decide
          rcases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact x21
          · exact x31
          · exact x32
    have hdiag : cm x 1 1 = 1 ∧ cm x 2 2 = 1 ∧ cm x 3 3 = 1 := by
      have hd : (cm x).det = 1 := x.1.2
      have hd2 : (cm x).det = ∏ i : Fin 5, cm x i i := by
        apply Matrix.det_of_isUpperTriangular
        intro i j hij
        exact low i j hij
      rw [hd2, Fin.prod_univ_five, cm_00, cm_44] at hd
      revert hd
      generalize cm x 1 1 = a
      generalize cm x 2 2 = b
      generalize cm x 3 3 = c
      revert a b c
      decide
    have hall : ∀ i : Fin 5, cm x i i = 1 := by
      intro i
      fin_cases i
      · exact cm_00 x
      · exact hdiag.1
      · exact hdiag.2.1
      · exact hdiag.2.2
      · exact cm_44 x
    rw [mem_Tm]
    intro i j hij
    rw [Matrix.sub_apply]
    by_cases hij' : i = j
    · subst hij'
      rw [Matrix.one_apply_eq, hall i, sub_self]
    · have hji : j < i := lt_of_le_of_ne (not_lt.1 hij) (Ne.symm hij')
      rw [low i j hji, Matrix.one_apply_ne hij']
      exact sub_self _
  · intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      exact conj_Jm_Tm hx hh
    · intro hh
      have := conj_Jm_Tm (Tm.inv_mem hx) hh
      have e : x⁻¹ * (x * h * x⁻¹) * x⁻¹⁻¹ = h := by group
      rwa [e] at this

end CFSG.Quasithin.A94.L52
