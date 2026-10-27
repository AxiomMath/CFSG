module

public import CFSG.Quasithin.Vol2.Ch12Sec5L2G
public import CFSG.Quasithin.Background.JonesParshallWords

public section

namespace CFSG.Quasithin.H13

open CFSG.Quasithin S125 Matrix CFSG.LieType.SteinbergBR.BlockPar

local notation "SL5" => Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)
local notation "M5" => Matrix (Fin 5) (Fin 5) (ZMod 2)

namespace S125Gen

@[expose] noncomputable def pR (d e : ℕ) (hde : d + e = 5) : Subgroup SL5 :=
  (parJR (ZMod 2) (Fin d) (Fin e)).map (reindexSL (ZMod 2) hde).toMonoidHom

@[expose] noncomputable def pL (d e : ℕ) (hde : d + e = 5) : Subgroup SL5 :=
  (parJL (ZMod 2) (Fin d) (Fin e)).map (reindexSL (ZMod 2) hde).toMonoidHom

theorem reindex_apply5 {d e : ℕ} (hde : d + e = 5)
    (g : Matrix.SpecialLinearGroup (Fin d ⊕ Fin e) (ZMod 2)) (a b : Fin 5) :
    (reindexSL (ZMod 2) hde g).val a b =
      g.val ((sumEquiv hde).symm a) ((sumEquiv hde).symm b) := by
  rw [reindexSL_val, Matrix.reindex_apply, Matrix.submatrix_apply]

theorem symm_val_apply {d e : ℕ} (hde : d + e = 5) (g : SL5) (a b : Fin d ⊕ Fin e) :
    ((reindexSL (ZMod 2) hde).symm g).val a b = g.val (sumEquiv hde a) (sumEquiv hde b) := by
  have h := reindex_apply5 hde ((reindexSL (ZMod 2) hde).symm g) (sumEquiv hde a)
    (sumEquiv hde b)
  rw [MulEquiv.apply_symm_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply] at h
  exact h.symm

theorem sumEquiv_inl_val {d e : ℕ} (hde : d + e = 5) (i : Fin d) :
    sumEquiv hde (Sum.inl i) = ⟨i.val, by omega⟩ :=
  Fin.ext (sumEquiv_inl hde i)

theorem sumEquiv_inr_val {d e : ℕ} (hde : d + e = 5) (j : Fin e) :
    sumEquiv hde (Sum.inr j) = ⟨d + j.val, by omega⟩ :=
  Fin.ext (sumEquiv_inr hde j)

theorem mem_pR_iff {d e : ℕ} (hde : d + e = 5) (g : SL5) :
    g ∈ pR d e hde ↔ (∀ a b : Fin 5, b.val < d → d ≤ a.val → g.val a b = 0) ∧
      ∀ a b : Fin 5, a.val < d → b.val < d → g.val a b = (1 : M5) a b := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨hQ, h11⟩ := mem_parJR.1 hx
    have hQ' : x.val.toBlocks₂₁ = 0 := hQ
    refine ⟨fun a b hb ha => ?_, fun a b ha hb => ?_⟩
    · change (reindexSL (ZMod 2) hde x).val a b = 0
      rw [reindex_apply5, S125Tr3.sumEquiv_symm_of_le hde ha,
        S125Tr3.sumEquiv_symm_of_lt hde hb]
      exact congrFun₂ hQ' _ _
    · change (reindexSL (ZMod 2) hde x).val a b = _
      rw [reindex_apply5, S125Tr3.sumEquiv_symm_of_lt hde ha,
        S125Tr3.sumEquiv_symm_of_lt hde hb]
      have := congrFun₂ h11 ⟨a.val, ha⟩ ⟨b.val, hb⟩
      change x.val.toBlocks₁₁ ⟨a.val, ha⟩ ⟨b.val, hb⟩ = _
      rw [this, Matrix.one_apply, Matrix.one_apply]
      by_cases hab : a = b
      · subst hab
        simp
      · have : (⟨a.val, ha⟩ : Fin d) ≠ ⟨b.val, hb⟩ := fun h => hab (Fin.ext (by
          simpa using congrArg Fin.val h))
        simp [this, hab]
  · rintro ⟨h1, h2⟩
    refine ⟨(reindexSL (ZMod 2) hde).symm g, ?_, MulEquiv.apply_symm_apply _ _⟩
    refine mem_parJR.2 ⟨?_, ?_⟩
    · change ((reindexSL (ZMod 2) hde).symm g).val.toBlocks₂₁ = 0
      ext i j
      rw [Matrix.toBlocks₂₁, Matrix.of_apply, symm_val_apply, sumEquiv_inr_val,
        sumEquiv_inl_val]
      exact h1 _ _ j.2 (by simp)
    · ext i j
      rw [Matrix.toBlocks₁₁, Matrix.of_apply, symm_val_apply, sumEquiv_inl_val, sumEquiv_inl_val,
        h2 _ _ i.2 j.2, Matrix.one_apply, Matrix.one_apply]
      by_cases hij : i = j
      · subst hij
        simp
      · have : (⟨i.val, by omega⟩ : Fin 5) ≠ ⟨j.val, by omega⟩ := fun h => hij (Fin.ext (by
          simpa using congrArg Fin.val h))
        simp [this, hij]

theorem mem_pL_iff {d e : ℕ} (hde : d + e = 5) (g : SL5) :
    g ∈ pL d e hde ↔ (∀ a b : Fin 5, b.val < d → d ≤ a.val → g.val a b = 0) ∧
      ∀ a b : Fin 5, d ≤ a.val → d ≤ b.val → g.val a b = (1 : M5) a b := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨hQ, h22⟩ := mem_parJL.1 hx
    have hQ' : x.val.toBlocks₂₁ = 0 := hQ
    refine ⟨fun a b hb ha => ?_, fun a b ha hb => ?_⟩
    · change (reindexSL (ZMod 2) hde x).val a b = 0
      rw [reindex_apply5, S125Tr3.sumEquiv_symm_of_le hde ha,
        S125Tr3.sumEquiv_symm_of_lt hde hb]
      exact congrFun₂ hQ' _ _
    · change (reindexSL (ZMod 2) hde x).val a b = _
      rw [reindex_apply5, S125Tr3.sumEquiv_symm_of_le hde ha,
        S125Tr3.sumEquiv_symm_of_le hde hb]
      have := congrFun₂ h22 ⟨a.val - d, by omega⟩ ⟨b.val - d, by omega⟩
      change x.val.toBlocks₂₂ ⟨a.val - d, by omega⟩ ⟨b.val - d, by omega⟩ = _
      rw [this, Matrix.one_apply, Matrix.one_apply]
      by_cases hab : a = b
      · subst hab
        simp
      · have : (⟨a.val - d, by omega⟩ : Fin e) ≠ ⟨b.val - d, by omega⟩ := fun h => hab (Fin.ext (by
          have := congrArg Fin.val h
          simp at this
          omega))
        simp [this, hab]
  · rintro ⟨h1, h2⟩
    refine ⟨(reindexSL (ZMod 2) hde).symm g, ?_, MulEquiv.apply_symm_apply _ _⟩
    refine mem_parJL.2 ⟨?_, ?_⟩
    · change ((reindexSL (ZMod 2) hde).symm g).val.toBlocks₂₁ = 0
      ext i j
      rw [Matrix.toBlocks₂₁, Matrix.of_apply, symm_val_apply, sumEquiv_inr_val,
        sumEquiv_inl_val]
      exact h1 _ _ j.2 (by simp)
    · ext i j
      rw [Matrix.toBlocks₂₂, Matrix.of_apply, symm_val_apply, sumEquiv_inr_val, sumEquiv_inr_val,
        h2 _ _ (by simp) (by simp), Matrix.one_apply, Matrix.one_apply]
      by_cases hij : i = j
      · subst hij
        simp
      · have : (⟨d + i.val, by omega⟩ : Fin 5) ≠ ⟨d + j.val, by omega⟩ := fun h => hij (Fin.ext (by
          have := congrArg Fin.val h
          simp at this
          omega))
        simp [this, hij]

@[expose] noncomputable def tv (i j : Fin 5) (h : i ≠ j) : SL5 :=
  ⟨Matrix.transvection i j 1, Matrix.det_transvection_of_ne i j h 1⟩

theorem transvection_apply (i j a b : Fin 5) :
    Matrix.transvection i j (1 : ZMod 2) a b = (1 : M5) a b + if i = a ∧ j = b then 1 else 0 := by
  simp [Matrix.transvection, Matrix.single_apply]

theorem tv_mem_pR {i j : Fin 5} (h : i ≠ j) (hj : 2 ≤ j.val) : tv i j h ∈ pR 2 3 rfl := by
  refine (mem_pR_iff rfl _).2 ⟨fun a b hb ha => ?_, fun a b _ hb => ?_⟩
  · change Matrix.transvection i j (1 : ZMod 2) a b = 0
    rw [transvection_apply, Matrix.one_apply_ne (fun h' => by rw [h'] at ha; omega),
      ite_eq_right (fun h' => by have := congrArg Fin.val h'.2; omega), add_zero]
  · change Matrix.transvection i j (1 : ZMod 2) a b = _
    rw [transvection_apply, ite_eq_right (fun h' => by have := congrArg Fin.val h'.2; omega), add_zero]

theorem tv_mem_pL41 {i j : Fin 5} (h : i ≠ j) (hi : i.val ≤ 3) : tv i j h ∈ pL 4 1 rfl := by
  refine (mem_pL_iff rfl _).2 ⟨fun a b hb ha => ?_, fun a b ha _ => ?_⟩
  · change Matrix.transvection i j (1 : ZMod 2) a b = 0
    rw [transvection_apply, Matrix.one_apply_ne (fun h' => by rw [h'] at ha; omega),
      ite_eq_right (fun h' => by have := congrArg Fin.val h'.1; omega), add_zero]
  · change Matrix.transvection i j (1 : ZMod 2) a b = _
    rw [transvection_apply, ite_eq_right (fun h' => by have := congrArg Fin.val h'.1; omega), add_zero]

theorem tv_mem_pL32 {i j : Fin 5} (h : i ≠ j) (hi : i.val ≤ 2) : tv i j h ∈ pL 3 2 rfl := by
  refine (mem_pL_iff rfl _).2 ⟨fun a b hb ha => ?_, fun a b ha _ => ?_⟩
  · change Matrix.transvection i j (1 : ZMod 2) a b = 0
    rw [transvection_apply, Matrix.one_apply_ne (fun h' => by rw [h'] at ha; omega),
      ite_eq_right (fun h' => by have := congrArg Fin.val h'.1; omega), add_zero]
  · change Matrix.transvection i j (1 : ZMod 2) a b = _
    rw [transvection_apply, ite_eq_right (fun h' => by have := congrArg Fin.val h'.1; omega), add_zero]

theorem transvection_comm : ∀ i j : Fin 5, 3 ≤ i.val → j.val ≤ 1 →
    Matrix.transvection i j (1 : ZMod 2) = Matrix.transvection i 2 1 * Matrix.transvection 2 j 1 *
      Matrix.transvection i 2 1 * Matrix.transvection 2 j 1 := by
  intro i j hi hj
  fin_cases i <;> fin_cases j <;> simp at hi hj <;> ext a b <;> fin_cases a <;> fin_cases b <;>
    decide

theorem eq_top_of_tv {H : Subgroup SL5} {k : ℕ} (hk : 2 ≤ k)
    (h1 : ∀ i j : Fin 5, ∀ h : i ≠ j, 2 ≤ j.val → tv i j h ∈ H)
    (h2 : ∀ i j : Fin 5, ∀ h : i ≠ j, i.val ≤ k → tv i j h ∈ H) : H = ⊤ := by
  have key : ∀ i j : Fin 5, ∀ h : i ≠ j, tv i j h ∈ H := by
    intro i j h
    by_cases hj : 2 ≤ j.val
    · exact h1 i j h hj
    by_cases hi : i.val ≤ k
    · exact h2 i j h hi
    have hi3 : 3 ≤ i.val := by omega
    have hi2 : i ≠ 2 := fun h' => by rw [h'] at hi3; exact absurd hi3 (by decide)
    have h2j : (2 : Fin 5) ≠ j := fun h' => hj (by rw [← h']; decide)
    have e : tv i j h = tv i 2 hi2 * tv 2 j h2j * tv i 2 hi2 * tv 2 j h2j := by
      apply Subtype.ext
      exact transvection_comm i j hi3 (by omega)
    rw [e]
    exact H.mul_mem (H.mul_mem (H.mul_mem (h1 i 2 hi2 (by decide))
      (h2 2 j h2j (by change 2 ≤ k; omega))) (h1 i 2 hi2 (by decide)))
      (h2 2 j h2j (by change 2 ≤ k; omega))
  have hcl : Subgroup.closure (H : Set SL5) = ⊤ := by
    refine JonesParshall.closure_eq_top_of_transvection fun t => ?_
    apply Subgroup.subset_closure
    obtain ⟨i, j, hij, c⟩ := t
    rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) c with rfl | rfl
    · have : (TransvectionStruct.toSpecialLinearGroup ⟨i, j, hij, 0⟩ : SL5) = 1 := by
        apply Subtype.ext
        rw [TransvectionStruct.toSpecialLinearGroup_coe]
        simp [TransvectionStruct.toMatrix]
      rw [this]
      exact H.one_mem
    · have : (TransvectionStruct.toSpecialLinearGroup ⟨i, j, hij, 1⟩ : SL5) = tv i j hij :=
        Subtype.ext (TransvectionStruct.toSpecialLinearGroup_coe _)
      rw [this]
      exact key i j hij
  rwa [Subgroup.closure_eq] at hcl

theorem pR_sup_pL41 : pR 2 3 rfl ⊔ pL 4 1 rfl = ⊤ :=
  eq_top_of_tv (k := 3) (by norm_num) (fun _ _ h hj => Subgroup.mem_sup_left (tv_mem_pR h hj))
    (fun _ _ h hi => Subgroup.mem_sup_right (tv_mem_pL41 h hi))

theorem pR_sup_pL32 : pR 2 3 rfl ⊔ pL 3 2 rfl = ⊤ :=
  eq_top_of_tv (k := 2) le_rfl (fun _ _ h hj => Subgroup.mem_sup_left (tv_mem_pR h hj))
    (fun _ _ h hi => Subgroup.mem_sup_right (tv_mem_pL32 h hi))

@[expose] def src : Fin 10 → Fin 10 × Fin 5 × Fin 5 :=
  ![(4, 0, 2), (7, 0, 3), (7, 0, 2), (8, 0, 2), (7, 1, 3), (7, 1, 2), (8, 1, 2), (9, 2, 4),
    (9, 2, 3), (8, 3, 2)]

theorem src_props : ∀ k : Fin 10, (src k).2.1 ≠ (src k).2.2 ∧ 2 ≤ (src k).2.2.val ∧
    JonesParshall.wedgeMat (Matrix.transvection (src k).2.1 (src k).2.2 (1 : ZMod 2)) *ᵥ
        Pi.single (src k).1 1 = Pi.single (src k).1 1 + Pi.single k 1 := by
  intro k
  fin_cases k <;> refine ⟨by decide, by decide, ?_⟩ <;> funext t <;> fin_cases t <;> decide

theorem exists_transvec_wedge (k : Fin 10) : ∃ (m : Fin 10) (t : SL5), t ∈ pR 2 3 rfl ∧
    JonesParshall.wedgeMat (t : M5) *ᵥ Pi.single m 1 = Pi.single m 1 + Pi.single k 1 := by
  obtain ⟨hne, hj, hw⟩ := src_props k
  exact ⟨(src k).1, tv _ _ hne, tv_mem_pR hne hj, hw⟩

end S125Gen

end CFSG.Quasithin.H13
