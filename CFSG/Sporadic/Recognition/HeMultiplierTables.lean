module

public import CFSG.Sporadic.Recognition.HeMultiplierInputs
public import CFSG.Sporadic.He.Simple

public section

namespace CFSG.Sporadic.Recognition.HeMultiplier

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.He CFSG.Sporadic.He.Native
  CFSG.LieType.Multipliers

@[expose] noncomputable def heGenE (k : ℕ) : J :=
  wordG genG (heGenWord k)

@[expose] noncomputable def heGen (i : Fin 4) : J :=
  heGenE i.val

@[expose] noncomputable def heImgG (z : ℤ) : J :=
  if 0 < z then heGenE (z - 1).toNat else (heGenE (-z - 1).toNat)⁻¹

theorem heImgG_letterZ (l : Fin 4 × Bool) :
    heImgG (letterZ l) = if l.2 then heGen l.1 else (heGen l.1)⁻¹ := by
  obtain ⟨i, b⟩ := l
  have hi : (i.val : ℤ) + 1 - 1 = (i.val : ℤ) := by omega
  cases b
  · simp [heImgG, letterZ, heGen]
  · have h0 : (0 : ℤ) < (i.val : ℤ) + 1 := by omega
    simp [heImgG, letterZ, h0, hi, heGen]

theorem wordG_heImgG_map_letterZ (w : List (Fin 4 × Bool)) :
    wordG heImgG (w.map letterZ) = FreeGroup.lift heGen (FreeGroup.mk w) := by
  induction w with
  | nil => rfl
  | cons l w ih =>
    simp only [wordG, List.map_cons, List.prod_cons] at ih ⊢
    rw [ih, show FreeGroup.mk (l :: w) = FreeGroup.mk [l] * FreeGroup.mk w from rfl, map_mul,
      heImgG_letterZ]
    obtain ⟨i, b⟩ := l
    cases b
    · rw [show FreeGroup.mk [(i, false)] = (FreeGroup.of i)⁻¹ from rfl, map_inv,
        FreeGroup.lift_apply_of]
      simp
    · rw [show FreeGroup.mk [(i, true)] = FreeGroup.of i from rfl, FreeGroup.lift_apply_of]
      simp

abbrev heT (k : ℕ) : Table := heImg (orbitData ()) k

abbrev heV (k : ℕ) : Table := invT 8330 (heT k)

abbrev heL : ℤ → Table :=
  heImgLetter (heT 0) (heT 1) (heT 2) (heT 3) (heV 0) (heV 1) (heV 2) (heV 3)

theorem rep_heT (k : ℕ) : Rep 8330 (heT k) (heGenE k) :=
  Rep.wordT (by norm_num) _ fun l _ => rep_gen l

theorem tab_facts (h : heTabCheck = true) :
    (∀ k, k < 4 → invOK 8330 (heT k) (heV k) = true) ∧
    (∀ r ∈ heTabRels, wordT 8330 heL r = idT 8330) ∧
    wordT 8330 heL heSurjA = (orbitData ()).alpha ∧
    wordT 8330 heL heSurjB = (orbitData ()).beta := by
  unfold heTabCheck at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  refine ⟨fun k hk => ?_, h4, h5, h6⟩
  interval_cases k
  exacts [h0, h1, h2, h3]

theorem heImgLetter_vals (T0 T1 T2 T3 V0 V1 V2 V3 : Table) :
    heImgLetter T0 T1 T2 T3 V0 V1 V2 V3 1 = T0 ∧ heImgLetter T0 T1 T2 T3 V0 V1 V2 V3 2 = T1 ∧
      heImgLetter T0 T1 T2 T3 V0 V1 V2 V3 3 = T2 ∧ heImgLetter T0 T1 T2 T3 V0 V1 V2 V3 4 = T3 ∧
      heImgLetter T0 T1 T2 T3 V0 V1 V2 V3 (-1) = V0 ∧
      heImgLetter T0 T1 T2 T3 V0 V1 V2 V3 (-2) = V1 ∧
      heImgLetter T0 T1 T2 T3 V0 V1 V2 V3 (-3) = V2 ∧
      heImgLetter T0 T1 T2 T3 V0 V1 V2 V3 (-4) = V3 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem rep_heL (h : heTabCheck = true) {z : ℤ} (hz0 : z ≠ 0)
    (hz : z.natAbs ≤ 4) : Rep 8330 (heL z) (heImgG z) := by
  have hinv := (tab_facts h).1
  have hz' : z = 1 ∨ z = 2 ∨ z = 3 ∨ z = 4 ∨ z = -1 ∨ z = -2 ∨ z = -3 ∨ z = -4 := by omega
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8⟩ := heImgLetter_vals (heT 0) (heT 1) (heT 2) (heT 3)
    (heV 0) (heV 1) (heV 2) (heV 3)
  rcases hz' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [show heL 1 = heT 0 from e1]; exact rep_heT 0
  · rw [show heL 2 = heT 1 from e2]; exact rep_heT 1
  · rw [show heL 3 = heT 2 from e3]; exact rep_heT 2
  · rw [show heL 4 = heT 3 from e4]; exact rep_heT 3
  · rw [show heL (-1) = heV 0 from e5]
    exact Rep.inv_of_invOK (rep_heT 0) (hinv 0 (by norm_num))
  · rw [show heL (-2) = heV 1 from e6]
    exact Rep.inv_of_invOK (rep_heT 1) (hinv 1 (by norm_num))
  · rw [show heL (-3) = heV 2 from e7]
    exact Rep.inv_of_invOK (rep_heT 2) (hinv 2 (by norm_num))
  · rw [show heL (-4) = heV 3 from e8]
    exact Rep.inv_of_invOK (rep_heT 3) (hinv 3 (by norm_num))

theorem eq_of_rep_eq {g h : J} {X : Table} (hg : Rep 8330 X g)
    (hh : Rep 8330 X h) : g = h := by
  refine FaithfulSMul.eq_of_smul_eq_smul (M := J) (α := Fin 8330) fun i => ?_
  apply Fin.ext
  have e := (hg i.val i.isLt).symm.trans (hh i.val i.isLt)
  rwa [idx_of_lt g i.isLt, idx_of_lt h i.isLt] at e

theorem rep_wordG_heImgG (h : heTabCheck = true)
    (w : List (Fin 4 × Bool)) :
    Rep 8330 (wordT 8330 heL (w.map letterZ)) (wordG heImgG (w.map letterZ)) := by
  refine Rep.wordT (by norm_num) _ fun z hz => ?_
  obtain ⟨l, -, rfl⟩ := List.mem_map.1 hz
  obtain ⟨i, b⟩ := l
  have hi := i.isLt
  refine rep_heL h ?_ ?_
  · cases b <;> simp [letterZ] <;> omega
  · cases b <;> simp [letterZ] <;> omega

theorem lift_heGen_eq_one (h : heTabCheck = true)
    {w : List (Fin 4 × Bool)}
    (hw : w ∈ heRels ++ (List.finRange 4).map fun i => (i, false) :: heCommWord i) :
    FreeGroup.lift heGen (FreeGroup.mk w) = 1 := by
  have h1 := (tab_facts h).2.1 (w.map letterZ) (List.mem_map_of_mem hw)
  have hr := rep_wordG_heImgG h w
  rw [h1] at hr
  rw [← wordG_heImgG_map_letterZ]
  exact eq_of_rep_eq hr (Rep.idT (by norm_num))

theorem lift_heGen_rels (h : heTabCheck = true) :
    ∀ r ∈ wordSet heRels, FreeGroup.lift heGen r = 1 := by
  intro r hr
  obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hr
  exact lift_heGen_eq_one h (List.mem_append_left _ hv)

theorem lift_heCommWord (h : heTabCheck = true) (i : Fin 4) :
    FreeGroup.lift heGen (FreeGroup.mk (heCommWord i)) = heGen i := by
  have h1 := lift_heGen_eq_one h (w := (i, false) :: heCommWord i)
    (List.mem_append_right _ (List.mem_map.2 ⟨i, List.mem_finRange i, rfl⟩))
  rw [show FreeGroup.mk ((i, false) :: heCommWord i) =
      (FreeGroup.of i)⁻¹ * FreeGroup.mk (heCommWord i) from rfl, map_mul, map_inv,
    FreeGroup.lift_apply_of, inv_mul_eq_one] at h1
  exact h1.symm

theorem lift_heGen_mem_closure (v : FreeGroup (Fin 4)) :
    FreeGroup.lift heGen v ∈ Subgroup.closure (Set.range heGen) := by
  induction v using FreeGroup.induction_on with
  | one => simp
  | of i =>
    rw [FreeGroup.lift_apply_of]
    exact Subgroup.subset_closure (Set.mem_range_self i)
  | inv_of i =>
    rw [map_inv, FreeGroup.lift_apply_of]
    exact Subgroup.inv_mem _ (Subgroup.subset_closure (Set.mem_range_self i))
  | mul _ _ h₁ h₂ => rw [map_mul]; exact Subgroup.mul_mem _ h₁ h₂

theorem closure_heGen (h : heTabCheck = true) :
    Subgroup.closure (Set.range heGen) = ⊤ := by
  rw [eq_top_iff, ← closure_ab, Subgroup.closure_le]
  have hA : a = FreeGroup.lift heGen (FreeGroup.mk (ofCodes surjACodes)) := by
    rw [← wordG_heImgG_map_letterZ]
    have hr := rep_wordG_heImgG h (ofCodes surjACodes)
    rw [show (ofCodes surjACodes).map letterZ = heSurjA from rfl, (tab_facts h).2.2.1] at hr
    exact eq_of_rep_eq rep_alpha hr
  have hB : b = FreeGroup.lift heGen (FreeGroup.mk (ofCodes surjBCodes)) := by
    rw [← wordG_heImgG_map_letterZ]
    have hr := rep_wordG_heImgG h (ofCodes surjBCodes)
    rw [show (ofCodes surjBCodes).map letterZ = heSurjB from rfl, (tab_facts h).2.2.2] at hr
    exact eq_of_rep_eq rep_beta hr
  rintro _ (rfl | rfl)
  · rw [hA]; exact lift_heGen_mem_closure _
  · rw [hB]; exact lift_heGen_mem_closure _

end CFSG.Sporadic.Recognition.HeMultiplier
