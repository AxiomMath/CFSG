module

public import CFSG.Sporadic.Recognition.McLMultiplierInputs
public import CFSG.Sporadic.McL.Action

public section

namespace CFSG.Sporadic.Recognition.McLMultiplier

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.McL CFSG.LieType.Multipliers
open CFSG.Sporadic.McL.Native (orbitData genTables)

@[expose] noncomputable def mclGenG (z : ℤ) : J :=
  if z = 1 ∨ z = -1 then a else if z = 2 then b else b⁻¹

theorem rep_mclGenG (z : ℤ) :
    Rep 275 (genTables (orbitData ()) z) (mclGenG z) := by
  unfold genTables mclGenG
  split_ifs
  · exact rep_alpha
  · exact rep_beta
  · exact Rep.inv_of_invOK rep_beta actionChecks_parts.2.2.2.2.1

@[expose] noncomputable def mclGenE (k : ℕ) : J :=
  wordG mclGenG (mclGenWord k)

@[expose] noncomputable def mclGen (i : Fin 6) : J :=
  mclGenE i.val

@[expose] noncomputable def mclImgG (z : ℤ) : J :=
  if 0 < z then mclGenE (z - 1).toNat else (mclGenE (-z - 1).toNat)⁻¹

theorem mclImgG_letterZ (l : Fin 6 × Bool) :
    mclImgG (letterZ l) = if l.2 then mclGen l.1 else (mclGen l.1)⁻¹ := by
  obtain ⟨i, b⟩ := l
  have hi : (i.val : ℤ) + 1 - 1 = (i.val : ℤ) := by omega
  cases b
  · simp [mclImgG, letterZ, mclGen]
  · have h0 : (0 : ℤ) < (i.val : ℤ) + 1 := by omega
    simp [mclImgG, letterZ, h0, hi, mclGen]

theorem wordG_mclImgG_map_letterZ (w : List (Fin 6 × Bool)) :
    wordG mclImgG (w.map letterZ) = FreeGroup.lift mclGen (FreeGroup.mk w) := by
  induction w with
  | nil => rfl
  | cons l w ih =>
    simp only [wordG, List.map_cons, List.prod_cons] at ih ⊢
    rw [ih, show FreeGroup.mk (l :: w) = FreeGroup.mk [l] * FreeGroup.mk w from rfl, map_mul,
      mclImgG_letterZ]
    obtain ⟨i, b⟩ := l
    cases b
    · rw [show FreeGroup.mk [(i, false)] = (FreeGroup.of i)⁻¹ from rfl, map_inv,
        FreeGroup.lift_apply_of]
      simp
    · rw [show FreeGroup.mk [(i, true)] = FreeGroup.of i from rfl, FreeGroup.lift_apply_of]
      simp

abbrev mclTt (k : ℕ) : Table := mclT (orbitData ()) k

abbrev mclVv (k : ℕ) : Table := mclV (orbitData ()) k

abbrev mclLL : ℤ → Table := mclL (orbitData ())

theorem rep_mclTt (k : ℕ) : Rep 275 (mclTt k) (mclGenE k) :=
  Rep.wordT (by norm_num) _ fun l _ => rep_mclGenG l

theorem tab_facts (h : mclTabCheck = true) :
    (∀ k, k < 6 → invOK 275 (mclTt k) (mclVv k) = true) ∧
    (∀ r ∈ mclTabRels, wordT 275 mclLL r = idT 275) ∧
    wordT 275 mclLL (mclSurjA.map letterZ) = (orbitData ()).alpha ∧
    wordT 275 mclLL (mclSurjB.map letterZ) = (orbitData ()).beta := by
  unfold mclTabCheck at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩ := h
  exact ⟨h0, h1, h2, h3⟩

theorem rep_mclLL (h : mclTabCheck = true) {z : ℤ}
    (hz : z.natAbs ≤ 6) : Rep 275 (mclLL z) (mclImgG z) := by
  have hinv := (tab_facts h).1
  by_cases hp : 0 < z
  · simp only [mclLL, mclL, mclImgG, hp, ite_true]
    exact rep_mclTt _
  · have hk : (-z - 1).toNat < 6 := by omega
    simp only [mclLL, mclL, mclImgG, hp, ite_false]
    exact Rep.inv_of_invOK (rep_mclTt _) (hinv _ hk)

theorem eq_of_rep_eq {g h : J} {X : Table} (hg : Rep 275 X g)
    (hh : Rep 275 X h) : g = h := by
  refine FaithfulSMul.eq_of_smul_eq_smul (M := J) (α := Fin 275) fun i => ?_
  apply Fin.ext
  have e := (hg i.val i.isLt).symm.trans (hh i.val i.isLt)
  rwa [idx_of_lt g i.isLt, idx_of_lt h i.isLt] at e

theorem rep_wordG_mclImgG (h : mclTabCheck = true)
    (w : List (Fin 6 × Bool)) :
    Rep 275 (wordT 275 mclLL (w.map letterZ)) (wordG mclImgG (w.map letterZ)) := by
  refine Rep.wordT (by norm_num) _ fun z hz => ?_
  obtain ⟨l, -, rfl⟩ := List.mem_map.1 hz
  obtain ⟨i, b⟩ := l
  have hi := i.isLt
  refine rep_mclLL h ?_
  cases b <;> simp [letterZ] <;> omega

theorem lift_mclGen_eq_one (h : mclTabCheck = true)
    {w : List (Fin 6 × Bool)}
    (hw : w ∈ mclRels ++ (List.finRange 6).map fun i => (i, false) :: mclCommWord i) :
    FreeGroup.lift mclGen (FreeGroup.mk w) = 1 := by
  have h1 := (tab_facts h).2.1 (w.map letterZ) (List.mem_map_of_mem hw)
  have hr := rep_wordG_mclImgG h w
  rw [h1] at hr
  rw [← wordG_mclImgG_map_letterZ]
  exact eq_of_rep_eq hr (Rep.idT (by norm_num))

theorem lift_mclGen_rels (h : mclTabCheck = true) :
    ∀ r ∈ wordSet mclRels, FreeGroup.lift mclGen r = 1 := by
  intro r hr
  obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hr
  exact lift_mclGen_eq_one h (List.mem_append_left _ hv)

theorem lift_mclCommWord (h : mclTabCheck = true) (i : Fin 6) :
    FreeGroup.lift mclGen (FreeGroup.mk (mclCommWord i)) = mclGen i := by
  have h1 := lift_mclGen_eq_one h (w := (i, false) :: mclCommWord i)
    (List.mem_append_right _ (List.mem_map.2 ⟨i, List.mem_finRange i, rfl⟩))
  rw [show FreeGroup.mk ((i, false) :: mclCommWord i) =
      (FreeGroup.of i)⁻¹ * FreeGroup.mk (mclCommWord i) from rfl, map_mul, map_inv,
    FreeGroup.lift_apply_of, inv_mul_eq_one] at h1
  exact h1.symm

theorem lift_mclGen_mem_closure (v : FreeGroup (Fin 6)) :
    FreeGroup.lift mclGen v ∈ Subgroup.closure (Set.range mclGen) := by
  induction v using FreeGroup.induction_on with
  | one => simp
  | of i =>
    rw [FreeGroup.lift_apply_of]
    exact Subgroup.subset_closure (Set.mem_range_self i)
  | inv_of i =>
    rw [map_inv, FreeGroup.lift_apply_of]
    exact Subgroup.inv_mem _ (Subgroup.subset_closure (Set.mem_range_self i))
  | mul _ _ h₁ h₂ => rw [map_mul]; exact Subgroup.mul_mem _ h₁ h₂

theorem closure_mclGen (h : mclTabCheck = true) :
    Subgroup.closure (Set.range mclGen) = ⊤ := by
  rw [eq_top_iff, ← closure_ab, Subgroup.closure_le]
  have hA : a = FreeGroup.lift mclGen (FreeGroup.mk mclSurjA) := by
    rw [← wordG_mclImgG_map_letterZ]
    have hr := rep_wordG_mclImgG h mclSurjA
    rw [(tab_facts h).2.2.1] at hr
    exact eq_of_rep_eq rep_alpha hr
  have hB : b = FreeGroup.lift mclGen (FreeGroup.mk mclSurjB) := by
    rw [← wordG_mclImgG_map_letterZ]
    have hr := rep_wordG_mclImgG h mclSurjB
    rw [(tab_facts h).2.2.2] at hr
    exact eq_of_rep_eq rep_beta hr
  rintro _ (rfl | rfl)
  · rw [hA]; exact lift_mclGen_mem_closure _
  · rw [hB]; exact lift_mclGen_mem_closure _

end CFSG.Sporadic.Recognition.McLMultiplier
