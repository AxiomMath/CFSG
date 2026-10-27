module

public import CFSG.Quasithin.Recognition.L34AmalgamIsoGlueData
public import CFSG.Quasithin.Recognition.L34AmalgamIsoPres

public section

namespace CFSG.Quasithin.L34Amalgam

open MulAction CFSG.ComponentClassification.WittDesign CFSG.Quasithin.Asc94

abbrev barB : Subgroup M22 := m22TwoStab ⊓ m22PtHexStab

structure IsAutB (θ : M22 → M22) : Prop where
  mem : ∀ g ∈ barB, θ g ∈ barB
  mul : ∀ g ∈ barB, ∀ h ∈ barB, θ (g * h) = θ g * θ h
  inj : ∀ g ∈ barB, ∀ h ∈ barB, θ g = θ h → g = h

theorem gen_mem_barB {i : Fin 5} (hi : i.val < 3) :
    gen i ∈ barB := by
  refine closure_c_le_B (Subgroup.subset_closure ⟨i, ?_, rfl⟩)
  fin_cases i <;> simp_all

theorem evalW_mem_barB {w : List (Fin 5 × Bool)}
    (hw : ∀ x ∈ w, x.1.val < 3) :
    evalW gen w ∈ barB := by
  refine closure_c_le_B (evalW_mem_closure gen _ w fun x hx => ?_)
  have := hw x hx
  rcases x with ⟨i, b⟩
  fin_cases i <;> simp_all

theorem evalW_congr {X : Type*} [Group X] {f g : Fin 5 → X} {w : List (Fin 5 × Bool)}
    (h : ∀ x ∈ w, f x.1 = g x.1) : evalW f w = evalW g w := by
  unfold evalW
  congr 1
  refine List.map_congr_left fun x hx => ?_
  rw [h x hx]

namespace IsAutB

variable {θ : M22 → M22} (hθ : IsAutB θ)
include hθ

theorem map_one : θ 1 = 1 := by
  have h := hθ.mul 1 barB.one_mem 1 barB.one_mem
  rw [one_mul] at h
  have h' : θ 1 * θ 1 = θ 1 * 1 := by rw [mul_one]; exact h.symm
  exact mul_left_cancel h'

theorem map_inv {g : M22} (hg : g ∈ barB) : θ g⁻¹ = (θ g)⁻¹ := by
  have h := hθ.mul g hg g⁻¹ (barB.inv_mem hg)
  rw [mul_inv_cancel, hθ.map_one] at h
  exact eq_inv_of_mul_eq_one_right h.symm

theorem ne_one {g : M22} (hg : g ∈ barB) (hg1 : g ≠ 1) : θ g ≠ 1 := fun h =>
  hg1 (hθ.inj g hg 1 barB.one_mem (h.trans hθ.map_one.symm))

theorem map_evalW {w : List (Fin 5 × Bool)}
    (hw : ∀ x ∈ w, x.1.val < 3) :
    θ (evalW gen w) = evalW (fun i => θ (gen i)) w := by
  induction w with
  | nil => exact hθ.map_one
  | cons x w ih =>
    have hw' : ∀ y ∈ w, y.1.val < 3 := fun y hy => hw y (List.mem_cons_of_mem _ hy)
    have hx := hw x List.mem_cons_self
    have e : ∀ f : Fin 5 → M22, evalW f (x :: w) = cond x.2 (f x.1) (f x.1)⁻¹ * evalW f w := by
      intro f
      simp [evalW]
    have hg : cond x.2 (gen x.1) (gen x.1)⁻¹ ∈ barB := by
      rcases x with ⟨i, b⟩
      cases b
      · exact barB.inv_mem (gen_mem_barB hx)
      · exact gen_mem_barB hx
    rw [e, e, hθ.mul _ hg _ (evalW_mem_barB hw'), ih hw']
    congr 1
    rcases x with ⟨i, b⟩
    cases b
    · exact hθ.map_inv (gen_mem_barB hx)
    · rfl

theorem pow_three {g : M22} (hg : g ∈ barB) (h3 : g ^ 3 = 1) : θ g ^ 3 = 1 := by
  rw [pow_three'] at h3
  have h := hθ.mul (g * g) (barB.mul_mem hg hg) g hg
  rw [hθ.mul g hg g hg, h3, hθ.map_one] at h
  rw [pow_three', ← h]

theorem conj {c : M22} (hc : c ∈ barB) : IsAutB (fun g => c * θ g * c⁻¹) where
  mem g hg := barB.mul_mem (barB.mul_mem hc (hθ.mem g hg)) (barB.inv_mem hc)
  mul g hg h hh := by
    rw [hθ.mul g hg h hh]
    group
  inj g hg h hh e := hθ.inj g hg h hh (mul_left_cancel (mul_right_cancel e))

end IsAutB

theorem crdTL_getD (x : Fin 16) : crdTL.getD x.val tid = tab (crd x) := by
  rw [crdTL, List.getD_eq_getElem _ _ (by simp), List.getElem_map, List.getElem_finRange]
  rfl

theorem mem_barA1_iff_tab {g : M22} :
    g ∈ barA1 ↔ crdTL.contains (tab g) = true := by
  rw [List.contains_iff_mem, crdTL, List.mem_map]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x, List.mem_finRange x, rfl⟩
  · rintro ⟨x, -, hx⟩
    exact ⟨x, tab_injective hx⟩

theorem genTL_get0 : genTL.getD 0 tid = tab (gen 0) := rfl

theorem genTL_get1 : genTL.getD 1 tid = tab (gen 1) := rfl

theorem genTL_get2 : genTL.getD 2 tid = tab (gen 2) := rfl

theorem genTL_get3 : genTL.getD 3 tid = tab (gen 3) := rfl

theorem genTL_get4 : genTL.getD 4 tid = tab (gen 4) := rfl

theorem genTiL_get2 : genTiL.getD 2 tid = tab (gen 2)⁻¹ := rfl

theorem genTiL_get3 : genTiL.getD 3 tid = tab (gen 3)⁻¹ := rfl

theorem genTiL_get4 : genTiL.getD 4 tid = tab (gen 4)⁻¹ := rfl

theorem genTL_getD' (i : ℕ) (hi : i < 5) : genTL.getD i tid = tab (gen ⟨i, hi⟩) :=
  genTL_getD ⟨i, hi⟩

theorem pq_facts :
    gen 0 ∈ barA2 ∧ gen 0 ∉ barA1 ∧ gen 1 ∈ barA1 ∧ gen 1 ∉ barA2 ∧
      bT1 * gen 0 * bT1⁻¹ ∉ m22PtHexStab ∧ bT2 * gen 1 * bT2⁻¹ ∉ m22TwoStab := by
  have h := pq_ok
  simp only [pqCheck, Bool.and_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  rw [genTL_get0] at h1 h2
  rw [genTL_get1] at h3 h4
  rw [genTL_get3, genTL_get0, genTiL_get3, ← tab_mul, ← tab_mul, gen_three] at h5
  rw [genTL_get4, genTL_get1, genTiL_get4, ← tab_mul, ← tab_mul, gen_four,
    show (1 : ℕ) = (1 : Fin 22).val from rfl, tab_getD] at h6
  refine ⟨fixesF_tab.mp h1, fun hm => ?_, mem_barA1_iff_tab.mpr h3, fun hm => ?_, fun hm => ?_,
    fun hm => h6 (mem_m22TwoStab_iff.mp hm).2⟩
  · rw [mem_barA1_iff_tab, h2] at hm
    exact absurd hm (by decide)
  · rw [← fixesF_tab, h4] at hm
    exact absurd hm (by decide)
  · rw [mem_ptHex_iff_tab, h5] at hm
    exact absurd hm.2 (by decide)

theorem exists_a2W
    {g : M22} (hg : g ∈ barA2) :
    ∃ i < 16, evalW gen (word (a2W.getD i "")) = g := by
  have h := a2_ok
  simp only [a2Check, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨hnd, hlen⟩, hall⟩ := h
  have hmem : ∀ i : Fin 16, a2W.getD i "" ∈ a2W := fun i => by
    rw [List.getD_eq_getElem _ _ (by rw [hlen]; exact i.2)]
    exact List.getElem_mem _
  let f : Fin 16 → ↥barA2 := fun i => ⟨evalW gen (word (a2W.getD i "")), by
    rw [← fixesF_tab, ← wtab_eq]
    exact (hall _ (hmem i)).2⟩
  have hf : Function.Injective f := by
    intro i j hij
    have e : wtab genTL genTiL (a2W.getD i "") = wtab genTL genTiL (a2W.getD j "") := by
      rw [wtab_eq, wtab_eq]
      exact congrArg tab (congrArg Subtype.val hij)
    have hi : i.val < (a2W.map (wtab genTL genTiL)).length := by simp [hlen]
    have hj : j.val < (a2W.map (wtab genTL genTiL)).length := by simp [hlen]
    have e' : (a2W.map (wtab genTL genTiL))[i.val] = (a2W.map (wtab genTL genTiL))[j.val] := by
      rw [List.getElem_map, List.getElem_map, ← List.getD_eq_getElem _ "",
        ← List.getD_eq_getElem _ ""]
      exact e
    exact Fin.ext ((hnd.getElem_inj_iff).mp e')
  have hbij := hf.bijective_of_nat_card_le (by rw [card_barA2, Nat.card_eq_fintype_card,
    Fintype.card_fin])
  obtain ⟨i, hi⟩ := hbij.2 ⟨g, hg⟩
  exact ⟨i, i.2, congrArg Subtype.val hi⟩

theorem mem_A1_or_A2
    {g : M22} (hg : g ∈ barB)
    (h2 : g * g = 1) : g ∈ barA1 ∨ g ∈ barA2 := by
  obtain ⟨s, hs, rfl⟩ := exists_bWord hg.1 hg.2
  have h := inv_ok
  simp only [invCheck, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    beq_eq_false_iff_ne, ne_eq] at h
  rcases h s hs with (h | h) | h
  · exact absurd (by rw [wtab_eq, ← tab_mul, h2, tab_one]) h
  · exact Or.inl (mem_barA1_iff_tab.mpr (by rwa [wtab_eq] at h))
  · exact Or.inr (fixesF_tab.mp (by rwa [wtab_eq] at h))

theorem exists_conj_r
    {g : M22} (hg : g ∈ barB)
    (h3 : g ^ 3 = 1) (h1 : g ≠ 1) :
    ∃ c ∈ barB, c * g * c⁻¹ = gen 2 ∨ c * g * c⁻¹ = (gen 2)⁻¹ := by
  obtain ⟨s, hs, rfl⟩ := exists_bWord hg.1 hg.2
  obtain ⟨i, hi, his⟩ := List.mem_iff_getElem.mp hs
  have hiD : bWords.getD i "" = s := by rw [List.getD_eq_getElem _ _ hi, his]
  have h := conj_ok
  simp only [conjCheck, List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.and_eq_true,
    Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq, beq_iff_eq] at h
  have hi' : i < 192 := by rw [← bWords_length]; exact hi
  rcases h i hi' with (h | h) | ⟨hl, h⟩
  · rw [hiD, wtab_eq, ← tab_one] at h
    exact absurd (tab_injective h) h1
  · rw [hiD, wtab_eq, ← tab_mul, ← tab_mul, ← pow_three, h3, tab_one] at h
    exact absurd rfl h
  · refine ⟨evalW gen (word (cjW.getD i "")), evalW_mem_barB (lettersB_iff.mp hl), ?_⟩
    rw [hiD, wtab_eq, wtab_eq, wtabI_eq, ← tab_mul, ← tab_mul, genTL_get2, genTiL_get2] at h
    rcases h with h | h
    · exact Or.inl (tab_injective h)
    · exact Or.inr (tab_injective h)

theorem map_closure_gen₂ :
    (Subgroup.closure (gen₂ '' {0, 1, 2})).map m22PtHexStab.subtype =
    Subgroup.closure (gen '' {0, 1, 2}) := by
  rw [MonoidHom.map_closure]
  congr 1
  ext g
  simp only [Set.mem_image, Subgroup.coe_subtype]
  constructor
  · rintro ⟨_, ⟨j, hj, rfl⟩, rfl⟩
    exact ⟨j, hj, (coe_gen₂ (by rintro rfl; simp at hj)).symm⟩
  · rintro ⟨j, hj, rfl⟩
    exact ⟨_, ⟨j, hj, rfl⟩, coe_gen₂ (by rintro rfl; simp at hj)⟩

theorem bB2_le_closure :
    bB2 ≤ Subgroup.closure (gen₂ '' {0, 1, 2}) := by
  intro g hg
  have h : (g : M22) ∈ (Subgroup.closure (gen₂ '' {0, 1, 2})).map m22PtHexStab.subtype := by
    rw [map_closure_gen₂]
    exact mem_closure_of_mem_B hg g.2
  obtain ⟨g', hg', e⟩ := h
  rwa [show g = g' from Subtype.ext e.symm]

theorem evalW_mem_two
    {w : List (Fin 5 × Bool)}
    (hw : ∀ x ∈ w, x.1 ≠ 4) :
    evalW gen w ∈ m22TwoStab := by
  rw [← closure_gen_P1]
  refine evalW_mem_closure gen _ w fun x hx => ?_
  have := hw x hx
  rcases x with ⟨i, b⟩
  fin_cases i <;> simp_all

theorem evalW_mem_ptHex
    {w : List (Fin 5 × Bool)} (hw : ∀ x ∈ w, x.1 ≠ 3) :
    evalW gen w ∈ m22PtHexStab := by
  rw [← closure_gen_P2]
  refine evalW_mem_closure gen _ w fun x hx => ?_
  have := hw x hx
  rcases x with ⟨i, b⟩
  fin_cases i <;> simp_all

theorem evalT_wtab (σ : List String) (w : List (Fin 5 × Bool)) :
    evalT (fun j => wtab genTL genTiL (σ.getD j "")) (fun j => wtabI genTL genTiL (σ.getD j ""))
      w = tab (evalW (fun j => evalW gen (word (σ.getD j ""))) w) := by
  rw [tab_evalW]
  exact congrArg₂ (fun f g => evalT f g w) (funext fun j => wtab_eq _)
    (funext fun j => wtabI_eq _)

theorem word_empty : word "" = [] := rfl

theorem exists_aut_factor_of_r
    {θ : M22 → M22} (hθ : IsAutB θ)
    (hA1 : ∀ g ∈ barB, θ g ∈ barA1 ↔ g ∈ barA1) (hA2 : ∀ g ∈ barB, θ g ∈ barA2 ↔ g ∈ barA2)
    (hr : θ (gen 2) = gen 2 ∨ θ (gen 2) = (gen 2)⁻¹) :
    ∃ (α₁ : ↥m22TwoStab ≃* ↥m22TwoStab) (α₂ : ↥m22PtHexStab ≃* ↥m22PtHexStab),
      (∀ g : ↥m22TwoStab, ((α₁ g : ↥m22TwoStab) : M22) ∈ m22PtHexStab ↔
        (g : M22) ∈ m22PtHexStab) ∧
      (∀ g : ↥m22PtHexStab, ((α₂ g : ↥m22PtHexStab) : M22) ∈ m22TwoStab ↔
        (g : M22) ∈ m22TwoStab) ∧
      ∀ (g : M22) (h₁ : g ∈ m22TwoStab) (h₂ : g ∈ m22PtHexStab),
        θ ((α₁ ⟨g, h₁⟩ : ↥m22TwoStab) : M22) = ((α₂ ⟨g, h₂⟩ : ↥m22PtHexStab) : M22) := by
  obtain ⟨hp2, hp1, hq1, hq2, -, -⟩ := pq_facts
  have hp : gen 0 ∈ barB := gen_mem_barB (by decide)
  have hq : gen 1 ∈ barB := gen_mem_barB (by decide)
  have hθp2 : θ (gen 0) ∈ barA2 := (hA2 _ hp).mpr hp2
  have hθp1 : θ (gen 0) ∉ barA1 := fun h => hp1 ((hA1 _ hp).mp h)
  have hθq1 : θ (gen 1) ∈ barA1 := (hA1 _ hq).mpr hq1
  have hθq2 : θ (gen 1) ∉ barA2 := fun h => hq2 ((hA2 _ hq).mp h)
  obtain ⟨i, hi, hiθ⟩ := exists_a2W hθp2
  obtain ⟨x, hx⟩ := hθq1
  set Tp := wtab genTL genTiL (a2W.getD i "") with hTp
  set Tq := crdTL.getD x.val tid with hTq
  have hTp' : Tp = tab (θ (gen 0)) := by rw [hTp, wtab_eq, hiθ]
  have hTq' : Tq = tab (θ (gen 1)) := by rw [hTq, crdTL_getD, hx]
  set e : ℕ := if θ (gen 2) = gen 2 then 0 else 1 with he
  have he2 : e < 2 := by rw [he]; split_ifs <;> decide
  set Tr := if e = 0 then genTL.getD 2 tid else genTiL.getD 2 tid with hTr
  set TR := if e = 0 then genTiL.getD 2 tid else genTL.getD 2 tid with hTR
  have hTr' : Tr = tab (θ (gen 2)) ∧ TR = tab (θ (gen 2))⁻¹ := by
    rw [hTr, hTR, genTL_get2, genTiL_get2]
    by_cases h : θ (gen 2) = gen 2
    · have : e = 0 := by rw [he, ite_eq_left h]
      rw [ite_eq_left this, ite_eq_left this, h]
      exact ⟨rfl, rfl⟩
    · have : e ≠ 0 := by rw [he, ite_eq_right h]; decide
      rw [ite_eq_right this, ite_eq_right this, hr.resolve_left h, inv_inv]
      exact ⟨rfl, rfl⟩
  clear_value Tp Tq Tr TR e
  have hg := glue_ok
  simp only [glueCheck, List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.and_eq_true,
    decide_eq_true_eq, beq_iff_eq] at hg
  have hc := hg i hi x.val x.2 e he2
  rw [← hTp, ← hTq, ← hTr, ← hTR] at hc
  have hc1 : ¬ crdTL.contains Tp = true := by
    rw [hTp', ← mem_barA1_iff_tab]
    exact hθp1
  have hc2 : ¬ fixesF Tq = true := by
    rw [hTq', fixesF_tab]
    exact hθq2
  obtain ⟨⟨hk, hl⟩, hcheck⟩ := hc.resolve_left (by rintro (h | h); exacts [hc1 h, hc2 h])
  set w := witL.getD ((16 * i + x.val) * 2 + e) (0, 0) with hw
  set σ := s1W.getD w.2 [] with hσ
  set ρ := rhW.getD w.1 [] with hρ
  have hσmem : σ ∈ s1W := by rw [hσ, List.getD_eq_getElem _ _ hl]; exact List.getElem_mem _
  have hρmem : ρ ∈ rhW := by rw [hρ, List.getD_eq_getElem _ _ hk]; exact List.getElem_mem _
  clear_value σ ρ w
  have hs1 := s1_ok
  simp only [s1Check, List.all_eq_true, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq,
    beq_iff_eq] at hs1
  obtain ⟨⟨⟨⟨⟨⟨hσ0, hσ1⟩, hσ2⟩, hσ3⟩, hσ4⟩, hσs⟩, hσrel⟩ := hs1 σ hσmem
  have hσl : ∀ j : Fin 5, ∀ y ∈ word (σ.getD j ""), y.1 ≠ 4 := by
    intro j y hy
    fin_cases j
    · have := lettersB_iff.mp hσ0 y hy; omega
    · have := lettersB_iff.mp hσ1 y hy; omega
    · have := lettersB_iff.mp hσ2 y hy; omega
    · exact hσ3 y hy
    · change y ∈ word (σ.getD 4 "") at hy
      rw [hσ4, word_empty] at hy
      simp at hy
  let f₁ : Fin 5 → ↥m22TwoStab := fun j => ⟨evalW gen (word (σ.getD j "")), evalW_mem_two (hσl j)⟩
  have hf₁ : ∀ w ∈ relsP1, evalW f₁ w = 1 := by
    intro w hw
    apply Subtype.ext
    have hm : ((evalW f₁ w : ↥m22TwoStab) : M22) =
        evalW (fun j => evalW gen (word (σ.getD j ""))) w :=
      (evalW_map m22TwoStab.subtype f₁ (fun j => evalW gen (word (σ.getD j ""))) w
        fun _ _ => rfl).symm
    rw [hm, Subgroup.coe_one]
    apply tab_injective
    rw [tab_one, ← evalT_wtab]
    exact hσrel w hw
  have hrh := rh_ok
  simp only [rhCheck, List.all_eq_true, List.mem_range, Bool.and_eq_true, Bool.not_eq_true',
    decide_eq_true_eq, beq_eq_false_iff_ne, ne_eq, beq_iff_eq] at hrh
  obtain ⟨⟨⟨⟨⟨⟨⟨hρ0, hρ1⟩, hρ2⟩, hρ3⟩, hρ4⟩, hρu⟩, hρrel⟩, hρinv⟩ := hrh ρ hρmem
  have hρl : ∀ j : Fin 5, ∀ y ∈ word (ρ.getD j ""), y.1 ≠ 3 := by
    intro j y hy
    fin_cases j
    · have := lettersB_iff.mp hρ0 y hy; omega
    · have := lettersB_iff.mp hρ1 y hy; omega
    · have := lettersB_iff.mp hρ2 y hy; omega
    · change y ∈ word (ρ.getD 3 "") at hy
      rw [hρ3, word_empty] at hy
      simp at hy
    · exact hρ4 y hy
  let f₂ : Fin 5 → ↥m22PtHexStab := fun j =>
    ⟨evalW gen (word (ρ.getD j "")), evalW_mem_ptHex (hρl j)⟩
  have hf₂ : ∀ w ∈ relsP2, evalW f₂ w = 1 := by
    intro w hw
    apply Subtype.ext
    have hm : ((evalW f₂ w : ↥m22PtHexStab) : M22) =
        evalW (fun j => evalW gen (word (ρ.getD j ""))) w :=
      (evalW_map m22PtHexStab.subtype f₂ (fun j => evalW gen (word (ρ.getD j ""))) w
        fun _ _ => rfl).symm
    rw [hm, Subgroup.coe_one]
    apply tab_injective
    rw [tab_one, ← evalT_wtab]
    exact hρrel w hw
  set α₁ := endo1 f₁ hf₁ with hα₁
  set α₂ := endo2 f₂ hf₂ with hα₂
  have hgen : ∀ j : Fin 5, j.val < 3 →
      θ (evalW gen (word (σ.getD j ""))) = evalW gen (word (ρ.getD j "")) := by
    intro j hj
    have hσj : ∀ y ∈ word (σ.getD j ""), y.1.val < 3 := by
      fin_cases j
      · exact lettersB_iff.mp hσ0
      · exact lettersB_iff.mp hσ1
      · exact lettersB_iff.mp hσ2
      · exact absurd hj (by decide)
      · exact absurd hj (by decide)
    have h := hcheck j.val hj
    rw [wtab_eq] at h
    set candM : Fin 5 → M22 := fun k => [θ (gen 0), θ (gen 1), θ (gen 2)].getD k 1 with hcandM
    have hcT : candT Tp Tq Tr = fun k => tab (candM k) := by
      funext k
      fin_cases k
      · exact hTp'
      · exact hTq'
      · exact hTr'.1
      · exact tab_one.symm
      · exact tab_one.symm
    have hθp' : (θ (gen 0))⁻¹ = θ (gen 0) :=
      inv_eq_of_mul_eq_one_right (mul_self_of_mem_barA2 hθp2)
    have hθq' : (θ (gen 1))⁻¹ = θ (gen 1) := by rw [← hx, crd_inv]
    have hcTi : candT Tp Tq TR = fun k => tab (candM k)⁻¹ := by
      funext k
      fin_cases k
      · show Tp = tab (θ (gen 0))⁻¹
        rw [hθp', hTp']
      · show Tq = tab (θ (gen 1))⁻¹
        rw [hθq', hTq']
      · exact hTr'.2
      · show tid = tab (1 : M22)⁻¹
        rw [inv_one, tab_one]
      · show tid = tab (1 : M22)⁻¹
        rw [inv_one, tab_one]
    rw [hcT, hcTi, ← tab_evalW] at h
    have h' := tab_injective h
    rw [evalW_congr (g := fun k => θ (gen k)) (fun y hy => by
      have := hσj y hy
      rcases y with ⟨k, b⟩
      fin_cases k
      · rfl
      · rfl
      · rfl
      · simp at this
      · simp at this), ← hθ.map_evalW hσj] at h'
    exact h'
  have main : ∀ g ∈ Subgroup.closure (gen '' {0, 1, 2}),
      ∀ (h₁ : g ∈ m22TwoStab) (h₂ : g ∈ m22PtHexStab),
        ((α₁ ⟨g, h₁⟩ : ↥m22TwoStab) : M22) ∈ m22PtHexStab ∧
        ((α₂ ⟨g, h₂⟩ : ↥m22PtHexStab) : M22) ∈ m22TwoStab ∧
        θ ((α₁ ⟨g, h₁⟩ : ↥m22TwoStab) : M22) = ((α₂ ⟨g, h₂⟩ : ↥m22PtHexStab) : M22) := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨j, hj, rfl⟩ := hy
      intro h₁ h₂
      have hj3 : j.val < 3 := by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hj
        rcases hj with rfl | rfl | rfl <;> decide
      have e₁ : (⟨gen j, h₁⟩ : ↥m22TwoStab) = gen₁ j :=
        Subtype.ext (coe_gen₁ (by intro h; rw [h] at hj3; exact absurd hj3 (by decide))).symm
      have e₂ : (⟨gen j, h₂⟩ : ↥m22PtHexStab) = gen₂ j :=
        Subtype.ext (coe_gen₂ (by intro h; rw [h] at hj3; exact absurd hj3 (by decide))).symm
      have hσj : ∀ y ∈ word (σ.getD j ""), y.1.val < 3 := by
        fin_cases j
        · exact lettersB_iff.mp hσ0
        · exact lettersB_iff.mp hσ1
        · exact lettersB_iff.mp hσ2
        · exact absurd hj3 (by decide)
        · exact absurd hj3 (by decide)
      have hρj : ∀ y ∈ word (ρ.getD j ""), y.1.val < 3 := by
        fin_cases j
        · exact lettersB_iff.mp hρ0
        · exact lettersB_iff.mp hρ1
        · exact lettersB_iff.mp hρ2
        · exact absurd hj3 (by decide)
        · exact absurd hj3 (by decide)
      rw [e₁, e₂, hα₁, hα₂, endo1_gen, endo2_gen]
      exact ⟨(evalW_mem_barB hσj).2, (evalW_mem_barB hρj).1, hgen j hj3⟩
    | one =>
      intro h₁ h₂
      have e₁ : (⟨1, h₁⟩ : ↥m22TwoStab) = 1 := rfl
      have e₂ : (⟨1, h₂⟩ : ↥m22PtHexStab) = 1 := rfl
      rw [e₁, e₂, map_one, map_one, Subgroup.coe_one, Subgroup.coe_one, hθ.map_one]
      exact ⟨m22PtHexStab.one_mem, m22TwoStab.one_mem, rfl⟩
    | mul y z hy hz ihy ihz =>
      intro h₁ h₂
      have hyB := closure_c_le_B hy
      have hzB := closure_c_le_B hz
      obtain ⟨a1, b1, c1⟩ := ihy hyB.1 hyB.2
      obtain ⟨a2, b2, c2⟩ := ihz hzB.1 hzB.2
      have e₁ : (⟨y * z, h₁⟩ : ↥m22TwoStab) = ⟨y, hyB.1⟩ * ⟨z, hzB.1⟩ := rfl
      have e₂ : (⟨y * z, h₂⟩ : ↥m22PtHexStab) = ⟨y, hyB.2⟩ * ⟨z, hzB.2⟩ := rfl
      rw [e₁, e₂, map_mul, map_mul, Subgroup.coe_mul, Subgroup.coe_mul]
      refine ⟨m22PtHexStab.mul_mem a1 a2, m22TwoStab.mul_mem b1 b2, ?_⟩
      rw [hθ.mul _ ⟨(α₁ _).2, a1⟩ _ ⟨(α₁ _).2, a2⟩, c1, c2]
    | inv y hy ihy =>
      intro h₁ h₂
      have hyB := closure_c_le_B hy
      obtain ⟨a1, b1, c1⟩ := ihy hyB.1 hyB.2
      have e₁ : (⟨y⁻¹, h₁⟩ : ↥m22TwoStab) = (⟨y, hyB.1⟩)⁻¹ := rfl
      have e₂ : (⟨y⁻¹, h₂⟩ : ↥m22PtHexStab) = (⟨y, hyB.2⟩)⁻¹ := rfl
      rw [e₁, e₂, map_inv, map_inv, Subgroup.coe_inv, Subgroup.coe_inv]
      refine ⟨m22PtHexStab.inv_mem a1, m22TwoStab.inv_mem b1, ?_⟩
      rw [hθ.map_inv ⟨(α₁ _).2, a1⟩, c1]
  have main' : ∀ (g : M22) (h₁ : g ∈ m22TwoStab) (h₂ : g ∈ m22PtHexStab),
      ((α₁ ⟨g, h₁⟩ : ↥m22TwoStab) : M22) ∈ m22PtHexStab ∧
        ((α₂ ⟨g, h₂⟩ : ↥m22PtHexStab) : M22) ∈ m22TwoStab ∧
        θ ((α₁ ⟨g, h₁⟩ : ↥m22TwoStab) : M22) = ((α₂ ⟨g, h₂⟩ : ↥m22PtHexStab) : M22) :=
    fun g h₁ h₂ => main g (mem_closure_of_mem_B h₁ h₂) h₁ h₂
  have hB2le : bB2.map α₂ ≤ bB2 := by
    rintro _ ⟨g, hg, rfl⟩
    exact (main' (g : M22) hg g.2).2.1
  have hB2ge : bB2 ≤ bB2.map α₂ := by
    refine bB2_le_closure.trans ?_
    rw [Subgroup.closure_le]
    rintro _ ⟨j, hj, rfl⟩
    have hj3 : j.val < 3 := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hj
      rcases hj with rfl | rfl | rfl <;> decide
    obtain ⟨hl, heq⟩ := hρinv j.val hj3
    have hv3 : ∀ y ∈ word (ρ.getD (j.val + 5) ""), y.1.val < 3 := lettersB_iff.mp hl
    have hv4 : ∀ y ∈ word (ρ.getD (j.val + 5) ""), y.1 ≠ 3 := fun y hy h => by
      have := hv3 y hy
      rw [h] at this
      exact absurd this (by decide)
    refine ⟨evalW gen₂ (word (ρ.getD (j.val + 5) "")), ?_, ?_⟩
    · show ((evalW gen₂ (word (ρ.getD (j.val + 5) "")) : ↥m22PtHexStab) : M22) ∈ m22TwoStab
      rw [coe_evalW_gen₂ hv4]
      exact (evalW_mem_barB hv3).1
    · have hm : evalW f₂ (word (ρ.getD (j.val + 5) "")) =
          α₂ (evalW gen₂ (word (ρ.getD (j.val + 5) ""))) :=
        evalW_map α₂ gen₂ f₂ _ fun y _ => by rw [hα₂, endo2_gen]
      rw [← hm]
      apply Subtype.ext
      have hm' : ((evalW f₂ (word (ρ.getD (j.val + 5) "")) : ↥m22PtHexStab) : M22) =
          evalW (fun k => evalW gen (word (ρ.getD k ""))) (word (ρ.getD (j.val + 5) "")) :=
        (evalW_map m22PtHexStab.subtype f₂ (fun k => evalW gen (word (ρ.getD k ""))) _
          fun _ _ => rfl).symm
      rw [hm', coe_gen₂ (fun h => by rw [h] at hj3; exact absurd hj3 (by decide))]
      apply tab_injective
      rw [← evalT_wtab, heq, genTL_getD' j.val (by omega)]
  have hB2 : bB2.map α₂ = bB2 := le_antisymm hB2le hB2ge
  have hu : α₂ (gen₂ 4) ∉ bB2 := by
    rw [hα₂, endo2_gen]
    intro h
    have h1 := (mem_m22TwoStab_iff.mp h).2
    apply hρu
    rw [wtab_eq, show (1 : ℕ) = (1 : Fin 22).val from rfl, tab_getD]
    exact h1
  have hbij₂ : Function.Bijective α₂ := bijective_of_map_B2 hB2 hu
  have hB1le : bB1.map α₁ ≤ bB1 := by
    rintro _ ⟨g, hg, rfl⟩
    exact (main' (g : M22) g.2 hg).1
  have hinj : ∀ g ∈ bB1, ∀ g' ∈ bB1, α₁ g = α₁ g' → g = g' := by
    intro g hg g' hg' e
    have h1 := (main' (g : M22) g.2 hg).2.2
    have h2 := (main' (g' : M22) g'.2 hg').2.2
    have e' : α₁ ⟨(g : M22), g.2⟩ = α₁ ⟨(g' : M22), g'.2⟩ := e
    rw [e'] at h1
    have h3 : α₂ ⟨(g : M22), hg⟩ = α₂ ⟨(g' : M22), hg'⟩ := Subtype.ext (h1.symm.trans h2)
    exact Subtype.ext (congrArg (Subtype.val : ↥m22PtHexStab → M22) (hbij₂.1 h3))
  have hB1 : bB1.map α₁ = bB1 := by
    refine Subgroup.eq_of_le_of_card_ge hB1le ?_
    refine Nat.card_le_card_of_injective (fun g : ↥bB1 =>
      (⟨α₁ g, Subgroup.mem_map_of_mem α₁ g.2⟩ : ↥(bB1.map α₁))) ?_
    intro g g' h
    exact Subtype.ext (hinj g g.2 g' g'.2 (congrArg Subtype.val h))
  have hs : α₁ (gen₁ 3) ∉ bB1 := by
    rw [hα₁, endo1_gen]
    intro h
    have h' := (mem_ptHex_iff_tab.mp h).2
    rw [wtab_eq] at hσs
    exact Bool.false_ne_true (hσs.symm.trans h')
  have hbij₁ : Function.Bijective α₁ := bijective_of_map_B1 hB1 hs
  refine ⟨MulEquiv.ofBijective α₁ hbij₁, MulEquiv.ofBijective α₂ hbij₂, fun g => ⟨fun h => ?_,
    fun h => (main' _ g.2 h).1⟩, fun g => ⟨fun h => ?_, fun h => (main' _ h g.2).2.1⟩,
    fun g h₁ h₂ => (main' g h₁ h₂).2.2⟩
  · have hm : α₁ g ∈ bB1.map α₁ := by rw [hB1]; exact h
    obtain ⟨g', hg', e⟩ := hm
    rw [← hbij₁.1 e]
    exact hg'
  · have hm : α₂ g ∈ bB2.map α₂ := by rw [hB2]; exact h
    obtain ⟨g', hg', e⟩ := hm
    rw [← hbij₂.1 e]
    exact hg'

theorem gen_two_ne_one : gen 2 ≠ 1 := by
  decide +kernel

theorem gen_two_cube : gen 2 ^ 3 = 1 := by
  have h := evalW_amalRels (word "rrr") (List.mem_map.mpr ⟨"rrr", by simp [rels1], rfl⟩)
  rw [show word "rrr" = [(2, true), (2, true), (2, true)] by decide] at h
  simpa [evalW, pow_succ, mul_assoc] using h

theorem exists_aut_factor
    {θ : M22 → M22} (hθ : IsAutB θ)
    (hA1 : ∀ g ∈ barB, θ g ∈ barA1 ↔ g ∈ barA1) (hA2 : ∀ g ∈ barB, θ g ∈ barA2 ↔ g ∈ barA2) :
    ∃ (α₁ : ↥m22TwoStab ≃* ↥m22TwoStab) (α₂ : ↥m22PtHexStab ≃* ↥m22PtHexStab),
      (∀ g : ↥m22TwoStab, ((α₁ g : ↥m22TwoStab) : M22) ∈ m22PtHexStab ↔
        (g : M22) ∈ m22PtHexStab) ∧
      (∀ g : ↥m22PtHexStab, ((α₂ g : ↥m22PtHexStab) : M22) ∈ m22TwoStab ↔
        (g : M22) ∈ m22TwoStab) ∧
      ∀ (g : M22) (h₁ : g ∈ m22TwoStab) (h₂ : g ∈ m22PtHexStab),
        θ ((α₁ ⟨g, h₁⟩ : ↥m22TwoStab) : M22) = ((α₂ ⟨g, h₂⟩ : ↥m22PtHexStab) : M22) := by
  have hr : gen 2 ∈ barB := gen_mem_barB (by decide)
  obtain ⟨c, hc, hcr⟩ := exists_conj_r (hθ.mem _ hr) (hθ.pow_three hr gen_two_cube)
    (hθ.ne_one hr gen_two_ne_one)
  have hθ' : IsAutB (fun g => c * θ g * c⁻¹) := hθ.conj hc
  have hA1' : ∀ g ∈ barB, c * θ g * c⁻¹ ∈ barA1 ↔ g ∈ barA1 := by
    intro g hg
    rw [← hA1 g hg]
    constructor
    · intro h
      have := conj_mem_barA1 (m22TwoStab.inv_mem hc.1) h
      rwa [show c⁻¹ * (c * θ g * c⁻¹) * c⁻¹⁻¹ = θ g by group] at this
    · intro h
      exact conj_mem_barA1 hc.1 h
  have hA2' : ∀ g ∈ barB, c * θ g * c⁻¹ ∈ barA2 ↔ g ∈ barA2 := by
    intro g hg
    rw [← hA2 g hg]
    constructor
    · intro h
      have := conj_mem_barA2 (m22PtHexStab.inv_mem hc.2) h
      rwa [show c⁻¹ * (c * θ g * c⁻¹) * c⁻¹⁻¹ = θ g by group] at this
    · intro h
      exact conj_mem_barA2 hc.2 h
  obtain ⟨α₁, α₂, h1, h2, h3⟩ := exists_aut_factor_of_r hθ' hA1' hA2' hcr
  set cc : ↥m22PtHexStab := ⟨c, hc.2⟩ with hcc
  have hcc' : (cc : M22) = c := rfl
  refine ⟨α₁, α₂.trans (MulAut.conj cc⁻¹), h1, fun g => ?_, fun g h₁ h₂ => ?_⟩
  · rw [MulEquiv.trans_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
      Subgroup.coe_inv, inv_inv, hcc', ← h2 g]
    constructor
    · intro h
      have := m22TwoStab.mul_mem (m22TwoStab.mul_mem hc.1 h) (m22TwoStab.inv_mem hc.1)
      rwa [show c * (c⁻¹ * ((α₂ g : ↥m22PtHexStab) : M22) * c) * c⁻¹ =
        ((α₂ g : ↥m22PtHexStab) : M22) by group] at this
    · intro h
      exact m22TwoStab.mul_mem (m22TwoStab.mul_mem (m22TwoStab.inv_mem hc.1) h) hc.1
  · have h := h3 g h₁ h₂
    rw [MulEquiv.trans_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
      Subgroup.coe_inv, inv_inv, hcc', ← h]
    group

end CFSG.Quasithin.L34Amalgam
