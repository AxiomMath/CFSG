module

public import CFSG.RankThree.PartTwo.Sec19.SeitzTrialityQ2Pairs

public section

open CFSG.RankThree.PartTwo.Sec4.Item434D42 CFSG.AGLEmbedding.ChevOuter HuppertD4Q2

namespace CFSG.RankThree.PartTwo.Sec19.TrialityTwo

section Generation

@[expose] def fixSet (α : MulAut lineGroup) : Set lineGroup := {t | α t = t}

theorem classCheck_spec {i : ℕ} (h : classCheck i = true) :
    wordP (classR1.getD i []) ≠ oneP ∧ wordP (classR2.getD i []) ≠ oneP ∧
    (∀ w ∈ classG1.getD i [] ++ classG2.getD i [], (wordP w).2 = 0) ∧
    (∀ w ∈ classG1.getD i [], mulP (wordP (classR1.getD i [])) (wordP w) =
      mulP (wordP w) (wordP (classR1.getD i []))) ∧
    (∀ w ∈ classG2.getD i [], mulP (wordP (classR2.getD i [])) (wordP w) =
      mulP (wordP w) (wordP (classR2.getD i []))) ∧
    (∀ w ∈ classG1.getD i [] ++ classG2.getD i [], mulP (wordP w) (wordP (invW w)) = oneP) ∧
    (∀ x ∈ classSlp.getD i [], x.1 < 18 ∧
      slpP ((classG1.getD i [] ++ classG2.getD i []).map wordP)
        ((classG1.getD i [] ++ classG2.getD i []).map fun w => wordP (invW w)) x.2 =
          (CFSG.AGLEmbedding.D4Two.letterArr x.1, 0)) ∧
    (∀ k < 18, ∃ x ∈ classSlp.getD i [], x.1 = k) := by
  simp only [classCheck, Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq, List.all_eq_true,
    beq_iff_eq, List.mem_append, List.mem_map] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  refine ⟨h1, h2, fun w hw => h3 w (List.mem_append.mp hw), fun w hw => h4 _ ⟨w, hw, rfl⟩,
    fun w hw => h5 _ ⟨w, hw, rfl⟩, fun w hw => h6 w (List.mem_append.mp hw), h7, ?_⟩
  intro k hk
  have := h8 k (List.mem_range.mpr hk)
  simp only [List.any_eq_true, beq_iff_eq] at this
  exact this

theorem aut_mul_conj_mul_inv (α : MulAut lineGroup) (t : lineGroup) :
    α * MulAut.conj t * α⁻¹ = MulAut.conj (α t) := by
  refine MulEquiv.ext fun x => ?_
  simp [MulAut.conj_apply, MulAut.mul_apply, map_mul, map_inv]

theorem lineGroup_induction {P : lineGroup → Prop} (hl : ∀ k < 18, P (letterX k)) (h1 : P 1)
    (hm : ∀ a b, P a → P b → P (a * b)) (hi : ∀ a, P a → P a⁻¹) : ∀ g, P g := by
  rintro ⟨g, hg⟩
  induction hg using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨k, hk, rfl⟩ := hy
    have hk' : k < 18 := hk
    have : (⟨CFSG.AGLEmbedding.D4Two.letterGL k, Subgroup.subset_closure ⟨k, hk, rfl⟩⟩ :
        lineGroup) = letterX k := by
      simp [letterX, hk']
    rw [this]
    exact hl k hk'
  | one => exact h1
  | mul y z hy hz ihy ihz => exact hm ⟨y, hy⟩ ⟨z, hz⟩ ihy ihz
  | inv y hy ihy => exact hi ⟨y, hy⟩ ihy

theorem slp_rep {F : Subgroup lineGroup} (entry : ℕ → Pr)
    (hentry : ∀ j, ∃ s ∈ F, Rep (entry j) (MulAut.conj s)) :
    ∀ (ids : List ℕ) (acc : Pr) (g : lineGroup), g ∈ F → Rep acc (MulAut.conj g) →
      ∃ g' ∈ F, Rep (ids.foldl (fun acc i => mulP acc (entry i)) acc) (MulAut.conj g') := by
  intro ids
  induction ids with
  | nil => intro acc g hg hacc; exact ⟨g, hg, hacc⟩
  | cons i ids ih =>
    intro acc g hg hacc
    obtain ⟨s, hs, hsi⟩ := hentry i
    have hrep := rep_mul hacc hsi
    rw [← map_mul] at hrep
    rw [List.foldl_cons]
    exact ih (mulP acc (entry i)) (g * s) (mul_mem hg hs) hrep

theorem repLine_ne_one (hZ : Subgroup.center lineGroup = ⊥) {i : ℕ} (h : classCheck i = true) :
    repLine1 i ≠ 1 ∧ repLine2 i ≠ 1 := by
  obtain ⟨h1, h2, -⟩ := classCheck_spec h
  exact ⟨fun hc => h1 ((rep_eq_oneP_iff hZ (rep_wordP _)).mpr hc),
    fun hc => h2 ((rep_eq_oneP_iff hZ (rep_wordP _)).mpr hc)⟩

theorem fixed_of_comm_wordP (hZ : Subgroup.center lineGroup = ⊥) {α : MulAut lineGroup}
    {pα : Pr} (hα : Rep pα α) {w : List ℕ} (hw : (wordP w).2 = 0)
    (h : mulP pα (wordP w) = mulP (wordP w) pα) :
    ∃ t : lineGroup, wordAut w = MulAut.conj t ∧ α t = t := by
  obtain ⟨-, -, t, -, hwt⟩ := rep_wordP w
  rw [hw, pow_zero, mul_one] at hwt
  refine ⟨t, hwt, ?_⟩
  have hcomm : α * wordAut w = wordAut w * α :=
    rep_ext (rep_mul hα (rep_wordP w)) (rep_mul (rep_wordP w) hα) h
  rw [hwt] at hcomm
  have h2 : MulAut.conj (α t) = MulAut.conj t := by
    rw [← aut_mul_conj_mul_inv, hcomm, mul_inv_cancel_right]
  exact (conj_injective_of_center hZ h2 : α t = t)

theorem classGen_of_check (hZ : Subgroup.center lineGroup = ⊥) {i : ℕ} (h : classCheck i = true) :
    Subgroup.closure (fixSet (repLine1 i) ∪ fixSet (repLine2 i)) = ⊤ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := classCheck_spec h
  set F : Subgroup lineGroup := Subgroup.closure (fixSet (repLine1 i) ∪ fixSet (repLine2 i))
    with hF
  set W : List (List ℕ) := classG1.getD i [] ++ classG2.getD i [] with hW
  have hW' : ∀ w ∈ W, ∃ t ∈ F, wordAut w = MulAut.conj t := by
    intro w hw
    rcases List.mem_append.mp hw with hw1 | hw2
    · obtain ⟨t, hwt, ht⟩ := fixed_of_comm_wordP hZ (rep_wordP (classR1.getD i [])) (h3 w hw)
        (h4 w hw1)
      exact ⟨t, Subgroup.subset_closure (Or.inl ht), hwt⟩
    · obtain ⟨t, hwt, ht⟩ := fixed_of_comm_wordP hZ (rep_wordP (classR2.getD i [])) (h3 w hw)
        (h5 w hw2)
      exact ⟨t, Subgroup.subset_closure (Or.inr ht), hwt⟩
  let entry : ℕ → Pr := fun j =>
    if j % 2 = 0 then (W.map wordP).getD (j / 2) oneP
    else (W.map fun w => wordP (invW w)).getD (j / 2) oneP
  have hentry : ∀ j, ∃ s ∈ F, Rep (entry j) (MulAut.conj s) := by
    intro j
    by_cases hj : j / 2 < W.length
    · have hwW : W[j / 2] ∈ W := List.getElem_mem hj
      obtain ⟨t, htF, hwt⟩ := hW' _ hwW
      have e1 : (W.map wordP).getD (j / 2) oneP = wordP W[j / 2] := by
        simp [List.getD_eq_getElem?_getD, hj]
      have e2 : (W.map fun w => wordP (invW w)).getD (j / 2) oneP = wordP (invW W[j / 2]) := by
        simp [List.getD_eq_getElem?_getD, hj]
      by_cases hev : j % 2 = 0
      · refine ⟨t, htF, ?_⟩
        simp only [entry, hev, ite_true, e1]
        rw [← hwt]
        exact rep_wordP _
      · refine ⟨t⁻¹, inv_mem htF, ?_⟩
        simp only [entry, hev, ite_false, e2]
        have hinv := rep_inv_eq (rep_wordP W[j / 2]) (rep_wordP (invW W[j / 2])) (h6 _ hwW)
        rw [map_inv, ← hwt, ← hinv]
        exact rep_wordP _
    · refine ⟨1, one_mem _, ?_⟩
      have e1 : (W.map wordP).getD (j / 2) oneP = oneP :=
        List.getD_eq_default _ _ (by simp; omega)
      have e2 : (W.map fun w => wordP (invW w)).getD (j / 2) oneP = oneP :=
        List.getD_eq_default _ _ (by simp; omega)
      have hone : Rep oneP (MulAut.conj (1 : lineGroup)) := by
        rw [map_one]
        exact rep_oneP
      by_cases hev : j % 2 = 0
      · simpa only [entry, hev, ite_true, e1] using hone
      · simpa only [entry, hev, ite_false, e2] using hone
  have hslp : ∀ x ∈ classSlp.getD i [], ∃ g ∈ F,
      Rep (CFSG.AGLEmbedding.D4Two.letterArr x.1, 0) (MulAut.conj g) := by
    intro x hx
    obtain ⟨-, hxeq⟩ := h7 x hx
    obtain ⟨g, hgF, hg⟩ := slp_rep entry hentry x.2 oneP 1 (one_mem _)
      (by rw [map_one]; exact rep_oneP)
    refine ⟨g, hgF, ?_⟩
    rw [← hxeq]
    exact hg
  have hletter : ∀ k < 18, letterX k ∈ F := by
    intro k hk
    obtain ⟨x, hx, hxk⟩ := h8 k hk
    obtain ⟨g, hgF, hg⟩ := hslp x hx
    rw [hxk] at hg
    have hrep : Rep (CFSG.AGLEmbedding.D4Two.letterArr k, 0) (MulAut.conj (letterX k)) := by
      have := rep_sym k
      simpa [symP, hk] using this
    have hconj : MulAut.conj g = MulAut.conj (letterX k) := rep_ext hg hrep rfl
    have hg' : g = letterX k := conj_injective_of_center hZ hconj
    rw [← hg']
    exact hgF
  rw [eq_top_iff]
  intro g _
  exact lineGroup_induction (P := fun g => g ∈ F) hletter (one_mem _)
    (fun a b ha hb => mul_mem ha hb) (fun a ha => inv_mem ha) g

end Generation

end CFSG.RankThree.PartTwo.Sec19.TrialityTwo
