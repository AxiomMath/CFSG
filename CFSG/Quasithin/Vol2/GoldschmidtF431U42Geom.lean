module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42Tau
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42Card

public section

namespace CFSG.Quasithin.H13.F431.U42

open CFSG.Quasithin U42F431
open scoped Pointwise

abbrev Y : Type := ↥Xs

@[expose] def lineSet (l : List ℕ) : Set (Fin 45) := {p | p.val ∈ l}

@[expose] def lnS (k : ℕ) : Set (Fin 45) := lineSet (lnTab.getD k [])

@[expose] def L0S : Set (Fin 45) := lineSet L0

@[expose] def P1 : Subgroup Y := MulAction.stabilizer Y (0 : Fin 45)

@[expose] def P2 : Subgroup Y := MulAction.stabilizer Y L0S

@[expose] def B0 : Subgroup Y := P1 ⊓ P2

theorem mem_P1_iff (g : Y) : g ∈ P1 ↔ (g : P45) 0 = 0 := MulAction.mem_stabilizer_iff

theorem smul_set_eq (g : Y) (S : Set (Fin 45)) : g • S = (g : P45) '' S :=
  (Set.image_smul (a := g) (t := S)).symm

theorem mem_P2_iff (g : Y) : g ∈ P2 ↔ (g : P45) '' L0S = L0S := by
  rw [P2, MulAction.mem_stabilizer_iff, smul_set_eq]

theorem lineSet_eq_of_sameSet {a b : List ℕ} (h : sameSet a b = true) : lineSet a = lineSet b := by
  simp only [sameSet, Bool.and_eq_true] at h
  ext q
  simp only [lineSet, Set.mem_ofPred_eq]
  constructor
  · intro hq
    exact List.contains_iff_mem.1
      (List.all_eq_true.1 h.1 q.val (List.mem_filter.2 ⟨hq, by simp⟩))
  · intro hq
    exact List.contains_iff_mem.1
      (List.all_eq_true.1 h.2 q.val (List.mem_filter.2 ⟨hq, by simp⟩))

theorem sameSet_of_lineSet_eq {a b : List ℕ} (h : lineSet a = lineSet b) : sameSet a b = true := by
  unfold sameSet
  rw [Bool.and_eq_true]
  constructor
  · refine List.all_eq_true.2 fun p hp => ?_
    rw [List.mem_filter] at hp
    have hp45 : p < 45 := by simpa using hp.2
    have := Set.ext_iff.1 h ⟨p, hp45⟩
    simp only [lineSet, Set.mem_ofPred_eq] at this
    exact List.contains_iff_mem.2 (this.1 hp.1)
  · refine List.all_eq_true.2 fun p hp => ?_
    rw [List.mem_filter] at hp
    have hp45 : p < 45 := by simpa using hp.2
    have := Set.ext_iff.1 h ⟨p, hp45⟩
    simp only [lineSet, Set.mem_ofPred_eq] at this
    exact List.contains_iff_mem.2 (this.2 hp.1)

theorem image_lineSet {g : P45} {gL : PL} (hg : RepL gL g) {l : List ℕ} (hl : ∀ p ∈ l, p < 45) :
    g '' lineSet l = lineSet (imgSet gL l) := by
  ext q
  simp only [Set.mem_image, lineSet, Set.mem_ofPred_eq, imgSet, List.mem_map]
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p.val, hp, hg.2 p⟩
  · rintro ⟨p, hp, hpq⟩
    refine ⟨⟨p, hl p hp⟩, hp, ?_⟩
    apply Fin.ext
    rw [← hpq]
    exact (hg.2 ⟨p, hl p hp⟩).symm

theorem chkLines_spec : chkLines = true :=
  Certificates.certificate4161.2.1

theorem lines_spec :
    lnTab.length = 27 ∧ lnTab.getD 0 [] = L0 ∧
    (∀ l ∈ lnTab, l.length = 5 ∧ ∀ p ∈ l, p < 45) ∧
    (∀ l ∈ lnTab, ∀ k < 2, ∃ l' ∈ lnTab, sameSet (imgSet (genL k) l) l' = true) ∧
    (∀ k < 27, sameSet (imgSet (evalW (wlW.getD k [])) L0) (lnTab.getD k []) = true) ∧
    (∀ i < 27, ∀ j < 27, i = j ∨ sameSet (lnTab.getD i []) (lnTab.getD j []) = false) := by
  have h := chkLines_spec
  simp only [chkLines, Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq,
    List.any_eq_true, decide_eq_true_eq, and_assoc, Bool.or_eq_true, Bool.not_eq_true'] at h
  exact h

theorem lnTab_lt {k : ℕ} (hk : k < 27) :
    ∀ p ∈ lnTab.getD k [], p < 45 := by
  have hlen := lines_spec.1
  have hmem : lnTab.getD k [] ∈ lnTab := by
    rw [List.getD_eq_getElem _ _ (by omega)]
    exact List.getElem_mem _
  exact (lines_spec.2.2.1 _ hmem).2

theorem L0_lt : ∀ p ∈ L0, p < 45 := by
  have := lnTab_lt (k := 0) (by norm_num)
  rwa [lines_spec.2.1] at this

theorem chkP_spec : chkP = true :=
  Certificates.certificate4161.2.2.1

theorem gen_line_stable {j : ℕ} (hj : j < 2) {k : ℕ} (hk : k < 27) :
    ∃ k' < 27, gP j '' lnS k = lnS k' := by
  have hmem : lnTab.getD k [] ∈ lnTab := by
    rw [List.getD_eq_getElem _ _ (by have := lines_spec.1; omega)]
    exact List.getElem_mem _
  obtain ⟨l', hl', hs⟩ := lines_spec.2.2.2.1 _ hmem j hj
  obtain ⟨k', hk', hkl⟩ := List.mem_iff_getElem.1 hl'
  have hk27 : k' < 27 := by have := lines_spec.1; omega
  refine ⟨k', hk27, ?_⟩
  rw [lnS, image_lineSet (repL_gP j) (lnTab_lt hk), lineSet_eq_of_sameSet hs, lnS,
    List.getD_eq_getElem _ _ hk', hkl]

theorem line_stable {g : P45} (hg : g ∈ Xs) {k : ℕ} (hk : k < 27) :
    ∃ k' < 27, g '' lnS k = lnS k' := by
  have key : ((Xs : Subgroup P45) : Set P45) ⊆
      {g : P45 | ∀ k < 27, ∃ k' < 27, g '' lnS k = lnS k'} := by
    refine closure_subset_of_right_closed (S := ({x45, y45} : Set P45)) ?_ ?_ ?_
    · intro s _
      obtain ⟨n, hn, h⟩ := (isOfFinOrder_of_finite s).exists_pow_eq_one
      exact ⟨n, hn, h⟩
    · intro k hk
      exact ⟨k, hk, by simp⟩
    · intro p hp s hs k hk
      have hs' : ∃ j < 2, s = gP j := by
        rcases hs with rfl | rfl
        · exact ⟨0, by norm_num, by simp [gP]⟩
        · exact ⟨1, by norm_num, by simp [gP]⟩
      obtain ⟨j, hj, rfl⟩ := hs'
      obtain ⟨k'', hk'', h''⟩ := gen_line_stable hj hk
      obtain ⟨k', hk', hp'⟩ := hp k'' hk''
      refine ⟨k', hk', ?_⟩
      rw [Equiv.Perm.coe_mul, Set.image_comp, h'', hp']
  exact key hg k hk

theorem orbit_zero : MulAction.orbit Y (0 : Fin 45) = Set.univ := by
  ext j
  simp only [MulAction.mem_orbit_iff, Set.mem_univ, iff_true]
  exact ⟨⟨wordP (wpW.getD j []), wordP_mem _⟩, point_move j⟩

theorem card_P1 :
    Nat.card P1 = 576 := by
  have h1 := orbit_zero
  have h2 := MulAction.index_stabilizer Y (0 : Fin 45)
  rw [h1] at h2
  have h3 : (Set.univ : Set (Fin 45)).ncard = 45 := by
    simp [Set.ncard_univ]
  have h4 := Subgroup.index_mul_card (H := MulAction.stabilizer Y (0 : Fin 45))
  rw [h2, h3, card_Xs] at h4
  show Nat.card (MulAction.stabilizer Y (0 : Fin 45)) = 576
  omega

end CFSG.Quasithin.H13.F431.U42
