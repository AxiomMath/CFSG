module

public import CFSG.LocalAnalysis.StandardType.GGFrameModelNumD
public import CFSG.LocalAnalysis.StandardType.GGFrameModelSignedTable

public section

namespace CFSG.StandardType.FrameRoute

open CFSG SpCoord Multiplicative

variable {k : ℕ}

private abbrev frameSN_P (α : Type*) [LT α] : Type _ := {x : α × α // x.1 < x.2}

private noncomputable def frameSN_L :
    frameSN_P (Fin k) ⊕ frameSN_P (Fin k) → MulAut (Fin k → Multiplicative (ZMod 3))
  | .inl x => permAut (Equiv.swap x.1.1 x.1.2)
  | .inr x => negSwapAut x.1.1 x.1.2

private noncomputable def frameSN_B :
    Fin k ⊕ (frameSN_P (Fin k) ⊕ frameSN_P (Fin k)) →
      MulAut (Fin k → Multiplicative (ZMod 3))
  | .inl i => sgnAut i
  | .inr y => frameSN_L y

private def frameSN_contains {α : Type*} (i : α) (x : α × α) : Prop := x.1 = i ∨ x.2 = i

private def frameSN_meetOne {α : Type*} (a b : α) (x : α × α) : Prop :=
  (frameSN_contains a x ∧ ¬ frameSN_contains b x) ∨
    (¬ frameSN_contains a x ∧ frameSN_contains b x)

private noncomputable def frameSN_sortPair {α : Type*} [LinearOrder α] (a b : α) (h : a ≠ b) :
    frameSN_P α :=
  if hab : a < b then ⟨(a, b), hab⟩
  else ⟨(b, a), lt_of_le_of_ne (le_of_not_gt hab) (Ne.symm h)⟩

private lemma frameSN_sortPair_pair {α : Type*} [LinearOrder α] {a b : α} (h : a ≠ b) :
    (frameSN_sortPair a b h).1.1 = a ∧ (frameSN_sortPair a b h).1.2 = b ∨
      (frameSN_sortPair a b h).1.1 = b ∧ (frameSN_sortPair a b h).1.2 = a := by
  classical
  unfold frameSN_sortPair
  split_ifs with hab
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr ⟨rfl, rfl⟩

private lemma frameSN_sortPair_contains_left {α : Type*} [LinearOrder α] {a b : α} (h : a ≠ b) :
    frameSN_contains a (frameSN_sortPair a b h).1 := by
  classical
  unfold frameSN_sortPair
  split_ifs with hab <;> simp [frameSN_contains]

private lemma frameSN_sortPair_contains_right {α : Type*} [LinearOrder α] {a b : α} (h : a ≠ b) :
    frameSN_contains b (frameSN_sortPair a b h).1 := by
  classical
  unfold frameSN_sortPair
  split_ifs with hab <;> simp [frameSN_contains]

private lemma frameSN_eq_sortPair_of_contains {α : Type*} [LinearOrder α] {a b : α} (hab : a ≠ b)
    {x : frameSN_P α} (ha : frameSN_contains a x.1) (hb : frameSN_contains b x.1) :
    x = frameSN_sortPair a b hab := by
  classical
  rcases x with ⟨⟨c, d⟩, hcd⟩
  simp only [frameSN_contains] at ha hb
  rcases ha with rfl | rfl
  · rcases hb with h | rfl
    · exact absurd h hab
    · simp [frameSN_sortPair, hcd]
  · rcases hb with rfl | h
    · simp [frameSN_sortPair, not_lt.mpr (le_of_lt hcd)]
    · exact absurd h hab

private lemma frameSN_card_P (α : Type*) [LinearOrder α] [Fintype α] :
    Nat.card (frameSN_P α) = (Fintype.card α).choose 2 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have h := Finset.card_product_filter_lt (s := (Finset.univ : Finset α))
  simpa [Finset.card_univ] using h

private lemma frameSN_card_ne (i : Fin k) :
    Nat.card {j : Fin k // j ≠ i} = k - 1 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have h : (Finset.univ.filter (fun j : Fin k => j ≠ i)) = Finset.univ.erase i := by
    ext j; simp [Finset.mem_erase]
  rw [h, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]

private lemma frameSN_fintypeCard_ne (i : Fin k) :
    Fintype.card {j : Fin k // j ≠ i} = k - 1 := by
  rw [← Nat.card_eq_fintype_card]
  exact frameSN_card_ne i

private lemma frameSN_natCard_subtype {α : Type*} (p : α → Prop) :
    Nat.card {x : α // p x} = {x : α | p x}.ncard := rfl

private def frameSN_complEquiv (i : Fin k) :
    {x : frameSN_P (Fin k) // x.1.1 ≠ i ∧ x.1.2 ≠ i} ≃
      frameSN_P {j : Fin k // j ≠ i} where
  toFun x := ⟨(⟨x.1.1.1, x.2.1⟩, ⟨x.1.1.2, x.2.2⟩), x.1.2⟩
  invFun y := ⟨⟨(y.1.1.1, y.1.2.1), y.2⟩, ⟨y.1.1.2, y.1.2.2⟩⟩
  left_inv x := by rfl
  right_inv y := by rfl

private lemma frameSN_ncard_contains (i : Fin k) :
    Nat.card {x : frameSN_P (Fin k) // frameSN_contains i x.1} = k - 1 := by
  classical
  set C : Set (frameSN_P (Fin k)) := {x | frameSN_contains i x.1} with hCdef
  have hcompl : Cᶜ.ncard = (k - 1).choose 2 := by
    change ({x : frameSN_P (Fin k) | ¬ frameSN_contains i x.1} : Set _).ncard = _
    rw [← frameSN_natCard_subtype (fun x : frameSN_P (Fin k) => ¬ frameSN_contains i x.1)]
    refine (Nat.card_congr (Equiv.subtypeEquivRight (p := fun x : frameSN_P (Fin k) =>
      ¬ frameSN_contains i x.1) (q := fun x : frameSN_P (Fin k) =>
      x.1.1 ≠ i ∧ x.1.2 ≠ i) ?_)).trans ?_
    · intro x; simp [frameSN_contains, not_or]
    · rw [Nat.card_congr (frameSN_complEquiv i), frameSN_card_P, frameSN_fintypeCard_ne]
  have hsum := Set.ncard_add_ncard_compl C
  rw [hcompl, frameSN_card_P, Fintype.card_fin] at hsum
  have hC : C.ncard = Nat.card {x : frameSN_P (Fin k) // frameSN_contains i x.1} :=
    (frameSN_natCard_subtype (fun x : frameSN_P (Fin k) => frameSN_contains i x.1)).symm
  rw [hC] at hsum
  have hk : 0 < k := Fin.pos i
  have hchoose : k.choose 2 = (k - 1).choose 2 + (k - 1) := by
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hk)
    have h := Nat.choose_succ_succ' n 1
    rw [Nat.choose_one_right] at h
    simpa [Nat.add_comm] using h
  omega

private lemma frameSN_ncard_meetOne {a b : Fin k} (hab : a ≠ b) :
    Nat.card {x : frameSN_P (Fin k) // frameSN_meetOne a b x.1} = 2 * (k - 2) := by
  classical
  set A : Set (frameSN_P (Fin k)) := {x | frameSN_contains a x.1} with hAdef
  set B : Set (frameSN_P (Fin k)) := {x | frameSN_contains b x.1} with hBdef
  have hA : A.ncard = k - 1 :=
    (frameSN_natCard_subtype (fun x : frameSN_P (Fin k) => frameSN_contains a x.1)).symm.trans
      (frameSN_ncard_contains a)
  have hB : B.ncard = k - 1 :=
    (frameSN_natCard_subtype (fun x : frameSN_P (Fin k) => frameSN_contains b x.1)).symm.trans
      (frameSN_ncard_contains b)
  have hAB : (A ∩ B).ncard = 1 := by
    have hEq : A ∩ B = {frameSN_sortPair a b hab} := by
      ext x
      constructor
      · rintro ⟨ha, hb⟩
        exact Set.mem_singleton_iff.mpr (frameSN_eq_sortPair_of_contains hab ha hb)
      · intro hx
        rw [Set.mem_singleton_iff] at hx
        subst hx
        exact ⟨frameSN_sortPair_contains_left hab, frameSN_sortPair_contains_right hab⟩
    rw [hEq, Set.ncard_singleton]
  have hU : (A ∪ B).ncard = 2 * k - 3 := by
    have h := Set.ncard_union_add_ncard_inter A B
    rw [hA, hB, hAB] at h
    have hk2 : 2 ≤ k := by
      have h1 := a.isLt
      have h2 := b.isLt
      have hne : a.val ≠ b.val := fun h => hab (Fin.ext h)
      omega
    omega
  have hmeet : {x : frameSN_P (Fin k) | frameSN_meetOne a b x.1} = (A ∪ B) \ (A ∩ B) := by
    ext x
    simp [frameSN_meetOne, A, B]
    tauto
  change ({x : frameSN_P (Fin k) | frameSN_meetOne a b x.1} : Set _).ncard = 2 * (k - 2)
  rw [hmeet]
  rw [Set.ncard_sdiff (Set.inter_subset_left.trans Set.subset_union_left)]
  rw [hU, hAB]
  have hk2 : 2 ≤ k := by
    have h1 := a.isLt
    have h2 := b.isLt
    have hne : a.val ≠ b.val := fun h => hab (Fin.ext h)
    omega
  omega

private lemma frameSN_meetOne_iff_not_table {α : Type*} {a b c d : α} (hab : a ≠ b) (hcd : c ≠ d) :
    frameSN_meetOne a b (c, d) ↔
      ¬ ((a = c ∧ b = d) ∨ (a = d ∧ b = c) ∨
        (a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d)) := by
  simp [frameSN_meetOne, frameSN_contains]
  grind

private lemma frameSN_negSwapAut_comm {a b : Fin k} (hab : a ≠ b) :
    negSwapAut a b = negSwapAut b a := by
  rw [negSwapAut_eq_negSwapAut_iff hab hab.symm]
  exact Or.inr ⟨rfl, rfl⟩

private lemma frameSN_mem_range_L_iff
    (u : MulAut (Fin k → Multiplicative (ZMod 3))) :
    u ∈ Set.range (frameSN_L (k := k)) ↔
      ∃ a b : Fin k, a ≠ b ∧ (u = permAut (Equiv.swap a b) ∨ u = negSwapAut a b) := by
  constructor
  · rintro ⟨x, rfl⟩
    cases x with
    | inl x => exact ⟨x.1.1, x.1.2, x.2.ne, Or.inl rfl⟩
    | inr x => exact ⟨x.1.1, x.1.2, x.2.ne, Or.inr rfl⟩
  · rintro ⟨a, b, hab, h | h⟩
    · subst h
      refine ⟨.inl (frameSN_sortPair a b hab), ?_⟩
      rcases frameSN_sortPair_pair hab with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · simp [frameSN_L, h1, h2]
      · simp [frameSN_L, h1, h2, Equiv.swap_comm]
    · subst h
      refine ⟨.inr (frameSN_sortPair a b hab), ?_⟩
      rcases frameSN_sortPair_pair hab with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · simp [frameSN_L, h1, h2]
      · simp [frameSN_L, h1, h2, (frameSN_negSwapAut_comm hab).symm]

private lemma frameSN_mem_range_B_iff
    (u : MulAut (Fin k → Multiplicative (ZMod 3))) :
    u ∈ Set.range (frameSN_B (k := k)) ↔
      (∃ i, u = sgnAut i) ∨
        ∃ a b : Fin k, a ≠ b ∧ (u = permAut (Equiv.swap a b) ∨ u = negSwapAut a b) := by
  constructor
  · rintro ⟨x, rfl⟩
    cases x with
    | inl i => exact Or.inl ⟨i, rfl⟩
    | inr y => exact Or.inr ((frameSN_mem_range_L_iff _).mp ⟨y, rfl⟩)
  · rintro (⟨i, rfl⟩ | hL)
    · exact ⟨.inl i, rfl⟩
    · obtain ⟨y, rfl⟩ := (frameSN_mem_range_L_iff _).mpr hL
      exact ⟨.inr y, rfl⟩

private lemma frameSN_range_L :
    Set.range (frameSN_L (k := k)) = modelReflSet (evenSignedPermSet k) := by
  ext u
  rw [frameSN_mem_range_L_iff, mem_modelReflSet_evenSignedPermSet_iff]

private lemma frameSN_range_B :
    Set.range (frameSN_B (k := k)) = modelReflSet (signedPermSet k) := by
  ext u
  rw [frameSN_mem_range_B_iff, mem_modelReflSet_signedPermSet_iff]

private lemma frameSN_L_injective : Function.Injective (frameSN_L (k := k)) := by
  intro x y h
  cases x with
  | inl x =>
    cases y with
    | inl y =>
      have hxy := (permAut_swap_eq_permAut_swap_iff x.2.ne y.2.ne).mp h
      rcases hxy with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [Subtype.ext (Prod.ext h1 h2)]
      · exfalso
        have hlt : y.1.2 < y.1.1 := by
          calc y.1.2 = x.1.1 := h1.symm
            _ < x.1.2 := x.2
            _ = y.1.1 := h2
        exact lt_asymm y.2 hlt
    | inr y => exact absurd h (permAut_swap_ne_negSwapAut x.2.ne y.2.ne)
  | inr x =>
    cases y with
    | inl y => exact absurd h.symm (permAut_swap_ne_negSwapAut y.2.ne x.2.ne)
    | inr y =>
      have hxy := (negSwapAut_eq_negSwapAut_iff x.2.ne y.2.ne).mp h
      rcases hxy with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [Subtype.ext (Prod.ext h1 h2)]
      · exfalso
        have hlt : y.1.2 < y.1.1 := by
          calc y.1.2 = x.1.1 := h1.symm
            _ < x.1.2 := x.2
            _ = y.1.1 := h2
        exact lt_asymm y.2 hlt

private lemma frameSN_B_injective : Function.Injective (frameSN_B (k := k)) := by
  intro x y h
  cases x with
  | inl i =>
    cases y with
    | inl j =>
      have hij : i = j := sgnAut_injective h
      rw [hij]
    | inr y =>
      cases y with
      | inl x => exact absurd h (sgnAut_ne_permAut_swap i x.2.ne)
      | inr x => exact absurd h (sgnAut_ne_negSwapAut i x.2.ne)
  | inr x =>
    cases y with
    | inl j =>
      cases x with
      | inl x => exact absurd h.symm (sgnAut_ne_permAut_swap j x.2.ne)
      | inr x => exact absurd h.symm (sgnAut_ne_negSwapAut j x.2.ne)
    | inr y =>
      have hxy := frameSN_L_injective h
      rw [hxy]

private lemma frameSN_ncard_noncomm_range {α X : Type} [Group X] [Finite α]
    (f : α → MulAut X) (hf : Function.Injective f) (u : MulAut X) :
    {v | v ∈ Set.range f ∧ u * v ≠ v * u}.ncard =
      Nat.card {x : α // u * f x ≠ f x * u} := by
  classical
  have himage : {v | v ∈ Set.range f ∧ u * v ≠ v * u} =
      f '' {x | u * f x ≠ f x * u} := by
    ext v
    constructor
    · rintro ⟨⟨x, rfl⟩, hx⟩
      exact ⟨x, hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, rfl⟩, hx⟩
  rw [himage, Set.ncard_image_of_injective _ hf]
  exact frameSN_natCard_subtype _

private lemma frameSN_card_subtype_sum {α β : Type} [Finite α] [Finite β]
    (p : α ⊕ β → Prop) :
    Nat.card {c : α ⊕ β // p c} =
      Nat.card {a : α // p (.inl a)} + Nat.card {b : β // p (.inr b)} := by
  rw [Nat.card_congr Equiv.subtypeSum, Nat.card_sum]

private lemma frameSN_noncomm_sgn_perm (i a b : Fin k) (hab : a ≠ b) :
    sgnAut (p := 3) i * permAut (p := 3) (Equiv.swap a b) ≠
        permAut (p := 3) (Equiv.swap a b) * sgnAut (p := 3) i ↔
      i = a ∨ i = b := by
  rw [show sgnAut (p := 3) i * permAut (p := 3) (Equiv.swap a b) ≠
      permAut (p := 3) (Equiv.swap a b) * sgnAut (p := 3) i ↔
      ¬ Commute (sgnAut (p := 3) i) (permAut (p := 3) (Equiv.swap a b)) from Iff.rfl]
  rw [sgnAut_commute_permAut_swap_iff i hab]
  tauto

private lemma frameSN_noncomm_sgn_neg (i a b : Fin k) (hab : a ≠ b) :
    sgnAut (p := 3) i * negSwapAut a b ≠ negSwapAut a b * sgnAut (p := 3) i ↔
      i = a ∨ i = b := by
  rw [show sgnAut (p := 3) i * negSwapAut a b ≠ negSwapAut a b * sgnAut (p := 3) i ↔
      ¬ Commute (sgnAut (p := 3) i) (negSwapAut a b) from Iff.rfl]
  rw [sgnAut_commute_negSwapAut_iff i hab]
  tauto

private lemma frameSN_noncomm_perm_sgn (i a b : Fin k) (hab : a ≠ b) :
    permAut (p := 3) (Equiv.swap a b) * sgnAut (p := 3) i ≠
        sgnAut (p := 3) i * permAut (p := 3) (Equiv.swap a b) ↔
      i = a ∨ i = b := by
  rw [show permAut (p := 3) (Equiv.swap a b) * sgnAut (p := 3) i ≠
      sgnAut (p := 3) i * permAut (p := 3) (Equiv.swap a b) ↔
      ¬ Commute (sgnAut (p := 3) i) (permAut (p := 3) (Equiv.swap a b)) from
    not_congr Commute.symm_iff]
  rw [sgnAut_commute_permAut_swap_iff i hab]
  tauto

private lemma frameSN_noncomm_neg_sgn (i a b : Fin k) (hab : a ≠ b) :
    negSwapAut a b * sgnAut (p := 3) i ≠ sgnAut (p := 3) i * negSwapAut a b ↔
      i = a ∨ i = b := by
  rw [show negSwapAut a b * sgnAut (p := 3) i ≠ sgnAut (p := 3) i * negSwapAut a b ↔
      ¬ Commute (sgnAut (p := 3) i) (negSwapAut a b) from
    not_congr Commute.symm_iff]
  rw [sgnAut_commute_negSwapAut_iff i hab]
  tauto

private lemma frameSN_noncomm_perm_perm (a b c d : Fin k) (hab : a ≠ b) (hcd : c ≠ d) :
    permAut (p := 3) (Equiv.swap a b) * permAut (p := 3) (Equiv.swap c d) ≠
        permAut (p := 3) (Equiv.swap c d) * permAut (p := 3) (Equiv.swap a b) ↔
      frameSN_meetOne a b (c, d) := by
  rw [show permAut (p := 3) (Equiv.swap a b) * permAut (p := 3) (Equiv.swap c d) ≠
      permAut (p := 3) (Equiv.swap c d) * permAut (p := 3) (Equiv.swap a b) ↔
      ¬ Commute (permAut (p := 3) (Equiv.swap a b))
        (permAut (p := 3) (Equiv.swap c d)) from Iff.rfl]
  rw [permAut_swap_commute_permAut_swap_iff hab hcd]
  exact (frameSN_meetOne_iff_not_table hab hcd).symm

private lemma frameSN_noncomm_perm_neg (a b c d : Fin k) (hab : a ≠ b) (hcd : c ≠ d) :
    permAut (p := 3) (Equiv.swap a b) * negSwapAut c d ≠
        negSwapAut c d * permAut (p := 3) (Equiv.swap a b) ↔
      frameSN_meetOne a b (c, d) := by
  rw [show permAut (p := 3) (Equiv.swap a b) * negSwapAut c d ≠
      negSwapAut c d * permAut (p := 3) (Equiv.swap a b) ↔
      ¬ Commute (permAut (p := 3) (Equiv.swap a b)) (negSwapAut c d) from Iff.rfl]
  rw [permAut_swap_commute_negSwapAut_iff hab hcd]
  exact (frameSN_meetOne_iff_not_table hab hcd).symm

private lemma frameSN_noncomm_neg_perm (a b c d : Fin k) (hab : a ≠ b) (hcd : c ≠ d) :
    negSwapAut a b * permAut (p := 3) (Equiv.swap c d) ≠
        permAut (p := 3) (Equiv.swap c d) * negSwapAut a b ↔
      frameSN_meetOne a b (c, d) := by
  rw [show negSwapAut a b * permAut (p := 3) (Equiv.swap c d) ≠
      permAut (p := 3) (Equiv.swap c d) * negSwapAut a b ↔
      ¬ Commute (permAut (p := 3) (Equiv.swap c d)) (negSwapAut a b) from
    not_congr Commute.symm_iff]
  rw [permAut_swap_commute_negSwapAut_iff hcd hab]
  simpa [eq_comm, and_comm, and_left_comm, and_assoc] using
    (frameSN_meetOne_iff_not_table hab hcd).symm

private lemma frameSN_noncomm_neg_neg (a b c d : Fin k) (hab : a ≠ b) (hcd : c ≠ d) :
    negSwapAut a b * negSwapAut c d ≠ negSwapAut c d * negSwapAut a b ↔
      frameSN_meetOne a b (c, d) := by
  rw [show negSwapAut a b * negSwapAut c d ≠ negSwapAut c d * negSwapAut a b ↔
      ¬ Commute (negSwapAut a b) (negSwapAut c d) from Iff.rfl]
  rw [negSwapAut_commute_negSwapAut_iff hab hcd]
  exact (frameSN_meetOne_iff_not_table hab hcd).symm

private lemma frameSN_ncard_noncomm_sgn_perm (i : Fin k) :
    Nat.card {x : frameSN_P (Fin k) //
      sgnAut (p := 3) i * permAut (p := 3) (Equiv.swap x.1.1 x.1.2) ≠
        permAut (p := 3) (Equiv.swap x.1.1 x.1.2) * sgnAut (p := 3) i} =
      Nat.card {x : frameSN_P (Fin k) // frameSN_contains i x.1} := by
  refine Nat.card_congr (Equiv.subtypeEquivRight (p := fun x : frameSN_P (Fin k) =>
    sgnAut (p := 3) i * permAut (p := 3) (Equiv.swap x.1.1 x.1.2) ≠
      permAut (p := 3) (Equiv.swap x.1.1 x.1.2) * sgnAut (p := 3) i)
    (q := fun x : frameSN_P (Fin k) => frameSN_contains i x.1) ?_)
  intro x
  simpa [frameSN_contains, eq_comm] using
    frameSN_noncomm_sgn_perm i x.1.1 x.1.2 x.2.ne

private lemma frameSN_ncard_noncomm_sgn_neg (i : Fin k) :
    Nat.card {x : frameSN_P (Fin k) //
      sgnAut (p := 3) i * negSwapAut x.1.1 x.1.2 ≠
        negSwapAut x.1.1 x.1.2 * sgnAut (p := 3) i} =
      Nat.card {x : frameSN_P (Fin k) // frameSN_contains i x.1} := by
  refine Nat.card_congr (Equiv.subtypeEquivRight (p := fun x : frameSN_P (Fin k) =>
    sgnAut (p := 3) i * negSwapAut x.1.1 x.1.2 ≠
      negSwapAut x.1.1 x.1.2 * sgnAut (p := 3) i)
    (q := fun x : frameSN_P (Fin k) => frameSN_contains i x.1) ?_)
  intro x
  simpa [frameSN_contains, eq_comm] using
    frameSN_noncomm_sgn_neg i x.1.1 x.1.2 x.2.ne

private lemma frameSN_ncard_noncomm_perm_sgn {a b : Fin k} (hab : a ≠ b) :
    Nat.card {i : Fin k //
      permAut (p := 3) (Equiv.swap a b) * sgnAut (p := 3) i ≠
        sgnAut (p := 3) i * permAut (p := 3) (Equiv.swap a b)} = 2 := by
  rw [Nat.card_congr (Equiv.subtypeEquivRight (p := fun i : Fin k =>
    permAut (p := 3) (Equiv.swap a b) * sgnAut (p := 3) i ≠
      sgnAut (p := 3) i * permAut (p := 3) (Equiv.swap a b))
    (q := fun i : Fin k => i = a ∨ i = b) (fun i => frameSN_noncomm_perm_sgn i a b hab))]
  rw [frameSN_natCard_subtype]
  have hset : {i : Fin k | i = a ∨ i = b} = ({a, b} : Set (Fin k)) := by
    ext i; simp [eq_comm]
  rw [hset, Set.ncard_pair hab]

private lemma frameSN_ncard_noncomm_perm_perm {a b : Fin k} (hab : a ≠ b) :
    Nat.card {x : frameSN_P (Fin k) //
      permAut (p := 3) (Equiv.swap a b) * permAut (p := 3) (Equiv.swap x.1.1 x.1.2) ≠
        permAut (p := 3) (Equiv.swap x.1.1 x.1.2) * permAut (p := 3) (Equiv.swap a b)} =
      2 * (k - 2) := by
  refine (Nat.card_congr (Equiv.subtypeEquivRight (p := fun x : frameSN_P (Fin k) =>
    permAut (p := 3) (Equiv.swap a b) * permAut (p := 3) (Equiv.swap x.1.1 x.1.2) ≠
      permAut (p := 3) (Equiv.swap x.1.1 x.1.2) * permAut (p := 3) (Equiv.swap a b))
    (q := fun x : frameSN_P (Fin k) => frameSN_meetOne a b x.1)
    (fun x => frameSN_noncomm_perm_perm a b x.1.1 x.1.2 hab x.2.ne))).trans ?_
  exact frameSN_ncard_meetOne hab

private lemma frameSN_ncard_noncomm_perm_neg {a b : Fin k} (hab : a ≠ b) :
    Nat.card {x : frameSN_P (Fin k) //
      permAut (p := 3) (Equiv.swap a b) * negSwapAut x.1.1 x.1.2 ≠
        negSwapAut x.1.1 x.1.2 * permAut (p := 3) (Equiv.swap a b)} = 2 * (k - 2) := by
  refine (Nat.card_congr (Equiv.subtypeEquivRight (p := fun x : frameSN_P (Fin k) =>
    permAut (p := 3) (Equiv.swap a b) * negSwapAut x.1.1 x.1.2 ≠
      negSwapAut x.1.1 x.1.2 * permAut (p := 3) (Equiv.swap a b))
    (q := fun x : frameSN_P (Fin k) => frameSN_meetOne a b x.1)
    (fun x => frameSN_noncomm_perm_neg a b x.1.1 x.1.2 hab x.2.ne))).trans ?_
  exact frameSN_ncard_meetOne hab

private lemma frameSN_ncard_noncomm_neg_perm {a b : Fin k} (hab : a ≠ b) :
    Nat.card {x : frameSN_P (Fin k) //
      negSwapAut a b * permAut (p := 3) (Equiv.swap x.1.1 x.1.2) ≠
        permAut (p := 3) (Equiv.swap x.1.1 x.1.2) * negSwapAut a b} = 2 * (k - 2) := by
  refine (Nat.card_congr (Equiv.subtypeEquivRight (p := fun x : frameSN_P (Fin k) =>
    negSwapAut a b * permAut (p := 3) (Equiv.swap x.1.1 x.1.2) ≠
      permAut (p := 3) (Equiv.swap x.1.1 x.1.2) * negSwapAut a b)
    (q := fun x : frameSN_P (Fin k) => frameSN_meetOne a b x.1)
    (fun x => frameSN_noncomm_neg_perm a b x.1.1 x.1.2 hab x.2.ne))).trans ?_
  exact frameSN_ncard_meetOne hab

private lemma frameSN_ncard_noncomm_neg_neg {a b : Fin k} (hab : a ≠ b) :
    Nat.card {x : frameSN_P (Fin k) //
      negSwapAut a b * negSwapAut x.1.1 x.1.2 ≠
        negSwapAut x.1.1 x.1.2 * negSwapAut a b} = 2 * (k - 2) := by
  refine (Nat.card_congr (Equiv.subtypeEquivRight (p := fun x : frameSN_P (Fin k) =>
    negSwapAut a b * negSwapAut x.1.1 x.1.2 ≠
      negSwapAut x.1.1 x.1.2 * negSwapAut a b)
    (q := fun x : frameSN_P (Fin k) => frameSN_meetOne a b x.1)
    (fun x => frameSN_noncomm_neg_neg a b x.1.1 x.1.2 hab x.2.ne))).trans ?_
  exact frameSN_ncard_meetOne hab

private lemma frameSN_ncard_noncomm_sgn_sgn (i : Fin k) :
    Nat.card {j : Fin k //
      sgnAut (p := 3) i * sgnAut (p := 3) j ≠
        sgnAut (p := 3) j * sgnAut (p := 3) i} = 0 := by
  rw [Nat.card_eq_zero]
  left
  exact ⟨fun j => j.2 (sgnAut_commute_sgnAut i j)⟩

private lemma frameSN_mem_signed_sgn (i : Fin k) :
    sgnAut (p := 3) i ∈ modelReflSet (signedPermSet k) := by
  rw [mem_modelReflSet_signedPermSet_iff]
  exact Or.inl ⟨i, rfl⟩

private lemma frameSN_mem_signed_perm {a b : Fin k} (hab : a ≠ b) :
    permAut (p := 3) (Equiv.swap a b) ∈ modelReflSet (signedPermSet k) := by
  rw [mem_modelReflSet_signedPermSet_iff]
  exact Or.inr ⟨a, b, hab, Or.inl rfl⟩

private lemma frameSN_mem_signed_neg {a b : Fin k} (hab : a ≠ b) :
    negSwapAut a b ∈ modelReflSet (signedPermSet k) := by
  rw [mem_modelReflSet_signedPermSet_iff]
  exact Or.inr ⟨a, b, hab, Or.inr rfl⟩

private lemma frameSN_mem_even_perm {a b : Fin k} (hab : a ≠ b) :
    permAut (p := 3) (Equiv.swap a b) ∈ modelReflSet (evenSignedPermSet k) := by
  rw [mem_modelReflSet_evenSignedPermSet_iff]
  exact ⟨a, b, hab, Or.inl rfl⟩

private lemma frameSN_mem_even_neg {a b : Fin k} (hab : a ≠ b) :
    negSwapAut a b ∈ modelReflSet (evenSignedPermSet k) := by
  rw [mem_modelReflSet_evenSignedPermSet_iff]
  exact ⟨a, b, hab, Or.inr rfl⟩

private lemma frameSN_degree_sgn (i : Fin k) :
    modelNonComm (signedPermSet k) (sgnAut (p := 3) i) = 2 * (k - 1) := by
  rw [modelNonComm, ← frameSN_range_B,
    frameSN_ncard_noncomm_range (frameSN_B (k := k)) frameSN_B_injective]
  rw [frameSN_card_subtype_sum]
  rw [frameSN_card_subtype_sum]
  simp only [frameSN_B, frameSN_L]
  rw [frameSN_ncard_noncomm_sgn_sgn, frameSN_ncard_noncomm_sgn_perm,
    frameSN_ncard_noncomm_sgn_neg, frameSN_ncard_contains]
  omega

private lemma frameSN_degree_perm {a b : Fin k} (hab : a ≠ b) :
    modelNonComm (signedPermSet k) (permAut (p := 3) (Equiv.swap a b)) = 4 * k - 6 := by
  rw [modelNonComm, ← frameSN_range_B,
    frameSN_ncard_noncomm_range (frameSN_B (k := k)) frameSN_B_injective]
  rw [frameSN_card_subtype_sum]
  rw [frameSN_card_subtype_sum]
  simp only [frameSN_B, frameSN_L]
  rw [frameSN_ncard_noncomm_perm_sgn hab,
    frameSN_ncard_noncomm_perm_perm hab, frameSN_ncard_noncomm_perm_neg hab]
  have hk2 : 2 ≤ k := by
    have h1 := a.isLt
    have h2 := b.isLt
    have hne : a.val ≠ b.val := fun h => hab (Fin.ext h)
    omega
  omega

private lemma frameSN_degree_even_perm {a b : Fin k} (hab : a ≠ b) :
    modelNonComm (evenSignedPermSet k) (permAut (p := 3) (Equiv.swap a b)) =
      4 * (k - 2) := by
  rw [modelNonComm, ← frameSN_range_L,
    frameSN_ncard_noncomm_range (frameSN_L (k := k)) frameSN_L_injective]
  rw [frameSN_card_subtype_sum]
  simp only [frameSN_L]
  rw [frameSN_ncard_noncomm_perm_perm hab, frameSN_ncard_noncomm_perm_neg hab]
  omega

private lemma frameSN_degree_even_neg {a b : Fin k} (hab : a ≠ b) :
    modelNonComm (evenSignedPermSet k) (negSwapAut a b) = 4 * (k - 2) := by
  rw [modelNonComm, ← frameSN_range_L,
    frameSN_ncard_noncomm_range (frameSN_L (k := k)) frameSN_L_injective]
  rw [frameSN_card_subtype_sum]
  simp only [frameSN_L]
  rw [frameSN_ncard_noncomm_neg_perm hab, frameSN_ncard_noncomm_neg_neg hab]
  omega

private lemma frameSN_pair_eq_of_contains_both {a b c d : Fin k} (hab : a ≠ b) (hcd : c ≠ d)
    (ha : frameSN_contains a (c, d)) (hb : frameSN_contains b (c, d)) :
    (c = a ∧ d = b) ∨ (c = b ∧ d = a) := by
  simp [frameSN_contains] at ha hb
  grind

private lemma frameSN_edge {X : Type} [Group X] {S : Set (MulAut X)} {u v : MulAut X}
    (hu : u ∈ modelReflSet S) (hv : v ∈ modelReflSet S) (h : u * v ≠ v * u) :
    Relation.ReflTransGen (fun a b => a ∈ modelReflSet S ∧ b ∈ modelReflSet S ∧
      a * b ≠ b * a) u v :=
  Relation.ReflTransGen.single ⟨hu, hv, h⟩

private lemma frameSN_reflTransGen_rev {X : Type} [Group X] {S : Set (MulAut X)} {u v : MulAut X}
    (h : Relation.ReflTransGen (fun a b => a ∈ modelReflSet S ∧ b ∈ modelReflSet S ∧
      a * b ≠ b * a) u v) :
    Relation.ReflTransGen (fun a b => a ∈ modelReflSet S ∧ b ∈ modelReflSet S ∧
      a * b ≠ b * a) v u := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hcd ih =>
      exact Relation.ReflTransGen.head ⟨hcd.2.1, hcd.1, fun h => hcd.2.2 h.symm⟩ ih

private lemma frameSN_signed_sgn_path_to (i0 i : Fin k) :
    Relation.ReflTransGen (fun a b => a ∈ modelReflSet (signedPermSet k) ∧
      b ∈ modelReflSet (signedPermSet k) ∧ a * b ≠ b * a)
      (sgnAut (p := 3) i) (sgnAut (p := 3) i0) := by
  by_cases hi : i = i0
  · rw [hi]
  · have hi0 : i0 ≠ i := Ne.symm hi
    have h1 : sgnAut (p := 3) i * permAut (p := 3) (Equiv.swap i0 i) ≠
        permAut (p := 3) (Equiv.swap i0 i) * sgnAut (p := 3) i :=
      (frameSN_noncomm_sgn_perm i i0 i hi0).mpr (Or.inr rfl)
    have h2 : permAut (p := 3) (Equiv.swap i0 i) * sgnAut (p := 3) i0 ≠
        sgnAut (p := 3) i0 * permAut (p := 3) (Equiv.swap i0 i) :=
      (frameSN_noncomm_perm_sgn i0 i0 i hi0).mpr (Or.inl rfl)
    exact (frameSN_edge (frameSN_mem_signed_sgn i) (frameSN_mem_signed_perm hi0) h1).trans
      (frameSN_edge (frameSN_mem_signed_perm hi0) (frameSN_mem_signed_sgn i0) h2)

private lemma frameSN_signed_perm_path_to (i0 : Fin k) (x : frameSN_P (Fin k)) :
    Relation.ReflTransGen (fun a b => a ∈ modelReflSet (signedPermSet k) ∧
      b ∈ modelReflSet (signedPermSet k) ∧ a * b ≠ b * a)
      (permAut (p := 3) (Equiv.swap x.1.1 x.1.2)) (sgnAut (p := 3) i0) := by
  have hab := x.2.ne
  by_cases h0 : frameSN_contains i0 x.1
  · have hnc : permAut (p := 3) (Equiv.swap x.1.1 x.1.2) * sgnAut (p := 3) i0 ≠
        sgnAut (p := 3) i0 * permAut (p := 3) (Equiv.swap x.1.1 x.1.2) :=
      (frameSN_noncomm_perm_sgn i0 x.1.1 x.1.2 hab).mpr
        (by simpa [frameSN_contains, eq_comm] using h0)
    exact frameSN_edge (frameSN_mem_signed_perm hab) (frameSN_mem_signed_sgn i0) hnc
  · have hne : i0 ≠ x.1.1 := fun h => h0 (Or.inl h.symm)
    have h1 : permAut (p := 3) (Equiv.swap x.1.1 x.1.2) * sgnAut (p := 3) x.1.1 ≠
        sgnAut (p := 3) x.1.1 * permAut (p := 3) (Equiv.swap x.1.1 x.1.2) :=
      (frameSN_noncomm_perm_sgn x.1.1 x.1.1 x.1.2 hab).mpr (Or.inl rfl)
    have h2 : sgnAut (p := 3) x.1.1 * permAut (p := 3) (Equiv.swap i0 x.1.1) ≠
        permAut (p := 3) (Equiv.swap i0 x.1.1) * sgnAut (p := 3) x.1.1 :=
      (frameSN_noncomm_sgn_perm x.1.1 i0 x.1.1 hne).mpr (Or.inr rfl)
    have h3 : permAut (p := 3) (Equiv.swap i0 x.1.1) * sgnAut (p := 3) i0 ≠
        sgnAut (p := 3) i0 * permAut (p := 3) (Equiv.swap i0 x.1.1) :=
      (frameSN_noncomm_perm_sgn i0 i0 x.1.1 hne).mpr (Or.inl rfl)
    exact ((frameSN_edge (frameSN_mem_signed_perm hab)
      (frameSN_mem_signed_sgn x.1.1) h1).trans
      (frameSN_edge (frameSN_mem_signed_sgn x.1.1)
        (frameSN_mem_signed_perm hne) h2)).trans
      (frameSN_edge (frameSN_mem_signed_perm hne) (frameSN_mem_signed_sgn i0) h3)

private lemma frameSN_signed_neg_path_to (i0 : Fin k) (x : frameSN_P (Fin k)) :
    Relation.ReflTransGen (fun a b => a ∈ modelReflSet (signedPermSet k) ∧
      b ∈ modelReflSet (signedPermSet k) ∧ a * b ≠ b * a)
      (negSwapAut x.1.1 x.1.2) (sgnAut (p := 3) i0) := by
  have hab := x.2.ne
  by_cases h0 : frameSN_contains i0 x.1
  · have hnc : negSwapAut x.1.1 x.1.2 * sgnAut (p := 3) i0 ≠
        sgnAut (p := 3) i0 * negSwapAut x.1.1 x.1.2 :=
      (frameSN_noncomm_neg_sgn i0 x.1.1 x.1.2 hab).mpr
        (by simpa [frameSN_contains, eq_comm] using h0)
    exact frameSN_edge (frameSN_mem_signed_neg hab) (frameSN_mem_signed_sgn i0) hnc
  · have hne : i0 ≠ x.1.1 := fun h => h0 (Or.inl h.symm)
    have h1 : negSwapAut x.1.1 x.1.2 * sgnAut (p := 3) x.1.1 ≠
        sgnAut (p := 3) x.1.1 * negSwapAut x.1.1 x.1.2 :=
      (frameSN_noncomm_neg_sgn x.1.1 x.1.1 x.1.2 hab).mpr (Or.inl rfl)
    have h2 : sgnAut (p := 3) x.1.1 * permAut (p := 3) (Equiv.swap i0 x.1.1) ≠
        permAut (p := 3) (Equiv.swap i0 x.1.1) * sgnAut (p := 3) x.1.1 :=
      (frameSN_noncomm_sgn_perm x.1.1 i0 x.1.1 hne).mpr (Or.inr rfl)
    have h3 : permAut (p := 3) (Equiv.swap i0 x.1.1) * sgnAut (p := 3) i0 ≠
        sgnAut (p := 3) i0 * permAut (p := 3) (Equiv.swap i0 x.1.1) :=
      (frameSN_noncomm_perm_sgn i0 i0 x.1.1 hne).mpr (Or.inl rfl)
    exact ((frameSN_edge (frameSN_mem_signed_neg hab)
      (frameSN_mem_signed_sgn x.1.1) h1).trans
      (frameSN_edge (frameSN_mem_signed_sgn x.1.1)
        (frameSN_mem_signed_perm hne) h2)).trans
      (frameSN_edge (frameSN_mem_signed_perm hne) (frameSN_mem_signed_sgn i0) h3)

private lemma frameSN_signed_path_to (i0 : Fin k) (u : MulAut (Fin k → Multiplicative (ZMod 3)))
    (hu : u ∈ modelReflSet (signedPermSet k)) :
    Relation.ReflTransGen (fun a b => a ∈ modelReflSet (signedPermSet k) ∧
      b ∈ modelReflSet (signedPermSet k) ∧ a * b ≠ b * a) u (sgnAut (p := 3) i0) := by
  rw [← frameSN_range_B] at hu
  obtain ⟨x, rfl⟩ := hu
  cases x with
  | inl i => exact frameSN_signed_sgn_path_to i0 i
  | inr y =>
    cases y with
    | inl x => exact frameSN_signed_perm_path_to i0 x
    | inr x => exact frameSN_signed_neg_path_to i0 x

private lemma frameSN_meetOne_swap {a b c d : Fin k} (hab : a ≠ b) (hcd : c ≠ d) :
    frameSN_meetOne a b (c, d) ↔ frameSN_meetOne c d (a, b) := by
  simp only [frameSN_meetOne, frameSN_contains]
  grind

private lemma frameSN_not_contains_of_not_both_of_not_meet {i j : Fin k} {x : frameSN_P (Fin k)}
    (hboth : ¬ (frameSN_contains i x.1 ∧ frameSN_contains j x.1))
    (hmeet : ¬ frameSN_meetOne i j x.1) :
    ¬ frameSN_contains i x.1 ∧ ¬ frameSN_contains j x.1 := by
  constructor
  · intro hi
    by_cases hj : frameSN_contains j x.1
    · exact hboth ⟨hi, hj⟩
    · exact hmeet (Or.inl ⟨hi, hj⟩)
  · intro hj
    by_cases hi : frameSN_contains i x.1
    · exact hboth ⟨hi, hj⟩
    · exact hmeet (Or.inr ⟨hi, hj⟩)

private lemma frameSN_even_perm_path_to (i0 i1 : Fin k) (h01 : i0 ≠ i1)
    (x : frameSN_P (Fin k)) :
    Relation.ReflTransGen (fun a b => a ∈ modelReflSet (evenSignedPermSet k) ∧
      b ∈ modelReflSet (evenSignedPermSet k) ∧ a * b ≠ b * a)
      (permAut (p := 3) (Equiv.swap x.1.1 x.1.2))
      (permAut (p := 3) (Equiv.swap i0 i1)) := by
  have hab := x.2.ne
  by_cases hboth : frameSN_contains i0 x.1 ∧ frameSN_contains i1 x.1
  · have hp : permAut (p := 3) (Equiv.swap x.1.1 x.1.2) =
        permAut (p := 3) (Equiv.swap i0 i1) :=
      (permAut_swap_eq_permAut_swap_iff hab h01).mpr
        (frameSN_pair_eq_of_contains_both h01 hab hboth.1 hboth.2)
    rw [hp]
  · by_cases hmeet : frameSN_meetOne i0 i1 x.1
    · exact frameSN_edge (frameSN_mem_even_perm hab) (frameSN_mem_even_perm h01)
        ((frameSN_noncomm_perm_perm x.1.1 x.1.2 i0 i1 hab h01).mpr
          (frameSN_meetOne_swap h01 hab |>.mp hmeet))
    · have hnone := frameSN_not_contains_of_not_both_of_not_meet hboth hmeet
      have ha0 : x.1.1 ≠ i0 := fun h => hnone.1 (Or.inl h)
      have hb0 : x.1.2 ≠ i0 := fun h => hnone.1 (Or.inr h)
      have ha1 : x.1.1 ≠ i1 := fun h => hnone.2 (Or.inl h)
      have h0a : i0 ≠ x.1.1 := fun h => ha0 h.symm
      have hm1 : frameSN_meetOne x.1.1 x.1.2 (i0, x.1.1) :=
        Or.inl ⟨Or.inr rfl, by
          rintro (h | h)
          · exact hb0 h.symm
          · exact hab h⟩
      have hm2 : frameSN_meetOne i0 x.1.1 (i0, i1) :=
        Or.inl ⟨Or.inl rfl, by
          rintro (h | h)
          · exact ha0 h.symm
          · exact ha1 h.symm⟩
      have h1 : permAut (p := 3) (Equiv.swap x.1.1 x.1.2) *
          permAut (p := 3) (Equiv.swap i0 x.1.1) ≠
          permAut (p := 3) (Equiv.swap i0 x.1.1) *
            permAut (p := 3) (Equiv.swap x.1.1 x.1.2) :=
        (frameSN_noncomm_perm_perm x.1.1 x.1.2 i0 x.1.1 hab h0a).mpr hm1
      have h2 : permAut (p := 3) (Equiv.swap i0 x.1.1) *
          permAut (p := 3) (Equiv.swap i0 i1) ≠
          permAut (p := 3) (Equiv.swap i0 i1) *
            permAut (p := 3) (Equiv.swap i0 x.1.1) :=
        (frameSN_noncomm_perm_perm i0 x.1.1 i0 i1 h0a h01).mpr hm2
      exact (frameSN_edge (frameSN_mem_even_perm hab) (frameSN_mem_even_perm h0a) h1).trans
        (frameSN_edge (frameSN_mem_even_perm h0a) (frameSN_mem_even_perm h01) h2)

private lemma frameSN_even_neg_both_path_to (i0 i1 i2 : Fin k)
    (h01 : i0 ≠ i1) (h02 : i0 ≠ i2) (h12 : i1 ≠ i2) :
    Relation.ReflTransGen (fun a b => a ∈ modelReflSet (evenSignedPermSet k) ∧
      b ∈ modelReflSet (evenSignedPermSet k) ∧ a * b ≠ b * a)
      (negSwapAut i0 i1) (permAut (p := 3) (Equiv.swap i0 i1)) := by
  have hm3 : frameSN_meetOne i0 i1 (i1, i2) :=
    Or.inr ⟨by
      rintro (h | h)
      · exact h01 h.symm
      · exact h02 h.symm, Or.inl rfl⟩
  have hm4 : frameSN_meetOne i1 i2 (i0, i1) :=
    Or.inl ⟨Or.inr rfl, by
      rintro (h | h)
      · exact h02 h
      · exact h12 h⟩
  have h1 : negSwapAut i0 i1 * permAut (p := 3) (Equiv.swap i1 i2) ≠
      permAut (p := 3) (Equiv.swap i1 i2) * negSwapAut i0 i1 :=
    (frameSN_noncomm_neg_perm i0 i1 i1 i2 h01 h12).mpr hm3
  have h2 : permAut (p := 3) (Equiv.swap i1 i2) *
      permAut (p := 3) (Equiv.swap i0 i1) ≠
      permAut (p := 3) (Equiv.swap i0 i1) *
        permAut (p := 3) (Equiv.swap i1 i2) :=
    (frameSN_noncomm_perm_perm i1 i2 i0 i1 h12 h01).mpr hm4
  exact (frameSN_edge (frameSN_mem_even_neg h01) (frameSN_mem_even_perm h12) h1).trans
    (frameSN_edge (frameSN_mem_even_perm h12) (frameSN_mem_even_perm h01) h2)

private lemma frameSN_even_neg_path_to (i0 i1 i2 : Fin k)
    (h01 : i0 ≠ i1) (h02 : i0 ≠ i2) (h12 : i1 ≠ i2)
    (x : frameSN_P (Fin k)) :
    Relation.ReflTransGen (fun a b => a ∈ modelReflSet (evenSignedPermSet k) ∧
      b ∈ modelReflSet (evenSignedPermSet k) ∧ a * b ≠ b * a)
      (negSwapAut x.1.1 x.1.2) (permAut (p := 3) (Equiv.swap i0 i1)) := by
  have hab := x.2.ne
  by_cases hboth : frameSN_contains i0 x.1 ∧ frameSN_contains i1 x.1
  · have hp : negSwapAut x.1.1 x.1.2 = negSwapAut i0 i1 :=
      (negSwapAut_eq_negSwapAut_iff hab h01).mpr
        (frameSN_pair_eq_of_contains_both h01 hab hboth.1 hboth.2)
    rw [hp]
    exact frameSN_even_neg_both_path_to i0 i1 i2 h01 h02 h12
  · by_cases hmeet : frameSN_meetOne i0 i1 x.1
    · exact frameSN_edge (frameSN_mem_even_neg hab) (frameSN_mem_even_perm h01)
        ((frameSN_noncomm_neg_perm x.1.1 x.1.2 i0 i1 hab h01).mpr
          (frameSN_meetOne_swap h01 hab |>.mp hmeet))
    · have hnone := frameSN_not_contains_of_not_both_of_not_meet hboth hmeet
      have ha0 : x.1.1 ≠ i0 := fun h => hnone.1 (Or.inl h)
      have hb0 : x.1.2 ≠ i0 := fun h => hnone.1 (Or.inr h)
      have ha1 : x.1.1 ≠ i1 := fun h => hnone.2 (Or.inl h)
      have h0a : i0 ≠ x.1.1 := fun h => ha0 h.symm
      have hm1 : frameSN_meetOne x.1.1 x.1.2 (i0, x.1.1) :=
        Or.inl ⟨Or.inr rfl, by
          rintro (h | h)
          · exact hb0 h.symm
          · exact hab h⟩
      have hm2 : frameSN_meetOne i0 x.1.1 (i0, i1) :=
        Or.inl ⟨Or.inl rfl, by
          rintro (h | h)
          · exact ha0 h.symm
          · exact ha1 h.symm⟩
      have h1 : negSwapAut x.1.1 x.1.2 * permAut (p := 3) (Equiv.swap i0 x.1.1) ≠
          permAut (p := 3) (Equiv.swap i0 x.1.1) * negSwapAut x.1.1 x.1.2 :=
        (frameSN_noncomm_neg_perm x.1.1 x.1.2 i0 x.1.1 hab h0a).mpr hm1
      have h2 : permAut (p := 3) (Equiv.swap i0 x.1.1) *
          permAut (p := 3) (Equiv.swap i0 i1) ≠
          permAut (p := 3) (Equiv.swap i0 i1) *
            permAut (p := 3) (Equiv.swap i0 x.1.1) :=
        (frameSN_noncomm_perm_perm i0 x.1.1 i0 i1 h0a h01).mpr hm2
      exact (frameSN_edge (frameSN_mem_even_neg hab) (frameSN_mem_even_perm h0a) h1).trans
        (frameSN_edge (frameSN_mem_even_perm h0a) (frameSN_mem_even_perm h01) h2)

private lemma frameSN_even_path_to (i0 i1 i2 : Fin k)
    (h01 : i0 ≠ i1) (h02 : i0 ≠ i2) (h12 : i1 ≠ i2)
    (u : MulAut (Fin k → Multiplicative (ZMod 3)))
    (hu : u ∈ modelReflSet (evenSignedPermSet k)) :
    Relation.ReflTransGen (fun a b => a ∈ modelReflSet (evenSignedPermSet k) ∧
      b ∈ modelReflSet (evenSignedPermSet k) ∧ a * b ≠ b * a) u
      (permAut (p := 3) (Equiv.swap i0 i1)) := by
  rw [← frameSN_range_L] at hu
  obtain ⟨x, rfl⟩ := hu
  cases x with
  | inl x => exact frameSN_even_perm_path_to i0 i1 h01 x
  | inr x => exact frameSN_even_neg_path_to i0 i1 i2 h01 h02 h12 x

private lemma frameSN_distinct012 {k : ℕ} (hk : 3 ≤ k) :
    (⟨0, by omega⟩ : Fin k) ≠ ⟨1, by omega⟩ ∧
      (⟨0, by omega⟩ : Fin k) ≠ ⟨2, by omega⟩ ∧
      (⟨1, by omega⟩ : Fin k) ≠ ⟨2, by omega⟩ := by
  refine ⟨?_, ?_, ?_⟩ <;>
    intro h <;> have hv := congrArg Fin.val h <;> simp at hv

theorem modelNumIs_signedPermSet (hk : 3 ≤ k) : ModelNumIs (signedPermSet k) (k ^ 2) none := by
  constructor
  · rw [← frameSN_range_B, Set.ncard_range_of_injective frameSN_B_injective]
    simp only [Nat.card_sum, Nat.card_fin, Fintype.card_fin, frameSN_card_P]
    have h2 : 2 * k.choose 2 = k * (k - 1) := by
      rw [Nat.choose_two_right]
      exact Nat.mul_div_cancel' (Nat.even_mul_pred_self k).two_dvd
    obtain ⟨n, rfl⟩ : ∃ n, k = n + 3 := ⟨k - 3, by omega⟩
    have h2' : 2 * (n + 3).choose 2 = (n + 3) * (n + 2) := by
      simpa using h2
    have hC : (n + 3).choose 2 + (n + 3).choose 2 = (n + 3) * (n + 2) := by
      omega
    rw [hC]
    ring
  · rintro ⟨d, hd⟩
    let i0 : Fin k := ⟨0, by omega⟩
    let i1 : Fin k := ⟨1, by omega⟩
    have hi01 : i0 ≠ i1 := by
      intro h
      have hv := congrArg Fin.val h
      simp [i0, i1] at hv
    have e0 := hd _ (frameSN_mem_signed_sgn i0)
    have e1 := hd _ (frameSN_mem_signed_perm hi01)
    rw [frameSN_degree_sgn] at e0
    rw [frameSN_degree_perm hi01] at e1
    omega

theorem modelConn_signedPermSet : ModelConn (signedPermSet k) := by
  by_cases hk0 : k = 0
  · subst hk0
    intro u hu v hv
    rw [← frameSN_range_B] at hu
    obtain ⟨x, _⟩ := hu
    cases x with
    | inl i => exact Fin.elim0 i
    | inr y =>
      cases y with
      | inl x => exact Fin.elim0 x.1.1
      | inr x => exact Fin.elim0 x.1.1
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
    let i0 : Fin k := ⟨0, hkpos⟩
    intro u hu v hv
    exact (frameSN_signed_path_to i0 u hu).trans
      (frameSN_reflTransGen_rev (frameSN_signed_path_to i0 v hv))

theorem modelNumIs_evenSignedPermSet (hk : 3 ≤ k) :
    ModelNumIs (evenSignedPermSet k) (k * (k - 1)) (some (4 * (k - 2))) := by
  constructor
  · rw [← frameSN_range_L, Set.ncard_range_of_injective frameSN_L_injective]
    simp only [Nat.card_sum, Fintype.card_fin, frameSN_card_P]
    have h2 : 2 * k.choose 2 = k * (k - 1) := by
      rw [Nat.choose_two_right]
      exact Nat.mul_div_cancel' (Nat.even_mul_pred_self k).two_dvd
    omega
  · intro u hu
    rw [← frameSN_range_L] at hu
    obtain ⟨x, rfl⟩ := hu
    cases x with
    | inl x => exact frameSN_degree_even_perm x.2.ne
    | inr x => exact frameSN_degree_even_neg x.2.ne

theorem modelConn_evenSignedPermSet (hk : 3 ≤ k) : ModelConn (evenSignedPermSet k) := by
  let i0 : Fin k := ⟨0, by omega⟩
  let i1 : Fin k := ⟨1, by omega⟩
  let i2 : Fin k := ⟨2, by omega⟩
  have hdist := frameSN_distinct012 hk
  have h01 : i0 ≠ i1 := hdist.1
  have h02 : i0 ≠ i2 := hdist.2.1
  have h12 : i1 ≠ i2 := hdist.2.2
  intro u hu v hv
  exact (frameSN_even_path_to i0 i1 i2 h01 h02 h12 u hu).trans
    (frameSN_reflTransGen_rev (frameSN_even_path_to i0 i1 i2 h01 h02 h12 v hv))

end CFSG.StandardType.FrameRoute

end
