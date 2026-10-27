module

public import CFSG.RankThree.PartOne.KE.Rank2Lines
public import CFSG.RankThree.PartOne.KE.D4TranspositionInterface

public noncomputable section

namespace CFSG.RankThree.PartOne.KE

open Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley CFSG.RankThree.Lattice
open scoped Matrix

section Lists

@[expose] def e7wl (w : List (Fin Tag.E7.rank)) : List (List ℤ) :=
  lword Tag.E7.rank (cartanList Tag.E7) (w.map Fin.val)

theorem wordMat_e7wl (w : List (Fin Tag.E7.rank)) :
    wordMat Tag.E7 w = toMat Tag.E7.rank (e7wl w) :=
  wordMat_eq_toMat Tag.E7 w rfl

theorem wordProd_smul_toVec7 (w : List (Fin Tag.E7.rank)) (l : List ℤ) :
    (coxeterSystem Tag.E7).wordProd w • toVec Tag.E7.rank l =
      toVec Tag.E7.rank (lmulVec Tag.E7.rank (e7wl w) l) := by
  rw [wordProd_smul_eq_wordMat_mulVec, wordMat_e7wl, toVec_lmulVec]

@[expose] def classSetL7 (rows : List LineRow) (j : ℕ) : Set (Fin Tag.E7.rank → ℤ) :=
  {α | ∃ l ∈ lineClassRoots rows j, α = toVec Tag.E7.rank l}

theorem setOfList_eq7 {A B : List (List ℤ)} (h1 : ∀ l ∈ A, l ∈ B) (h2 : ∀ l ∈ B, l ∈ A) :
    {α : Fin Tag.E7.rank → ℤ | ∃ l ∈ A, α = toVec Tag.E7.rank l} =
      {α | ∃ l ∈ B, α = toVec Tag.E7.rank l} := by
  ext α
  constructor
  · rintro ⟨l, hl, rfl⟩
    exact ⟨l, h1 l hl, rfl⟩
  · rintro ⟨l, hl, rfl⟩
    exact ⟨l, h2 l hl, rfl⟩

@[expose] def e7D4RootList : List (List ℤ) := [
    [0, -1, -1, -2, -1, 0, 0], [0, -1, -1, -1, -1, 0, 0], [0, -1, -1, -1, 0, 0, 0],
    [0, -1, 0, -1, -1, 0, 0], [0, -1, 0, -1, 0, 0, 0], [0, -1, 0, 0, 0, 0, 0],
    [0, 0, -1, -1, -1, 0, 0], [0, 0, -1, -1, 0, 0, 0], [0, 0, -1, 0, 0, 0, 0],
    [0, 0, 0, -1, -1, 0, 0], [0, 0, 0, -1, 0, 0, 0], [0, 0, 0, 0, -1, 0, 0],
    [0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 1, 0, 0],
    [0, 0, 1, 0, 0, 0, 0], [0, 0, 1, 1, 0, 0, 0], [0, 0, 1, 1, 1, 0, 0],
    [0, 1, 0, 0, 0, 0, 0], [0, 1, 0, 1, 0, 0, 0], [0, 1, 0, 1, 1, 0, 0],
    [0, 1, 1, 1, 0, 0, 0], [0, 1, 1, 1, 1, 0, 0], [0, 1, 1, 2, 1, 0, 0]]

theorem e7D4_complete : ∀ l ∈ Tag.E7.artifactRoots,
    (∀ k : Fin Tag.E7.rank, ¬ (1 ≤ k.val ∧ k.val ≤ 4) → vget l k.val = 0) →
      l ∈ e7D4RootList := by
  decide +kernel

theorem e7D4_sound : ∀ l ∈ e7D4RootList,
    l ∈ Tag.E7.artifactRoots ∧
      ∀ k : Fin Tag.E7.rank, ¬ (1 ≤ k.val ∧ k.val ≤ 4) → vget l k.val = 0 := by
  decide +kernel

theorem parabolicRoots_d4_eq7 :
    parabolicRoots Tag.E7 (d4Nodes Tag.E7) =
      {α | ∃ l ∈ e7D4RootList, α = toVec Tag.E7.rank l} := by
  ext α
  constructor
  · rintro ⟨hα, hsupp⟩
    obtain ⟨l, hl, rfl⟩ := isRoot_iff_exists_mem.1 hα
    refine ⟨l, e7D4_complete l hl (fun k hk => ?_), rfl⟩
    exact hsupp k hk
  · rintro ⟨l, hl, rfl⟩
    obtain ⟨hl', hs⟩ := e7D4_sound l hl
    exact ⟨isRoot_toVec hl', fun k hk => hs k hk⟩

@[expose] def e7perm2 (a b : Fin Tag.E7.rank) (l : List ℤ) : List ℤ :=
  List.ofFn fun k : Fin Tag.E7.rank => vget l ((Equiv.swap a b) k).val

theorem permLattice_toVec_swap7 (a b : Fin Tag.E7.rank) (l : List ℤ) :
    permLattice (Equiv.swap a b) (toVec Tag.E7.rank l) = toVec Tag.E7.rank (e7perm2 a b l) := by
  funext k
  simp only [permLattice, Function.comp_apply, Equiv.symm_swap]
  simp [toVec, vget, e7perm2]

end Lists

section Cert

structure D4A1Cert where
  cls : ℕ
  w : List (Fin Tag.E7.rank)
  u : List (Fin Tag.E7.rank)
  a : Fin Tag.E7.rank
  b : Fin Tag.E7.rank
  r : List ℤ

@[expose] def D4A1Cert.Good (S0 : List (List ℤ)) (rows : List LineRow)
    (ww : List (Fin Tag.E7.rank)) (c : D4A1Cert) : Prop :=
  (∀ l ∈ S0 ++ lineClassRoots rows c.cls,
    l ∈ e7D4RootList.map (lmulVec Tag.E7.rank (e7wl c.w)) ++ [c.r, vneg Tag.E7.rank c.r]) ∧
  (∀ l ∈ e7D4RootList.map (lmulVec Tag.E7.rank (e7wl c.w)) ++ [c.r, vneg Tag.E7.rank c.r],
    l ∈ S0 ++ lineClassRoots rows c.cls) ∧
  c.r ∈ Tag.E7.artifactRoots ∧ c.r ∈ S0 ∧
  (∀ l ∈ e7D4RootList.map (lmulVec Tag.E7.rank (e7wl c.w)),
    toVec Tag.E7.rank l ⬝ᵥ (Tag.E7.symmetrizedCartan *ᵥ toVec Tag.E7.rank c.r) = 0) ∧
  lmulVec Tag.E7.rank (e7wl ww) c.r = c.r ∧
  (∀ x ∈ c.u, 1 ≤ x.val ∧ x.val ≤ 4) ∧ c.a ≠ c.b ∧
  (c.a.val = 1 ∨ c.a.val = 2 ∨ c.a.val = 4) ∧ (c.b.val = 1 ∨ c.b.val = 2 ∨ c.b.val = 4) ∧
  (∀ l ∈ e7D4RootList, lmulVec Tag.E7.rank (e7wl (c.w.reverse ++ ww ++ c.w)) l =
    lmulVec Tag.E7.rank (e7wl c.u) (e7perm2 c.a c.b l))

instance d4A1Cert_decidableGood (S0 : List (List ℤ)) (rows : List LineRow)
    (ww : List (Fin Tag.E7.rank)) (c : D4A1Cert) : Decidable (c.Good S0 rows ww) := by
  unfold D4A1Cert.Good
  infer_instance

theorem D4A1Cert.sound {S0 : List (List ℤ)} {rows : List LineRow}
    {ww : List (Fin Tag.E7.rank)} {c : D4A1Cert} (h : c.Good S0 rows ww) :
    IsRoot Tag.E7 (toVec Tag.E7.rank c.r) ∧
      toVec Tag.E7.rank c.r ∈ {α | ∃ l ∈ S0, α = toVec Tag.E7.rank l} ∧
      ({α | ∃ l ∈ S0, α = toVec Tag.E7.rank l} ∪ classSetL7 rows c.cls =
        (fun γ => (coxeterSystem Tag.E7).wordProd c.w • γ) ''
          parabolicRoots Tag.E7 (d4Nodes Tag.E7) ∪
            {toVec Tag.E7.rank c.r, -toVec Tag.E7.rank c.r}) ∧
      (∀ α ∈ (fun γ => (coxeterSystem Tag.E7).wordProd c.w • γ) ''
          parabolicRoots Tag.E7 (d4Nodes Tag.E7),
        α ⬝ᵥ (Tag.E7.symmetrizedCartan *ᵥ toVec Tag.E7.rank c.r) = 0) ∧
      (coxeterSystem Tag.E7).wordProd ww • toVec Tag.E7.rank c.r = toVec Tag.E7.rank c.r ∧
      ∃ u ∈ parabolicWeylGroup Tag.E7 (d4Nodes Tag.E7),
        ∀ α ∈ parabolicRoots Tag.E7 (d4Nodes Tag.E7),
          (((coxeterSystem Tag.E7).wordProd c.w)⁻¹ * (coxeterSystem Tag.E7).wordProd ww *
            (coxeterSystem Tag.E7).wordProd c.w) • α =
            u • permLattice (Equiv.swap c.a c.b) α := by
  obtain ⟨h1, h2, hr, hrS, h4, h5, h6, hab, -, -, h9⟩ := h
  have hD4 : (fun γ => (coxeterSystem Tag.E7).wordProd c.w • γ) ''
      parabolicRoots Tag.E7 (d4Nodes Tag.E7) =
        {α | ∃ l ∈ e7D4RootList.map (lmulVec Tag.E7.rank (e7wl c.w)),
          α = toVec Tag.E7.rank l} := by
    rw [parabolicRoots_d4_eq7]
    ext β
    constructor
    · rintro ⟨α, ⟨l, hl, rfl⟩, rfl⟩
      exact ⟨_, List.mem_map.2 ⟨l, hl, rfl⟩, wordProd_smul_toVec7 c.w l⟩
    · rintro ⟨l, hl, rfl⟩
      obtain ⟨l', hl', rfl⟩ := List.mem_map.1 hl
      exact ⟨toVec _ l', ⟨l', hl', rfl⟩, wordProd_smul_toVec7 c.w l'⟩
  refine ⟨isRoot_toVec hr, ⟨c.r, hrS, rfl⟩, ?_, ?_, ?_, ?_⟩
  · rw [hD4, classSetL7]
    have hset := setOfList_eq7 h1 h2
    ext α
    have hα := Set.ext_iff.1 hset α
    simp only [Set.mem_union, Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    simp only [Set.mem_ofPred_eq] at hα
    constructor
    · rintro (⟨l, hl, hαl⟩ | ⟨l, hl, hαl⟩)
      · obtain ⟨l', hl', hαl'⟩ := hα.1 ⟨l, List.mem_append_left _ hl, hαl⟩
        rcases List.mem_append.1 hl' with hl' | hl'
        · exact Or.inl ⟨l', hl', hαl'⟩
        · rcases List.mem_cons.1 hl' with rfl | hl'
          · exact Or.inr (Or.inl hαl')
          · rcases List.mem_cons.1 hl' with rfl | hl'
            · exact Or.inr (Or.inr (by rw [hαl', toVec_vneg]))
            · exact absurd hl' (List.not_mem_nil)
      · obtain ⟨l', hl', hαl'⟩ := hα.1 ⟨l, List.mem_append_right _ hl, hαl⟩
        rcases List.mem_append.1 hl' with hl' | hl'
        · exact Or.inl ⟨l', hl', hαl'⟩
        · rcases List.mem_cons.1 hl' with rfl | hl'
          · exact Or.inr (Or.inl hαl')
          · rcases List.mem_cons.1 hl' with rfl | hl'
            · exact Or.inr (Or.inr (by rw [hαl', toVec_vneg]))
            · exact absurd hl' (List.not_mem_nil)
    · rintro (⟨l, hl, hαl⟩ | hαr | hαr)
      · obtain ⟨l', hl', hαl'⟩ := hα.2 ⟨l, List.mem_append_left _ hl, hαl⟩
        rcases List.mem_append.1 hl' with hl' | hl'
        · exact Or.inl ⟨l', hl', hαl'⟩
        · exact Or.inr ⟨l', hl', hαl'⟩
      · obtain ⟨l', hl', hαl'⟩ := hα.2 ⟨c.r, List.mem_append_right _
          (List.mem_cons_self), hαr⟩
        rcases List.mem_append.1 hl' with hl' | hl'
        · exact Or.inl ⟨l', hl', hαl'⟩
        · exact Or.inr ⟨l', hl', hαl'⟩
      · obtain ⟨l', hl', hαl'⟩ := hα.2 ⟨vneg Tag.E7.rank c.r, List.mem_append_right _
          (List.mem_cons_of_mem _ List.mem_cons_self), by rw [hαr, toVec_vneg]⟩
        rcases List.mem_append.1 hl' with hl' | hl'
        · exact Or.inl ⟨l', hl', hαl'⟩
        · exact Or.inr ⟨l', hl', hαl'⟩
  · rw [hD4]
    rintro _ ⟨l, hl, rfl⟩
    exact h4 l hl
  · rw [wordProd_smul_toVec7, h5]
  · refine ⟨(coxeterSystem Tag.E7).wordProd c.u, ?_, ?_⟩
    · unfold CoxeterSystem.wordProd
      refine Subgroup.list_prod_mem _ fun x hx => ?_
      obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
      exact Subgroup.subset_closure ⟨i, h6 i hi, rfl⟩
    · intro α hα
      rw [parabolicRoots_d4_eq7] at hα
      obtain ⟨l, hl, rfl⟩ := hα
      rw [← CoxeterSystem.wordProd_reverse, ← CoxeterSystem.wordProd_append,
        ← CoxeterSystem.wordProd_append, wordProd_smul_toVec7,
        permLattice_toVec_swap7, wordProd_smul_toVec7, h9 l hl]

end Cert

end CFSG.RankThree.PartOne.KE
