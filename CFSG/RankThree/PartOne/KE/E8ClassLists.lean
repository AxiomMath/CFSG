module

public import CFSG.RankThree.PartOne.KE.Rank2Lines
public import CFSG.RankThree.PartOne.KE.D4TranspositionInterface
public import CFSG.RankThree.PartOne.KE.E8A2Sigma

public noncomputable section

namespace CFSG.RankThree.PartOne.KE

open Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley CFSG.RankThree.Lattice
open scoped Matrix

section Lists

@[expose] def e8wl (w : List (Fin Tag.E8.rank)) : List (List ℤ) :=
  lword Tag.E8.rank (cartanList Tag.E8) (w.map Fin.val)

theorem wordMat_e8wl (w : List (Fin Tag.E8.rank)) :
    wordMat Tag.E8 w = toMat Tag.E8.rank (e8wl w) :=
  wordMat_eq_toMat Tag.E8 w rfl

theorem wordProd_smul_toVec
    (w : List (Fin Tag.E8.rank)) (l : List ℤ) :
    (coxeterSystem Tag.E8).wordProd w • toVec Tag.E8.rank l =
      toVec Tag.E8.rank (lmulVec Tag.E8.rank (e8wl w) l) := by
  rw [wordProd_smul_eq_wordMat_mulVec, wordMat_e8wl, toVec_lmulVec]

@[expose] def e8bList : Fin 3 → List ℤ :=
  ![[1, 0, 1, 1, 0, 0, 0, 0], [0, 0, 1, 1, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0]]

theorem e8a2Weight_eq (i : Fin 3) : e8a2Weight i = toVec Tag.E8.rank (e8bList i) := by
  fin_cases i <;> (funext k; fin_cases k <;> rfl)

@[expose] def e8rootL (W : List (List ℤ)) (i j : Fin 3) : List ℤ :=
  lmulVec Tag.E8.rank W (vadd Tag.E8.rank (e8bList i) (vneg Tag.E8.rank (e8bList j)))

theorem sigmaRootE8_wordProd (w : List (Fin Tag.E8.rank)) (i j : Fin 3) :
    sigmaRootE8 ((coxeterSystem Tag.E8).wordProd w) i j =
      toVec Tag.E8.rank (e8rootL (e8wl w) i j) := by
  rw [e8rootL, toVec_lmulVec, toVec_vadd, toVec_vneg, Matrix.mulVec_add, Matrix.mulVec_neg,
    ← wordMat_e8wl, ← e8a2Weight_eq, ← e8a2Weight_eq, sigmaRootE8, wbE8, wbE8,
    wordProd_smul_eq_wordMat_mulVec, wordProd_smul_eq_wordMat_mulVec, sub_eq_add_neg]

@[expose] def e8a2L (W : List (List ℤ)) : List (List ℤ) :=
  [e8rootL W 0 1, e8rootL W 0 2, e8rootL W 1 0, e8rootL W 1 2, e8rootL W 2 0, e8rootL W 2 1]

theorem mem_e8a2L_iff {W : List (List ℤ)} {l : List ℤ} :
    l ∈ e8a2L W ↔ ∃ i j : Fin 3, i ≠ j ∧ l = e8rootL W i j := by
  constructor
  · intro h
    simp only [e8a2L, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨0, 1, by decide, rfl⟩
    · exact ⟨0, 2, by decide, rfl⟩
    · exact ⟨1, 0, by decide, rfl⟩
    · exact ⟨1, 2, by decide, rfl⟩
    · exact ⟨2, 0, by decide, rfl⟩
    · exact ⟨2, 1, by decide, rfl⟩
  · rintro ⟨i, j, hij, rfl⟩
    fin_cases i <;> fin_cases j <;> simp_all [e8a2L]

theorem sigmaSetE8_wordProd_eq (w : List (Fin Tag.E8.rank)) :
    sigmaSetE8 ((coxeterSystem Tag.E8).wordProd w) =
      {α | ∃ l ∈ e8a2L (e8wl w), α = toVec Tag.E8.rank l} := by
  rw [sigmaSetE8_eq]
  ext α
  simp only [Set.mem_ofPred_eq, mem_e8a2L_iff, sigmaRootE8_wordProd]
  constructor
  · rintro ⟨i, j, hij, rfl⟩
    exact ⟨_, ⟨i, j, hij, rfl⟩, rfl⟩
  · rintro ⟨l, ⟨i, j, hij, rfl⟩, rfl⟩
    exact ⟨i, j, hij, rfl⟩

@[expose] def classSetL (rows : List LineRow) (j : ℕ) : Set (Fin Tag.E8.rank → ℤ) :=
  {α | ∃ l ∈ lineClassRoots rows j, α = toVec Tag.E8.rank l}

theorem setOfList_eq {A B : List (List ℤ)} (h1 : ∀ l ∈ A, l ∈ B) (h2 : ∀ l ∈ B, l ∈ A) :
    {α : Fin Tag.E8.rank → ℤ | ∃ l ∈ A, α = toVec Tag.E8.rank l} =
      {α | ∃ l ∈ B, α = toVec Tag.E8.rank l} := by
  ext α
  constructor
  · rintro ⟨l, hl, rfl⟩
    exact ⟨l, h1 l hl, rfl⟩
  · rintro ⟨l, hl, rfl⟩
    exact ⟨l, h2 l hl, rfl⟩

@[expose] def e8unit (i : ℕ) : List ℤ := List.ofFn fun k : Fin Tag.E8.rank => if k.val = i then 1 else 0

@[expose] def e8D4RootList : List (List ℤ) := [
    [0, -1, -1, -2, -1, 0, 0, 0], [0, -1, -1, -1, -1, 0, 0, 0], [0, -1, -1, -1, 0, 0, 0, 0],
    [0, -1, 0, -1, -1, 0, 0, 0], [0, -1, 0, -1, 0, 0, 0, 0], [0, -1, 0, 0, 0, 0, 0, 0],
    [0, 0, -1, -1, -1, 0, 0, 0], [0, 0, -1, -1, 0, 0, 0, 0], [0, 0, -1, 0, 0, 0, 0, 0],
    [0, 0, 0, -1, -1, 0, 0, 0], [0, 0, 0, -1, 0, 0, 0, 0], [0, 0, 0, 0, -1, 0, 0, 0],
    [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 1, 1, 0, 0, 0],
    [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 1, 1, 0, 0, 0, 0], [0, 0, 1, 1, 1, 0, 0, 0],
    [0, 1, 0, 0, 0, 0, 0, 0], [0, 1, 0, 1, 0, 0, 0, 0], [0, 1, 0, 1, 1, 0, 0, 0],
    [0, 1, 1, 1, 0, 0, 0, 0], [0, 1, 1, 1, 1, 0, 0, 0], [0, 1, 1, 2, 1, 0, 0, 0]]


@[expose] def e8perm3 (a b c : Fin Tag.E8.rank) (l : List ℤ) : List ℤ :=
  List.ofFn fun k : Fin Tag.E8.rank =>
    vget l (if k = b then a else if k = c then b else if k = a then c else k).val

theorem formPerm_three_symm : ∀ a b c k : Fin Tag.E8.rank, a ≠ b → b ≠ c → a ≠ c →
    (List.formPerm [a, b, c]).symm k =
      if k = b then a else if k = c then b else if k = a then c else k := by
  decide +kernel

theorem permLattice_toVec_three {a b c : Fin Tag.E8.rank} (hab : a ≠ b) (hbc : b ≠ c)
    (hac : a ≠ c) (l : List ℤ) :
    permLattice (List.formPerm [a, b, c]) (toVec Tag.E8.rank l) =
      toVec Tag.E8.rank (e8perm3 a b c l) := by
  funext k
  simp only [permLattice, Function.comp_apply]
  rw [formPerm_three_symm a b c k hab hbc hac]
  simp [toVec, vget, e8perm3]

theorem e8D4_complete : ∀ l ∈ Tag.E8.artifactRoots,
    (∀ k : Fin Tag.E8.rank, ¬ (1 ≤ k.val ∧ k.val ≤ 4) → vget l k.val = 0) →
      l ∈ e8D4RootList := by
  decide +kernel

theorem e8D4_sound : ∀ l ∈ e8D4RootList,
    l ∈ Tag.E8.artifactRoots ∧
      ∀ k : Fin Tag.E8.rank, ¬ (1 ≤ k.val ∧ k.val ≤ 4) → vget l k.val = 0 := by
  decide +kernel

theorem parabolicRoots_d4_eq :
    parabolicRoots Tag.E8 (d4Nodes Tag.E8) =
      {α | ∃ l ∈ e8D4RootList, α = toVec Tag.E8.rank l} := by
  ext α
  constructor
  · rintro ⟨hα, hsupp⟩
    obtain ⟨l, hl, rfl⟩ := isRoot_iff_exists_mem.1 hα
    refine ⟨l, e8D4_complete l hl (fun k hk => ?_), rfl⟩
    exact hsupp k hk
  · rintro ⟨l, hl, rfl⟩
    obtain ⟨hl', hs⟩ := e8D4_sound l hl
    exact ⟨isRoot_toVec hl', fun k hk => hs k hk⟩

structure D4Cert where
  cls : ℕ
  w : List (Fin Tag.E8.rank)
  u : List (Fin Tag.E8.rank)
  a : Fin Tag.E8.rank
  b : Fin Tag.E8.rank
  c : Fin Tag.E8.rank

@[expose] def D4Cert.Good (rows : List LineRow) (ww : List (Fin Tag.E8.rank)) (c : D4Cert) :
    Prop :=
  (∀ l ∈ lineClassRoots rows c.cls, l ∈ e8D4RootList.map (lmulVec Tag.E8.rank (e8wl c.w))) ∧
  (∀ l ∈ e8D4RootList.map (lmulVec Tag.E8.rank (e8wl c.w)), l ∈ lineClassRoots rows c.cls) ∧
  (∀ x ∈ c.u, 1 ≤ x.val ∧ x.val ≤ 4) ∧ c.a ≠ c.b ∧ c.b ≠ c.c ∧ c.a ≠ c.c ∧
  (c.a.val = 1 ∨ c.a.val = 2 ∨ c.a.val = 4) ∧ (c.b.val = 1 ∨ c.b.val = 2 ∨ c.b.val = 4) ∧
  (c.c.val = 1 ∨ c.c.val = 2 ∨ c.c.val = 4) ∧
  (∀ l ∈ e8D4RootList, lmulVec Tag.E8.rank (e8wl (c.w.reverse ++ ww ++ c.w)) l =
    lmulVec Tag.E8.rank (e8wl c.u) (e8perm3 c.a c.b c.c l))

instance (rows : List LineRow) (ww : List (Fin Tag.E8.rank)) (c : D4Cert) :
    Decidable (c.Good rows ww) := by
  unfold D4Cert.Good
  infer_instance

theorem D4Cert.sound {rows : List LineRow}
    {ww : List (Fin Tag.E8.rank)} {c : D4Cert} (h : c.Good rows ww) :
    classSetL rows c.cls =
        (fun γ => (coxeterSystem Tag.E8).wordProd c.w • γ) ''
          parabolicRoots Tag.E8 (d4Nodes Tag.E8) ∧
      ∃ u ∈ parabolicWeylGroup Tag.E8 (d4Nodes Tag.E8),
        ∀ α ∈ parabolicRoots Tag.E8 (d4Nodes Tag.E8),
          (((coxeterSystem Tag.E8).wordProd c.w)⁻¹ * (coxeterSystem Tag.E8).wordProd ww *
            (coxeterSystem Tag.E8).wordProd c.w) • α =
            u • permLattice (List.formPerm [c.a, c.b, c.c]) α := by
  obtain ⟨h1, h2, h3, hab, hbc, hac, -, -, -, h9⟩ := h
  refine ⟨?_, ?_⟩
  · rw [classSetL, setOfList_eq h1 h2, parabolicRoots_d4_eq]
    ext β
    constructor
    · rintro ⟨l, hl, rfl⟩
      obtain ⟨l', hl', rfl⟩ := List.mem_map.1 hl
      exact ⟨toVec _ l', ⟨l', hl', rfl⟩, wordProd_smul_toVec c.w l'⟩
    · rintro ⟨α, ⟨l, hl, rfl⟩, rfl⟩
      exact ⟨_, List.mem_map.2 ⟨l, hl, rfl⟩, wordProd_smul_toVec c.w l⟩
  · refine ⟨(coxeterSystem Tag.E8).wordProd c.u, ?_, ?_⟩
    · unfold CoxeterSystem.wordProd
      refine Subgroup.list_prod_mem _ fun x hx => ?_
      obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
      exact Subgroup.subset_closure ⟨i, h3 i hi, rfl⟩
    · intro α hα
      rw [parabolicRoots_d4_eq] at hα
      obtain ⟨l, hl, rfl⟩ := hα
      rw [← CoxeterSystem.wordProd_reverse, ← CoxeterSystem.wordProd_append,
        ← CoxeterSystem.wordProd_append, wordProd_smul_toVec,
        permLattice_toVec_three hab hbc hac, wordProd_smul_toVec, h9 l hl]

structure TwoA2Cert where
  cls : ℕ
  w₁ : List (Fin Tag.E8.rank)
  w₂ : List (Fin Tag.E8.rank)
  π₁ : Fin 3 → Fin 3
  π₂ : Fin 3 → Fin 3

@[expose] def TwoA2Cert.Good (rows : List LineRow) (Wl : List (List ℤ)) (c : TwoA2Cert) : Prop :=
  (∀ l ∈ lineClassRoots rows c.cls, l ∈ e8a2L (e8wl c.w₁) ++ e8a2L (e8wl c.w₂)) ∧
  (∀ l ∈ e8a2L (e8wl c.w₁) ++ e8a2L (e8wl c.w₂), l ∈ lineClassRoots rows c.cls) ∧
  (∀ i j : Fin 3, i ≠ j →
    lmulVec Tag.E8.rank Wl (e8rootL (e8wl c.w₁) i j) ∈ e8a2L (e8wl c.w₂)) ∧
  (∀ i j : Fin 3, i ≠ j →
    lmulVec Tag.E8.rank Wl (e8rootL (e8wl c.w₂) i j) ∈ e8a2L (e8wl c.w₁)) ∧
  Function.Injective c.π₁ ∧ Function.Injective c.π₂ ∧
  (∀ i j : Fin 3, i ≠ j → lmulVec Tag.E8.rank (lmul Tag.E8.rank Wl Wl) (e8rootL (e8wl c.w₁) i j) =
    e8rootL (e8wl c.w₁) (c.π₁ j) (c.π₁ i)) ∧
  (∀ i j : Fin 3, i ≠ j → lmulVec Tag.E8.rank (lmul Tag.E8.rank Wl Wl) (e8rootL (e8wl c.w₂) i j) =
    e8rootL (e8wl c.w₂) (c.π₂ j) (c.π₂ i)) ∧
  (∀ i j i' j' : Fin 3, i ≠ j → i' ≠ j' →
    toVec Tag.E8.rank (e8rootL (e8wl c.w₁) i j) ⬝ᵥ
      (Tag.E8.symmetrizedCartan *ᵥ toVec Tag.E8.rank (e8rootL (e8wl c.w₂) i' j')) = 0)

instance (rows : List LineRow) (Wl : List (List ℤ)) (c : TwoA2Cert) :
    Decidable (c.Good rows Wl) := by
  unfold TwoA2Cert.Good
  infer_instance

theorem TwoA2Cert.sound {rows : List LineRow} {Wl : List (List ℤ)} {c : TwoA2Cert}
    {M : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) ℤ} (hM : M = toMat Tag.E8.rank Wl)
    (h : c.Good rows Wl) :
    classSetL rows c.cls =
        sigmaSetE8 ((coxeterSystem Tag.E8).wordProd c.w₁) ∪
          sigmaSetE8 ((coxeterSystem Tag.E8).wordProd c.w₂) ∧
      (∀ i j : Fin 3, i ≠ j → ∃ i' j' : Fin 3, i' ≠ j' ∧
        M *ᵥ sigmaRootE8 ((coxeterSystem Tag.E8).wordProd c.w₁) i j =
          sigmaRootE8 ((coxeterSystem Tag.E8).wordProd c.w₂) i' j') ∧
      (∀ i j : Fin 3, i ≠ j → ∃ i' j' : Fin 3, i' ≠ j' ∧
        M *ᵥ sigmaRootE8 ((coxeterSystem Tag.E8).wordProd c.w₂) i j =
          sigmaRootE8 ((coxeterSystem Tag.E8).wordProd c.w₁) i' j') ∧
      (∃ π : Equiv.Perm (Fin 3), ∀ i j : Fin 3, i ≠ j →
        (M * M) *ᵥ sigmaRootE8 ((coxeterSystem Tag.E8).wordProd c.w₁) i j =
          sigmaRootE8 ((coxeterSystem Tag.E8).wordProd c.w₁) (π j) (π i)) ∧
      (∃ π : Equiv.Perm (Fin 3), ∀ i j : Fin 3, i ≠ j →
        (M * M) *ᵥ sigmaRootE8 ((coxeterSystem Tag.E8).wordProd c.w₂) i j =
          sigmaRootE8 ((coxeterSystem Tag.E8).wordProd c.w₂) (π j) (π i)) ∧
      (∀ α ∈ sigmaSetE8 ((coxeterSystem Tag.E8).wordProd c.w₁),
        ∀ β ∈ sigmaSetE8 ((coxeterSystem Tag.E8).wordProd c.w₂),
          α ⬝ᵥ (Tag.E8.symmetrizedCartan *ᵥ β) = 0) := by
  obtain ⟨h1, h2, h3, h4, hi₁, hi₂, h7, h8, h9⟩ := h
  have hexch : ∀ (w w' : List (Fin Tag.E8.rank)),
      (∀ i j : Fin 3, i ≠ j → lmulVec Tag.E8.rank Wl (e8rootL (e8wl w) i j) ∈ e8a2L (e8wl w')) →
      ∀ i j : Fin 3, i ≠ j → ∃ i' j' : Fin 3, i' ≠ j' ∧
        M *ᵥ sigmaRootE8 ((coxeterSystem Tag.E8).wordProd w) i j =
          sigmaRootE8 ((coxeterSystem Tag.E8).wordProd w') i' j' := by
    intro w w' hw i j hij
    obtain ⟨i', j', hij', he⟩ := mem_e8a2L_iff.1 (hw i j hij)
    refine ⟨i', j', hij', ?_⟩
    rw [sigmaRootE8_wordProd, sigmaRootE8_wordProd, hM, ← toVec_lmulVec, he]
  have hperm : ∀ (w : List (Fin Tag.E8.rank)) (π : Fin 3 → Fin 3), Function.Injective π →
      (∀ i j : Fin 3, i ≠ j → lmulVec Tag.E8.rank (lmul Tag.E8.rank Wl Wl) (e8rootL (e8wl w) i j) =
        e8rootL (e8wl w) (π j) (π i)) →
      ∃ π' : Equiv.Perm (Fin 3), ∀ i j : Fin 3, i ≠ j →
        (M * M) *ᵥ sigmaRootE8 ((coxeterSystem Tag.E8).wordProd w) i j =
          sigmaRootE8 ((coxeterSystem Tag.E8).wordProd w) (π' j) (π' i) := by
    intro w π hπ hw
    refine ⟨Equiv.ofBijective π (Finite.injective_iff_bijective.1 hπ), fun i j hij => ?_⟩
    rw [sigmaRootE8_wordProd, sigmaRootE8_wordProd, hM, ← toMat_lmul, ← toVec_lmulVec, hw i j hij]
    rfl
  refine ⟨?_, hexch c.w₁ c.w₂ h3, hexch c.w₂ c.w₁ h4, hperm c.w₁ c.π₁ hi₁ h7,
    hperm c.w₂ c.π₂ hi₂ h8, ?_⟩
  · rw [classSetL, setOfList_eq h1 h2, sigmaSetE8_wordProd_eq, sigmaSetE8_wordProd_eq]
    ext α
    simp only [Set.mem_union, Set.mem_ofPred_eq, List.mem_append]
    constructor
    · rintro ⟨l, hl | hl, rfl⟩
      · exact Or.inl ⟨l, hl, rfl⟩
      · exact Or.inr ⟨l, hl, rfl⟩
    · rintro (⟨l, hl, rfl⟩ | ⟨l, hl, rfl⟩)
      · exact ⟨l, Or.inl hl, rfl⟩
      · exact ⟨l, Or.inr hl, rfl⟩
  · intro α hα β hβ
    rw [sigmaSetE8_eq] at hα hβ
    obtain ⟨i, j, hij, rfl⟩ := hα
    obtain ⟨i', j', hij', rfl⟩ := hβ
    rw [sigmaRootE8_wordProd, sigmaRootE8_wordProd]
    exact h9 i j i' j' hij hij'

end Lists

end CFSG.RankThree.PartOne.KE
