module

public import CFSG.RankThree.PartOne.KE.E8ClassLists
public import CFSG.RankThree.PartOne.KE.FourA1Group

public noncomputable section

namespace CFSG.RankThree.PartOne.KE

open Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley CFSG.RankThree.Lattice
open scoped Matrix

section Swap

@[expose] def e8perm2 (a b : Fin Tag.E8.rank) (l : List ℤ) : List ℤ :=
  List.ofFn fun k : Fin Tag.E8.rank => vget l ((Equiv.swap a b) k).val

theorem permLattice_toVec_swap (a b : Fin Tag.E8.rank) (l : List ℤ) :
    permLattice (Equiv.swap a b) (toVec Tag.E8.rank l) = toVec Tag.E8.rank (e8perm2 a b l) := by
  funext k
  simp only [permLattice, Function.comp_apply, Equiv.symm_swap]
  simp [toVec, vget, e8perm2]

structure D4SwapCert where
  cls : ℕ
  w : List (Fin Tag.E8.rank)
  u : List (Fin Tag.E8.rank)
  a : Fin Tag.E8.rank
  b : Fin Tag.E8.rank

@[expose] def D4SwapCert.Good (rows : List LineRow) (ww : List (Fin Tag.E8.rank))
    (c : D4SwapCert) : Prop :=
  (∀ l ∈ lineClassRoots rows c.cls, l ∈ e8D4RootList.map (lmulVec Tag.E8.rank (e8wl c.w))) ∧
  (∀ l ∈ e8D4RootList.map (lmulVec Tag.E8.rank (e8wl c.w)), l ∈ lineClassRoots rows c.cls) ∧
  (∀ x ∈ c.u, 1 ≤ x.val ∧ x.val ≤ 4) ∧ c.a ≠ c.b ∧
  (c.a.val = 1 ∨ c.a.val = 2 ∨ c.a.val = 4) ∧ (c.b.val = 1 ∨ c.b.val = 2 ∨ c.b.val = 4) ∧
  (∀ l ∈ e8D4RootList, lmulVec Tag.E8.rank (e8wl (c.w.reverse ++ ww ++ c.w)) l =
    lmulVec Tag.E8.rank (e8wl c.u) (e8perm2 c.a c.b l))

instance (rows : List LineRow) (ww : List (Fin Tag.E8.rank)) (c : D4SwapCert) :
    Decidable (c.Good rows ww) := by
  unfold D4SwapCert.Good
  infer_instance

theorem D4SwapCert.sound {rows : List LineRow}
    {ww : List (Fin Tag.E8.rank)} {c : D4SwapCert} (h : c.Good rows ww) :
    classSetL rows c.cls =
        (fun γ => (coxeterSystem Tag.E8).wordProd c.w • γ) ''
          parabolicRoots Tag.E8 (d4Nodes Tag.E8) ∧
      ∃ u ∈ parabolicWeylGroup Tag.E8 (d4Nodes Tag.E8),
        ∀ α ∈ parabolicRoots Tag.E8 (d4Nodes Tag.E8),
          (((coxeterSystem Tag.E8).wordProd c.w)⁻¹ * (coxeterSystem Tag.E8).wordProd ww *
            (coxeterSystem Tag.E8).wordProd c.w) • α =
            u • permLattice (Equiv.swap c.a c.b) α := by
  obtain ⟨h1, h2, h3, hab, -, -, h7⟩ := h
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
        permLattice_toVec_swap, wordProd_smul_toVec, h7 l hl]

end Swap

section FourA1

structure FourA1Cert where
  cls : ℕ
  r : List ℤ

@[expose] def FourA1Cert.r₂ (Wl : List (List ℤ)) (c : FourA1Cert) : List ℤ :=
  lmulVec Tag.E8.rank Wl c.r

@[expose] def FourA1Cert.r₃ (Wl : List (List ℤ)) (c : FourA1Cert) : List ℤ :=
  lmulVec Tag.E8.rank Wl (c.r₂ Wl)

@[expose] def FourA1Cert.r₄ (Wl : List (List ℤ)) (c : FourA1Cert) : List ℤ :=
  lmulVec Tag.E8.rank Wl (c.r₃ Wl)

@[expose] def FourA1Cert.roots (Wl : List (List ℤ)) (c : FourA1Cert) : List (List ℤ) :=
  [c.r, c.r₂ Wl, c.r₃ Wl, c.r₄ Wl, vneg Tag.E8.rank c.r, vneg Tag.E8.rank (c.r₂ Wl),
    vneg Tag.E8.rank (c.r₃ Wl), vneg Tag.E8.rank (c.r₄ Wl)]

@[expose] def FourA1Cert.Good (rows : List LineRow) (Wl : List (List ℤ)) (c : FourA1Cert) : Prop :=
  c.r ∈ Tag.E8.artifactRoots ∧ c.r₂ Wl ∈ Tag.E8.artifactRoots ∧
  c.r₃ Wl ∈ Tag.E8.artifactRoots ∧ c.r₄ Wl ∈ Tag.E8.artifactRoots ∧
  lmulVec Tag.E8.rank Wl (c.r₄ Wl) = vneg Tag.E8.rank c.r ∧
  toVec Tag.E8.rank c.r ⬝ᵥ (Tag.E8.symmetrizedCartan *ᵥ toVec Tag.E8.rank (c.r₂ Wl)) = 0 ∧
  toVec Tag.E8.rank c.r ⬝ᵥ (Tag.E8.symmetrizedCartan *ᵥ toVec Tag.E8.rank (c.r₃ Wl)) = 0 ∧
  toVec Tag.E8.rank c.r ⬝ᵥ (Tag.E8.symmetrizedCartan *ᵥ toVec Tag.E8.rank (c.r₄ Wl)) = 0 ∧
  toVec Tag.E8.rank (c.r₂ Wl) ⬝ᵥ (Tag.E8.symmetrizedCartan *ᵥ toVec Tag.E8.rank (c.r₃ Wl)) = 0 ∧
  toVec Tag.E8.rank (c.r₂ Wl) ⬝ᵥ (Tag.E8.symmetrizedCartan *ᵥ toVec Tag.E8.rank (c.r₄ Wl)) = 0 ∧
  toVec Tag.E8.rank (c.r₃ Wl) ⬝ᵥ (Tag.E8.symmetrizedCartan *ᵥ toVec Tag.E8.rank (c.r₄ Wl)) = 0 ∧
  (∀ l ∈ lineClassRoots rows c.cls, l ∈ c.roots Wl) ∧
  (∀ l ∈ c.roots Wl, l ∈ lineClassRoots rows c.cls)

instance (rows : List LineRow) (Wl : List (List ℤ)) (c : FourA1Cert) :
    Decidable (c.Good rows Wl) := by
  unfold FourA1Cert.Good
  infer_instance

theorem FourA1Cert.sound {rows : List LineRow} {Wl : List (List ℤ)} {c : FourA1Cert}
    {M : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) ℤ} (hM : M = toMat Tag.E8.rank Wl)
    (h : c.Good rows Wl) :
    ∃ r₁ r₂ r₃ r₄ : Fin Tag.E8.rank → ℤ,
      IsRoot Tag.E8 r₁ ∧ IsRoot Tag.E8 r₂ ∧ IsRoot Tag.E8 r₃ ∧ IsRoot Tag.E8 r₄ ∧
      M *ᵥ r₁ = r₂ ∧ M *ᵥ r₂ = r₃ ∧ M *ᵥ r₃ = r₄ ∧ M *ᵥ r₄ = -r₁ ∧
      r₁ ⬝ᵥ (Tag.E8.symmetrizedCartan *ᵥ r₂) = 0 ∧ r₁ ⬝ᵥ (Tag.E8.symmetrizedCartan *ᵥ r₃) = 0 ∧
      r₁ ⬝ᵥ (Tag.E8.symmetrizedCartan *ᵥ r₄) = 0 ∧ r₂ ⬝ᵥ (Tag.E8.symmetrizedCartan *ᵥ r₃) = 0 ∧
      r₂ ⬝ᵥ (Tag.E8.symmetrizedCartan *ᵥ r₄) = 0 ∧ r₃ ⬝ᵥ (Tag.E8.symmetrizedCartan *ᵥ r₄) = 0 ∧
      classSetL rows c.cls = fourRootSet r₁ r₂ r₃ r₄ := by
  obtain ⟨m1, m2, m3, m4, hneg, o12, o13, o14, o23, o24, o34, hc1, hc2⟩ := h
  have e2 : toVec Tag.E8.rank (c.r₂ Wl) = M *ᵥ toVec Tag.E8.rank c.r := by
    rw [FourA1Cert.r₂, toVec_lmulVec, hM]
  have e3 : toVec Tag.E8.rank (c.r₃ Wl) = M *ᵥ toVec Tag.E8.rank (c.r₂ Wl) := by
    rw [FourA1Cert.r₃, toVec_lmulVec, hM]
  have e4 : toVec Tag.E8.rank (c.r₄ Wl) = M *ᵥ toVec Tag.E8.rank (c.r₃ Wl) := by
    rw [FourA1Cert.r₄, toVec_lmulVec, hM]
  have e5 : M *ᵥ toVec Tag.E8.rank (c.r₄ Wl) = -toVec Tag.E8.rank c.r := by
    rw [hM, ← toVec_lmulVec, hneg, toVec_vneg]
  refine ⟨toVec Tag.E8.rank c.r, toVec Tag.E8.rank (c.r₂ Wl), toVec Tag.E8.rank (c.r₃ Wl),
    toVec Tag.E8.rank (c.r₄ Wl), isRoot_toVec m1, isRoot_toVec m2, isRoot_toVec m3,
    isRoot_toVec m4, e2.symm, e3.symm, e4.symm, e5, o12, o13, o14, o23, o24, o34, ?_⟩
  rw [classSetL, setOfList_eq hc1 hc2]
  ext α
  simp only [FourA1Cert.roots, fourRootSet, Set.mem_insert_iff, Set.mem_singleton_iff,
    List.mem_cons, List.not_mem_nil, or_false, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨l, hl, rfl⟩
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
    · exact Or.inr (Or.inl (by rw [toVec_vneg]))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (by rw [toVec_vneg]))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by rw [toVec_vneg]))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by rw [toVec_vneg])))))))
  · rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    · exact ⟨c.r, Or.inl rfl, rfl⟩
    · exact ⟨vneg Tag.E8.rank c.r, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))),
        by rw [toVec_vneg]⟩
    · exact ⟨c.r₂ Wl, Or.inr (Or.inl rfl), rfl⟩
    · exact ⟨vneg Tag.E8.rank (c.r₂ Wl), Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))),
        by rw [toVec_vneg]⟩
    · exact ⟨c.r₃ Wl, Or.inr (Or.inr (Or.inl rfl)), rfl⟩
    · exact ⟨vneg Tag.E8.rank (c.r₃ Wl),
        Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))), by rw [toVec_vneg]⟩
    · exact ⟨c.r₄ Wl, Or.inr (Or.inr (Or.inr (Or.inl rfl))), rfl⟩
    · exact ⟨vneg Tag.E8.rank (c.r₄ Wl),
        Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))), by rw [toVec_vneg]⟩

end FourA1

end CFSG.RankThree.PartOne.KE
