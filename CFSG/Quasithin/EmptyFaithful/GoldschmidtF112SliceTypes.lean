module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Defs
public import CFSG.Quasithin.Background.F1Models

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

variable {G : Type} [Group G]

@[expose] def VS3 (L : Subgroup G) : Prop :=
  Nonempty (oTwoQuot ↥L ≃* Equiv.Perm (Fin 3))

@[expose] def VFD (L : Subgroup G) : Prop :=
  Nonempty (oTwoQuot ↥L ≃* DihedralGroup 5) ∨ Nonempty (oTwoQuot ↥L ≃* ↥(Sz 0))

@[expose] def VU3two (L : Subgroup G) : Prop :=
  ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ 2 ∧
    (Nonempty (oTwoQuot ↥L ≃* StatedSU 3 2 F) ∨
      Nonempty (oTwoQuot ↥L ≃* StatedProj (StatedSU 3 2 F)))

@[expose] def VBig (L : Subgroup G) : Prop :=
  ¬ (VS3 L ∨ VFD L ∨ VU3two L)

theorem f112_vertex_types (L : Subgroup G) : VS3 L ∨ VFD L ∨ VU3two L ∨ VBig L := by
  by_cases h : VS3 L ∨ VFD L ∨ VU3two L
  · rcases h with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr h))

@[expose] def PairSS (L1 L2 : Subgroup G) : Prop :=
  VS3 L1 ∧ VS3 L2

@[expose] def PairTits (L1 L2 : Subgroup G) : Prop :=
  (VFD L1 ∧ VS3 L2) ∨ (VS3 L1 ∧ VFD L2)

@[expose] def PairS3Big (L1 L2 : Subgroup G) : Prop :=
  (VS3 L1 ∧ VBig L2) ∨ (VBig L1 ∧ VS3 L2)

@[expose] def PairFDBig (L1 L2 : Subgroup G) : Prop :=
  (VFD L1 ∧ VBig L2) ∨ (VBig L1 ∧ VFD L2)

@[expose] def PairBig (L1 L2 : Subgroup G) : Prop :=
  VBig L1 ∧ VBig L2

@[expose] def PairExotic (L1 L2 : Subgroup G) : Prop :=
  VU3two L1 ∨ VU3two L2 ∨ (VFD L1 ∧ VFD L2)

theorem PairSS.symm {L1 L2 : Subgroup G} (h : PairSS L1 L2) : PairSS L2 L1 :=
  ⟨h.2, h.1⟩

theorem PairTits.symm {L1 L2 : Subgroup G} (h : PairTits L1 L2) : PairTits L2 L1 := by
  rcases h with ⟨a, b⟩ | ⟨a, b⟩
  · exact Or.inr ⟨b, a⟩
  · exact Or.inl ⟨b, a⟩

theorem PairS3Big.symm {L1 L2 : Subgroup G} (h : PairS3Big L1 L2) : PairS3Big L2 L1 := by
  rcases h with ⟨a, b⟩ | ⟨a, b⟩
  · exact Or.inr ⟨b, a⟩
  · exact Or.inl ⟨b, a⟩

theorem PairFDBig.symm {L1 L2 : Subgroup G} (h : PairFDBig L1 L2) : PairFDBig L2 L1 := by
  rcases h with ⟨a, b⟩ | ⟨a, b⟩
  · exact Or.inr ⟨b, a⟩
  · exact Or.inl ⟨b, a⟩

theorem PairBig.symm {L1 L2 : Subgroup G} (h : PairBig L1 L2) : PairBig L2 L1 :=
  ⟨h.2, h.1⟩

theorem PairExotic.symm {L1 L2 : Subgroup G} (h : PairExotic L1 L2) : PairExotic L2 L1 := by
  rcases h with h | h | h
  · exact Or.inr (Or.inl h)
  · exact Or.inl h
  · exact Or.inr (Or.inr ⟨h.2, h.1⟩)

theorem f112_pair_cases (L1 L2 : Subgroup G) :
    PairSS L1 L2 ∨ PairTits L1 L2 ∨ PairS3Big L1 L2 ∨ PairFDBig L1 L2 ∨ PairBig L1 L2 ∨
      PairExotic L1 L2 := by
  rcases f112_vertex_types L1 with h1 | h1 | h1 | h1 <;>
    rcases f112_vertex_types L2 with h2 | h2 | h2 | h2
  · exact Or.inl ⟨h1, h2⟩
  · exact Or.inr (Or.inl (Or.inr ⟨h1, h2⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h2))))))
  · exact Or.inr (Or.inr (Or.inl (Or.inl ⟨h1, h2⟩)))
  · exact Or.inr (Or.inl (Or.inl ⟨h1, h2⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h1, h2⟩))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h2))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inl ⟨h1, h2⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h1)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h1)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h1)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h1)))))
  · exact Or.inr (Or.inr (Or.inl (Or.inr ⟨h1, h2⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inr ⟨h1, h2⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h2))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, h2⟩))))

end CFSG.Quasithin
