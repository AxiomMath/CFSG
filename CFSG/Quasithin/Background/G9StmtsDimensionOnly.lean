module

public import CFSG.Quasithin.Background.G9Stmts

public section

namespace CFSG.Quasithin

namespace G11

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

@[expose] def G93ConclDimensionOnly (Γ H : Subgroup (GLV V)) (m : ℕ) : Prop :=
  G93Case0 H m ∨ G93Case1DimensionOnly H m ∨ G93Case2 Γ H m ∨ G93Case3 Γ H m ∨ G93Case4 H m ∨
    G93Case5 H m ∨ G93Case6 H m ∨ G93Case7 H m ∨ G93Case8 H m ∨ G93Case9 H m ∨
    G93Case10 H m ∨ G93Case11 Γ H m ∨ G93Case12 H m ∨ G93Case13 Γ H m ∨ G93Case14 H m ∨
    G93Case15 H m ∨ G93Case16 H m ∨ G93Case17 H m

theorem G93Concl.toDimensionOnly {Γ H : Subgroup (GLV V)} {m : ℕ} (h : G93Concl Γ H m) :
    G93ConclDimensionOnly Γ H m :=
  Or.imp id (Or.imp G93Case1.toDimensionOnly id) h

@[expose] def G93StmtDimensionOnly : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (Γ A L H : Subgroup (GLV V)) (m : ℕ), G93Hyp Γ A L H m → G93ConclDimensionOnly Γ H m

theorem G93ConclDimensionOnly.of_selfDual {Γ H : Subgroup (GLV V)} {m : ℕ}
    (h : G93ConclDimensionOnly Γ H m) (hs : SelfDual H ⊤) : G93SelfDualCases Γ H m := by
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact Or.inl h
  · exact absurd hs h.2.2
  · exact Or.inr (Or.inl h)
  · exact absurd hs h.2.2
  · exact Or.inr (Or.inr (Or.inl h))
  · exact absurd hs h.2.2
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · obtain ⟨_, _, _, hd⟩ := h
    exact absurd hs hd
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
  · exact absurd hs h.2.2
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))
  · exact absurd hs h.2.2
  · exact absurd hs h.2.2
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))
  · obtain ⟨_, _, _, hd⟩ := h
    exact absurd hs hd

theorem G93ConclDimensionOnly.of_not_selfDual {Γ H : Subgroup (GLV V)} {m : ℕ}
    (h : G93ConclDimensionOnly Γ H m) (hs : ¬ SelfDual H ⊤) :
    G93Case1DimensionOnly H m ∨ G93Case3 Γ H m ∨ G93Case5 H m ∨ G93Case8 H m ∨
      G93Case11 Γ H m ∨ G93Case13 Γ H m ∨ G93Case14 H m ∨ G93Case17 H m := by
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact absurd h.2.2 hs
  · exact Or.inl h
  · exact absurd h.2.2 hs
  · exact Or.inr (Or.inl h)
  · exact absurd h.2.2 hs
  · exact Or.inr (Or.inr (Or.inl h))
  · obtain ⟨_, _, _, hd⟩ := h
    exact absurd hd hs
  · obtain ⟨_, _, _, hd⟩ := h
    exact absurd hd hs
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · obtain ⟨_, _, _, hd⟩ := h
    exact absurd hd hs
  · obtain ⟨_, _, _, hd⟩ := h
    exact absurd hd hs
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact absurd h.2.2 hs
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
  · obtain ⟨_, _, _, hd⟩ := h
    exact absurd hd hs
  · exact absurd h.2.2 hs
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))

end G11

end CFSG.Quasithin
