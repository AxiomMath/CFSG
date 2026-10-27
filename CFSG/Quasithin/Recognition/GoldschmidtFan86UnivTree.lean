module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86UnivLoc
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Setting

public section

namespace CFSG.Quasithin.Fan86

open CFSG.Quasithin Univ

variable {A C B : Type} [Group A] [Group C] [Group B] {X : GoldAmalgam A C B}

namespace Univ

theorem locTrans_all (X : GoldAmalgam A C B) (v : Vtx X) : LocTrans X.treeGraph X.Universal v := by
  rcases exists_smul_base X v with ⟨g, rfl⟩ | ⟨g, rfl⟩
  · exact (locTrans_baseA X).smul (adj_smul X) g
  · exact (locTrans_baseB X).smul (adj_smul X) g

theorem frobTwo_all (h : Hyp53 X) (v : Vtx X) : FrobTwo X.treeGraph X.Universal v := by
  rcases exists_smul_base X v with ⟨g, rfl⟩ | ⟨g, rfl⟩
  · exact (frobTwo_baseA h).smul (adj_smul X) g
  · exact (frobTwo_baseB h).smul (adj_smul X) g

theorem frobNonreg_all (h : Hyp53 X) (v : Vtx X) : FrobNonreg X.treeGraph X.Universal v := by
  rcases exists_smul_base X v with ⟨g, rfl⟩ | ⟨g, rfl⟩
  · exact (frobNonreg_baseA h).smul (adj_smul X) g
  · exact (frobNonreg_baseB h).smul (adj_smul X) g

theorem card_neighborSet_inl (h : Hyp53 X) (q : X.Universal ⧸ X.ofA.range) :
    Nat.card (X.treeGraph.neighborSet (Sum.inl q)) = 5 := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  rw [Nat.card_coe_set_eq, ncard_neighborSet_inl, h.index_left]

theorem card_neighborSet_inr (h : Hyp53 X) (q : X.Universal ⧸ X.ofB.range) :
    Nat.card (X.treeGraph.neighborSet (Sum.inr q)) = 3 := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  rw [Nat.card_coe_set_eq, ncard_neighborSet_inr, h.index_right]

theorem not_adj_inl_inl (x y : X.Universal ⧸ X.ofA.range) :
    ¬ X.treeGraph.Adj (Sum.inl x) (Sum.inl y) := by
  simp [GoldAmalgam.treeGraph, goldCosetGraph, SimpleGraph.fromRel_adj, goldCosetRel]

theorem not_adj_inr_inr (x y : X.Universal ⧸ X.ofB.range) :
    ¬ X.treeGraph.Adj (Sum.inr x) (Sum.inr y) := by
  simp [GoldAmalgam.treeGraph, goldCosetGraph, SimpleGraph.fromRel_adj, goldCosetRel]

end Univ

theorem fanTree_of_hyp53 (h : Hyp53 X) : FanTree X.treeGraph X.Universal where
  isTree := X.treeGraph_isTree
  adj_smul := Univ.adj_smul X
  faithful := fun g hg => by
    have hf := (X.universalCompletion.isFaithful_iff_ker_inf_ker_eq_bot).1 h.faithful
    have hmem : g ∈ (MulAction.toPermHom X.Universal
          (X.Universal ⧸ X.universalCompletion.ψA.range)).ker ⊓
        (MulAction.toPermHom X.Universal (X.Universal ⧸ X.universalCompletion.ψB.range)).ker :=
      ⟨MonoidHom.mem_ker.2 (Equiv.ext fun q => Sum.inl_injective (hg (Sum.inl q))),
        MonoidHom.mem_ker.2 (Equiv.ext fun q => Sum.inr_injective (hg (Sum.inr q)))⟩
    rw [hf] at hmem
    exact Subgroup.mem_bot.1 hmem
  loc_finite := fun v => by
    have := h.finite_left
    have := h.finite_right
    exact Univ.finite_stabilizer X v
  loc_trans := fun v => Univ.locTrans_all X v
  valence := fun v => by
    rcases v with q | q
    · exact Or.inr (Univ.card_neighborSet_inl h q)
    · exact Or.inl (Univ.card_neighborSet_inr h q)
  alternating := fun u v huv => by
    rcases u with x | x <;> rcases v with y | y
    · exact absurd huv (Univ.not_adj_inl_inl x y)
    · rw [Univ.card_neighborSet_inl h x, Univ.card_neighborSet_inr h y]
      decide
    · rw [Univ.card_neighborSet_inr h x, Univ.card_neighborSet_inl h y]
      decide
    · exact absurd huv (Univ.not_adj_inr_inr x y)
  frobenius_two := fun v => Univ.frobTwo_all h v
  frobenius_nonreg := fun v => Univ.frobNonreg_all h v
  edge_two := fun u v huv => Univ.isPGroup_stabilizer_inf X h.pgroup huv
  charTwo := fun v => Univ.charTwo_stabilizer X h.charTwo_left h.charTwo_right v

end CFSG.Quasithin.Fan86
