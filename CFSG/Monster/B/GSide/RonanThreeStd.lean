module

public import CFSG.Monster.B.E6.StdF4PairCount
public import CFSG.Monster.B.E6.StdF4RadicalGroup

public noncomputable section

namespace CFSG.Monster.B.GSide

open CFSG.Monster.B.E6.StdF4 CFSG.Monster.B.E6.StdF4Radical CFSG.LieType.Chevalley.C2E6Std
  CFSG.LieType.Chevalley.C2E6Std.FieldExtension

@[expose] def nonFixedRoots :
    Set Pts := {x | betaG (x : stdGroup) ≠ x}

@[expose] def nonFixedGraph :
    SimpleGraph nonFixedRoots :=
  SimpleGraph.fromRel fun p q => Commute ((p : Pts) : stdGroup) ((q : Pts) : stdGroup)

abbrev IsNbr
    (x y : Pts) : Prop := relIdx x y = 1 ∨ relIdx x y = 2

theorem isNbr_iff
    (x y : Pts) : IsNbr x y ↔ x ≠ y ∧ Commute (x : stdGroup) y := by
  rw [commute_iff_relPt_lt x.2 y.2, ← val_relIdx, ne_eq, ← relIdx_eq_zero_iff]
  show (relIdx x y = 1 ∨ relIdx x y = 2) ↔ _
  generalize relIdx x y = r
  fin_cases r <;> decide

theorem isNbr_comm
    (x y : Pts) : IsNbr x y ↔ IsNbr y x := by
  rw [IsNbr, IsNbr, relIdx_comm]

@[expose] def cnbr (r : Fin 5) : ℕ := orbM 1 r 1 + orbM 1 r 2 + orbM 2 r 1 + orbM 2 r 2

theorem cnbr_three : cnbr 3 = 295 := by decide

theorem cnbr_four : cnbr 4 = 693 := by decide

theorem cnbr_le : ∀ r : Fin 5, r ≠ 0 → cnbr r ≤ 2997 := by decide

theorem card_filter_isNbr_isNbr
    (x y : Pts) :
    (Finset.univ.filter fun z => IsNbr x z ∧ IsNbr z y).card = cnbr (relIdx x y) := by
  classical
  have e : (Finset.univ.filter fun z => IsNbr x z ∧ IsNbr z y) =
      (((Finset.univ.filter fun z => relIdx x z = 1 ∧ relIdx z y = 1) ∪
        (Finset.univ.filter fun z => relIdx x z = 1 ∧ relIdx z y = 2)) ∪
        (Finset.univ.filter fun z => relIdx x z = 2 ∧ relIdx z y = 1)) ∪
        (Finset.univ.filter fun z => relIdx x z = 2 ∧ relIdx z y = 2) := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, IsNbr]
    tauto
  rw [e, Finset.card_union_of_disjoint, Finset.card_union_of_disjoint,
    Finset.card_union_of_disjoint, card_filter_relIdx, card_filter_relIdx, card_filter_relIdx,
    card_filter_relIdx, cnbr]
  all_goals
    rw [Finset.disjoint_left]
    intro z hz1 hz2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at hz1 hz2
    rw [hz2.1, hz2.2] at hz1
    revert hz1
    decide

theorem card_filter_relIdx_isNbr
    (x d : Pts) (k : Fin 5) :
    (Finset.univ.filter fun z => relIdx x z = k ∧ IsNbr z d).card =
      orbM k (relIdx x d) 1 + orbM k (relIdx x d) 2 := by
  classical
  have e : (Finset.univ.filter fun z => relIdx x z = k ∧ IsNbr z d) =
      (Finset.univ.filter fun z => relIdx x z = k ∧ relIdx z d = 1) ∪
        (Finset.univ.filter fun z => relIdx x z = k ∧ relIdx z d = 2) := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, IsNbr]
    tauto
  rw [e, Finset.card_union_of_disjoint, card_filter_relIdx, card_filter_relIdx]
  rw [Finset.disjoint_left]
  intro z hz1 hz2
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz1 hz2
  rw [hz2.2] at hz1
  exact absurd hz1.2 (by decide)

theorem orbM_three_le : ∀ r : Fin 5, (r = 1 ∨ r = 2) → orbM 3 r 1 + orbM 3 r 2 ≤ 44032 := by
  decide

theorem orbM_four_le : ∀ r : Fin 5, (r = 1 ∨ r = 2) → orbM 4 r 1 + orbM 4 r 2 ≤ 32768 := by
  decide

theorem starConj_betaStarElt
    (x : stdGroup) : starConj betaStarElt x = betaG x := by
  simp [starConj]

theorem coe_betaStarElt_smul
    (x : Pts) : ((betaStarElt • x : Pts) : stdGroup) = betaG x :=
  starConj_betaStarElt x

theorem ncard_not_reachable_le
    {x : Pts} (hx : x ∈ nonFixedRoots) :
    {z : Pts | ∃ hz : z ∈ nonFixedRoots,
      ¬nonFixedGraph.Reachable ⟨x, hx⟩ ⟨z, hz⟩}.ncard ≤ 589045 := by
  classical
  set Zs : Finset Pts := Finset.univ.filter fun z => ∃ hz : z ∈ nonFixedRoots,
    ¬nonFixedGraph.Reachable ⟨x, hx⟩ ⟨z, hz⟩ with hZs
  have hZcoe : {z : Pts | ∃ hz : z ∈ nonFixedRoots,
      ¬nonFixedGraph.Reachable ⟨x, hx⟩ ⟨z, hz⟩} = (Zs : Set Pts) := by
    ext z
    simp [hZs]
  rw [hZcoe, Set.ncard_coe_finset]
  have hadj : ∀ {a b : Pts} (ha : a ∈ nonFixedRoots) (hb : b ∈ nonFixedRoots), IsNbr a b →
      nonFixedGraph.Adj ⟨a, ha⟩ ⟨b, hb⟩ := by
    intro a b ha hb hab
    obtain ⟨hne, hc⟩ := (isNbr_iff a b).1 hab
    rw [nonFixedGraph, SimpleGraph.fromRel_adj]
    exact ⟨fun e => hne (congrArg Subtype.val e), Or.inl hc⟩
  set D : Finset Pts := Finset.univ.filter fun d => IsNbr x d ∧ betaG (d : stdGroup) = d with hD
  set bx : Pts := betaStarElt • x with hbx
  have hbx_ne : relIdx x bx ≠ 0 := by
    rw [ne_eq, relIdx_eq_zero_iff]
    intro e
    apply hx
    have h := congrArg Subtype.val e
    rw [hbx, coe_betaStarElt_smul] at h
    exact h.symm
  have hDcard : D.card ≤ 2997 := by
    have hsub : D ⊆ Finset.univ.filter fun w => IsNbr x w ∧ IsNbr w bx := by
      intro d hd
      simp only [hD, Finset.mem_filter, Finset.mem_univ, true_and] at hd ⊢
      refine ⟨hd.1, ?_⟩
      have hbd : betaStarElt • d = d := Subtype.ext (by rw [coe_betaStarElt_smul, hd.2])
      have h := relIdx_smul betaStarElt x d
      rw [hbd, ← hbx] at h
      rw [isNbr_comm, IsNbr, h]
      exact hd.1
    calc D.card ≤ _ := Finset.card_le_card hsub
      _ = cnbr (relIdx x bx) := card_filter_isNbr_isNbr x bx
      _ ≤ 2997 := cnbr_le _ hbx_ne
  have hZ : ∀ z ∈ Zs, (relIdx x z = 3 ∨ relIdx x z = 4) ∧
      ∀ w, IsNbr x w → IsNbr w z → w ∈ D := by
    intro z hz
    simp only [hZs, Finset.mem_filter, Finset.mem_univ, true_and] at hz
    obtain ⟨hzA, hnr⟩ := hz
    refine ⟨?_, fun w hxw hwz => ?_⟩
    · have h0 : relIdx x z ≠ 0 := by
        rw [ne_eq, relIdx_eq_zero_iff]
        rintro rfl
        exact hnr (SimpleGraph.Reachable.refl _)
      have h12 : ¬(relIdx x z = 1 ∨ relIdx x z = 2) := fun h => hnr (hadj hx hzA h).reachable
      revert h0 h12
      generalize relIdx x z = r
      fin_cases r <;> decide
    · simp only [hD, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨hxw, ?_⟩
      by_contra hw
      exact hnr ((hadj hx hw hxw).reachable.trans (hadj hw hzA hwz).reachable)
  have hcount : ∀ k : Fin 5, ∀ m n : ℕ, cnbr k = m →
      (∀ r : Fin 5, (r = 1 ∨ r = 2) → orbM k r 1 + orbM k r 2 ≤ n) →
      (Zs.filter fun z => relIdx x z = k).card * m ≤ 2997 * n := by
    intro k m n hm hn
    have h := Finset.card_nsmul_le_card_nsmul (s := Zs.filter fun z => relIdx x z = k) (t := D)
      (r := fun z d => IsNbr z d) (m := m) (n := n) ?_ ?_
    · rw [smul_eq_mul, smul_eq_mul] at h
      calc (Zs.filter fun z => relIdx x z = k).card * m ≤ D.card * n := h
        _ ≤ 2997 * n := Nat.mul_le_mul_right n hDcard
    · intro z hz
      rw [Finset.mem_filter] at hz
      rw [← hm, ← hz.2, ← card_filter_isNbr_isNbr x z]
      refine Finset.card_le_card fun w hw => ?_
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
      rw [Finset.mem_bipartiteAbove]
      exact ⟨(hZ z hz.1).2 w hw.1 hw.2, (isNbr_comm _ _).1 hw.2⟩
    · intro d hd
      have hd' := hd
      simp only [hD, Finset.mem_filter, Finset.mem_univ, true_and] at hd'
      calc (Finset.bipartiteBelow (fun z d => IsNbr z d) (Zs.filter fun z => relIdx x z = k)
            d).card ≤ (Finset.univ.filter fun z => relIdx x z = k ∧ IsNbr z d).card := by
            refine Finset.card_le_card fun z hz => ?_
            rw [Finset.mem_bipartiteBelow, Finset.mem_filter] at hz
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨hz.1.2, hz.2⟩
        _ = orbM k (relIdx x d) 1 + orbM k (relIdx x d) 2 := card_filter_relIdx_isNbr x d k
        _ ≤ n := hn _ hd'.1
  have h3 := hcount 3 295 44032 cnbr_three orbM_three_le
  have h4 := hcount 4 693 32768 cnbr_four orbM_four_le
  have hsplit : Zs.card = (Zs.filter fun z => relIdx x z = 3).card +
      (Zs.filter fun z => relIdx x z = 4).card := by
    rw [← Finset.card_union_of_disjoint (Finset.disjoint_filter.2 fun z _ h3 h4 => by
      rw [h3] at h4
      exact absurd h4 (by decide))]
    congr 1
    ext z
    simp only [Finset.mem_union, Finset.mem_filter]
    constructor
    · intro hz
      rcases (hZ z hz).1 with h | h
      · exact Or.inl ⟨hz, h⟩
      · exact Or.inr ⟨hz, h⟩
    · rintro (h | h)
      · exact h.1
      · exact h.1
  omega

theorem nonFixedGraph_connected
    (hA : 1178090 < nonFixedRoots.ncard) :
    nonFixedGraph.Connected := by
  classical
  have hne : nonFixedRoots.Nonempty := Set.nonempty_of_ncard_ne_zero (by omega)
  have : Nonempty nonFixedRoots := hne.to_subtype
  refine ⟨fun a b => ?_⟩
  by_contra hab
  set Afin : Finset Pts := Finset.univ.filter fun z => z ∈ nonFixedRoots with hAfin
  have hAcard : nonFixedRoots.ncard = Afin.card := by
    rw [Set.ncard_eq_toFinset_card']
    congr 1
    ext z
    simp [hAfin]
  set Ra : Finset Pts := Afin.filter fun z => ∃ hz : z ∈ nonFixedRoots,
    nonFixedGraph.Reachable a ⟨z, hz⟩ with hRa
  set Za : Finset Pts := Afin.filter fun z => ¬∃ hz : z ∈ nonFixedRoots,
    nonFixedGraph.Reachable a ⟨z, hz⟩ with hZa
  have hsplit : Afin.card = Ra.card + Za.card := by
    rw [hRa, hZa, Finset.card_filter_add_card_filter_not]
  have hbound : ∀ c : nonFixedRoots, (Afin.filter fun z => ¬∃ hz : z ∈ nonFixedRoots,
      nonFixedGraph.Reachable c ⟨z, hz⟩).card ≤ 589045 := by
    intro c
    have h := ncard_not_reachable_le c.2
    rw [← Set.ncard_coe_finset]
    refine le_trans (Set.ncard_le_ncard ?_ (Set.toFinite _)) h
    intro z hz
    simp only [Finset.coe_filter, Finset.mem_filter, Finset.mem_univ, true_and,
      Set.mem_ofPred_eq, hAfin] at hz
    obtain ⟨hzA, hnr⟩ := hz
    exact ⟨hzA, fun h => hnr ⟨hzA, by simpa using h⟩⟩
  have hZa : Za.card ≤ 589045 := hbound a
  have hRa' : Ra.card ≤ 589045 := by
    refine le_trans (Finset.card_le_card fun z hz => ?_) (hbound b)
    simp only [hRa, Finset.mem_filter] at hz ⊢
    refine ⟨hz.1, ?_⟩
    rintro ⟨hzA, hbz⟩
    obtain ⟨hzA', haz⟩ := hz.2
    exact hab (haz.trans hbz.symm)
  omega

end CFSG.Monster.B.GSide
