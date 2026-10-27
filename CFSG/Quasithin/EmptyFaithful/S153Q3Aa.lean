module

public import CFSG.Quasithin.EmptyFaithful.S153QDef

public section

namespace CFSG.Quasithin

namespace S153Q

namespace Q3A

variable {W : Type} [CommGroup W] {z : MulAut W}

theorem z3_apply (hz3 : z ^ 3 = 1) (w : W) : z (z (z w)) = w := by
  have h := congrArg (fun g : MulAut W => g w) hz3
  simpa [pow_succ, MulAut.mul_apply] using h

theorem four_distinct (hz3 : z ^ 3 = 1) (hfpf : ∀ w : W, z w = w → w = 1) {w : W} (hw1 : w ≠ 1) :
    z w ≠ 1 ∧ z (z w) ≠ 1 ∧ z w ≠ w ∧ z (z w) ≠ w ∧ z (z w) ≠ z w := by
  have hz1 : ∀ u : W, z u = 1 → u = 1 := fun u hu => z.injective (hu.trans (map_one z).symm)
  have h1 : z w ≠ 1 := fun h => hw1 (hz1 w h)
  have h2 : z (z w) ≠ 1 := fun h => h1 (hz1 _ h)
  have h3 : z w ≠ w := fun h => hw1 (hfpf w h)
  have h4 : z (z w) ≠ w := fun h => by
    apply h3
    have := congrArg z h
    rw [z3_apply hz3] at this
    exact this.symm
  have h5 : z (z w) ≠ z w := fun h => h1 (hfpf _ h)
  exact ⟨h1, h2, h3, h4, h5⟩

variable [Finite W]

theorem mem_pt_iff (hz3 : z ^ 3 = 1) (hfpf : ∀ w : W, z w = w → w = 1) {o : Subgroup W}
    (ho : IsPt z o) {w : W} (hw : w ∈ o) (hw1 : w ≠ 1) (u : W) :
    u ∈ o ↔ u = 1 ∨ u = w ∨ u = z w ∨ u = z (z w) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := four_distinct hz3 hfpf hw1
  have hsub : ({1, w, z w, z (z w)} : Set W) ⊆ (o : Set W) := by
    intro v hv
    rcases hv with rfl | rfl | rfl | rfl
    · exact o.one_mem
    · exact hw
    · exact ho.2 _ hw
    · exact ho.2 _ (ho.2 _ hw)
  have hcard : ({1, w, z w, z (z w)} : Set W).ncard = 4 := by
    have e1 : (1 : W) ∉ ({w, z w, z (z w)} : Set W) := by
      simp [hw1.symm, h1.symm, h2.symm]
    have e2 : w ∉ ({z w, z (z w)} : Set W) := by simp [h3.symm, h4.symm]
    rw [Set.ncard_insert_of_notMem e1 (Set.toFinite _),
      Set.ncard_insert_of_notMem e2 (Set.toFinite _), Set.ncard_pair h5.symm]
  have hcard' : (o : Set W).ncard = 4 := (Nat.card_coe_set_eq (o : Set W)).symm.trans ho.1
  have hS : ({1, w, z w, z (z w)} : Set W) = (o : Set W) :=
    Set.eq_of_subset_of_ncard_le hsub (le_of_eq (hcard'.trans hcard.symm)) (Set.toFinite _)
  constructor
  · intro hu
    have : u ∈ ({1, w, z w, z (z w)} : Set W) := by rw [hS]; exact hu
    simpa using this
  · intro hu
    have : u ∈ ({1, w, z w, z (z w)} : Set W) := by simpa using hu
    rw [hS] at this
    exact this

theorem pt_ext (hz3 : z ^ 3 = 1) (hfpf : ∀ w : W, z w = w → w = 1) {o o' : Subgroup W}
    (ho : IsPt z o) (ho' : IsPt z o') {w : W} (hw : w ∈ o) (hw' : w ∈ o') (hw1 : w ≠ 1) :
    o = o' := by
  ext u
  rw [mem_pt_iff hz3 hfpf ho hw hw1, mem_pt_iff hz3 hfpf ho' hw' hw1]

theorem ncard_pts_le (hWc : Nat.card W = 2 ^ 6) (hz3 : z ^ 3 = 1)
    (hfpf : ∀ w : W, z w = w → w = 1) {S : Set (Subgroup W)} (hS : ∀ o ∈ S, IsPt z o) :
    S.ncard ≤ 21 := by
  classical
  have : Fintype W := Fintype.ofFinite W
  have hSfin : S.Finite := Set.toFinite S
  let t : Subgroup W → Finset W := fun o => Finset.univ.filter fun w => w ∈ o ∧ w ≠ 1
  have ht : ∀ o, IsPt z o → (t o).card = 3 := by
    intro o ho
    have h1 : ((t o : Finset W) : Set W) = (o : Set W) \ {1} := by
      ext w
      simp [t]
    have h2 : (t o).card = ((o : Set W) \ {1}).ncard := by
      rw [← h1, Set.ncard_coe_finset]
    rw [h2, Set.ncard_sdiff_singleton_of_mem o.one_mem]
    have : (o : Set W).ncard = 4 := (Nat.card_coe_set_eq (o : Set W)).symm.trans ho.1
    omega
  have hdisj : (↑hSfin.toFinset : Set (Subgroup W)).PairwiseDisjoint t := by
    intro o ho o' ho' hne
    show Disjoint (t o) (t o')
    rw [Finset.disjoint_left]
    intro w hw hw'
    simp only [t, Finset.mem_filter, Finset.mem_univ, true_and] at hw hw'
    exact hne (pt_ext hz3 hfpf (hS o (hSfin.mem_toFinset.mp ho))
      (hS o' (hSfin.mem_toFinset.mp ho')) hw.1 hw'.1 hw.2)
  have hcard := Finset.card_biUnion hdisj
  have hsum : ∑ o ∈ hSfin.toFinset, (t o).card = hSfin.toFinset.card * 3 := by
    rw [Finset.sum_congr rfl (fun o ho => ht o (hS o (hSfin.mem_toFinset.mp ho)))]
    simp
  have hle : (hSfin.toFinset.biUnion t).card ≤ 64 := by
    calc (hSfin.toFinset.biUnion t).card ≤ Fintype.card W := Finset.card_le_univ _
      _ = 64 := by rw [← Nat.card_eq_fintype_card, hWc]; norm_num
  have hn : S.ncard = hSfin.toFinset.card := Set.ncard_eq_toFinset_card S hSfin
  omega

end Q3A

end S153Q

end CFSG.Quasithin
