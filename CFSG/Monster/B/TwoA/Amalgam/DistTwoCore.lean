module

public import CFSG.Monster.B.TwoA.Amalgam.DistTwoModel
public import CFSG.Monster.B.TwoA.Amalgam.CosetGraphLocalBase

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Amalgam

open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA
open CFSG.Monster.B.E6.StdF4 CFSG.LieType.Chevalley.C2E6Std
  CFSG.LieType.Chevalley.C2E6Std.FieldExtension

theorem cgraph_dist_eq_two_iff
    {v w : CVert} :
    cgraph.dist v w = 2 ↔ v ≠ w ∧ ¬cgraph.Adj v w ∧ ∃ u, cgraph.Adj v u ∧ cgraph.Adj u w := by
  rw [SimpleGraph.dist, ENat.toNat_eq_iff two_ne_zero, Nat.cast_ofNat,
    SimpleGraph.edist_eq_two_iff]
  simp only [Set.Nonempty, SimpleGraph.mem_commonNeighbors]
  exact and_congr_right fun _ => and_congr_right fun _ =>
    exists_congr fun u => and_congr_right fun _ => cgraph.adj_comm _ _

theorem dist_eq_two_cvMul
    {v w : CVert} (h : cgraph.dist v w = 2) (s : Shat) :
    cgraph.dist (cvMul v s) (cvMul w s) = 2 := by
  rw [cgraph_dist_eq_two_iff] at h ⊢
  obtain ⟨hne, hna, u, hu1, hu2⟩ := h
  exact ⟨fun e => hne (cvMul_injective s e), fun ha => hna ((cgraph_adj_cvMul v w s).1 ha),
    cvMul u s, (cgraph_adj_cvMul v u s).2 hu1, (cgraph_adj_cvMul u w s).2 hu2⟩

abbrev lblOrd
    (v w : CVert) : ℕ := orderOf (clabel v * clabel w)

theorem lblOrd_cvMul
    (v w : CVert) (s : Shat) :
    lblOrd (cvMul v s) (cvMul w s) = lblOrd v w := by
  rw [lblOrd, clabel_cvMul, clabel_cvMul]
  have e : ((s : Dfull))⁻¹ * clabel v * s * (((s : Dfull))⁻¹ * clabel w * s) =
      MulAut.conj ((s : Dfull))⁻¹ (clabel v * clabel w) := by
    rw [MulAut.conj_apply, inv_inv]
    group
  rw [e, MulEquiv.orderOf_eq]

abbrev LabelThree
    (v w : CVert) : Prop := lblOrd v w = 3 ∨ lblOrd v w = 6

abbrev LabelFour
    (v w : CVert) : Prop := lblOrd v w = 4 ∨ lblOrd v w = 8

theorem labelThree_cvMul
    (v w : CVert) (s : Shat) :
    LabelThree (cvMul v s) (cvMul w s) ↔ LabelThree v w := by
  rw [LabelThree, LabelThree, lblOrd_cvMul]

theorem labelFour_cvMul
    (v w : CVert) (s : Shat) :
    LabelFour (cvMul v s) (cvMul w s) ↔ LabelFour v w := by
  rw [LabelFour, LabelFour, lblOrd_cvMul]

@[expose] def sphereThree
    (v : CVert) : Set CVert :=
  {w | cgraph.dist v w = 2 ∧ LabelThree v w}

@[expose] def sphereFour
    (v : CVert) : Set CVert :=
  {w | cgraph.dist v w = 2 ∧ LabelFour v w}

@[expose] def IsDistTwoPath
    (t : CVert × CVert × CVert) : Prop :=
  cgraph.Adj t.2.1 t.1 ∧ cgraph.Adj t.2.1 t.2.2 ∧ cgraph.dist t.1 t.2.2 = 2

@[expose] def tripleOrbit
    (t : CVert × CVert × CVert) : Set (CVert × CVert × CVert) :=
  {t' | ∃ s : Shat, t' = (cvMul t.1 s, cvMul t.2.1 s, cvMul t.2.2 s)}

@[expose] def vStabOrbit
    (v w : CVert) : Set CVert :=
  {w' | ∃ s : Shat, cvMul v s = v ∧ cvMul w s = w'}

theorem dist_eq_two_iff_of_mem
    {u : CVert} {v w : cgraph.neighborSet u} :
    cgraph.dist v w = 2 ↔ v ≠ w ∧ ¬cgraph.Adj v w := by
  rw [cgraph_dist_eq_two_iff]
  exact ⟨fun h => ⟨fun e => h.1 (congrArg Subtype.val e), h.2.1⟩,
    fun h => ⟨fun e => h.1 (Subtype.ext e), h.2, u, (cgraph.adj_comm _ _).1 v.2, w.2⟩⟩

namespace RootModel

variable {u : CVert} (M : RootModel u)

theorem not_commute_of_not_adj {v w : cgraph.neighborSet u} (hne : v ≠ w)
    (hna : ¬cgraph.Adj v w) : ¬Commute (M.pt v) (M.pt w) := fun h =>
  hna ((M.adj_iff_commute hne).2 h)

theorem labelThree_iff (hL : M.LabelCompat) {v w : cgraph.neighborSet u} (hne : v ≠ w)
    (hna : ¬cgraph.Adj v w) :
    LabelThree v w ↔ orbSize (M.pt v) (M.pt w) = 2097152 := by
  rcases (not_commute_iff_orbSize (M.pt_mem v) (M.pt_mem w)).1
    (M.not_commute_of_not_adj hne hna) with h4 | h3
  · have ho := (orderOf_eq_four_iff (M.pt_mem v) (M.pt_mem w)).2 h4
    rw [h4]
    rcases hL v w with e | e <;> rw [LabelThree, lblOrd, e, ho] <;> decide
  · have ho := (orderOf_eq_three_iff (M.pt_mem v) (M.pt_mem w)).2 h3
    rw [h3]
    rcases hL v w with e | e <;> rw [LabelThree, lblOrd, e, ho] <;> decide

theorem labelFour_iff (hL : M.LabelCompat) {v w : cgraph.neighborSet u} (hne : v ≠ w)
    (hna : ¬cgraph.Adj v w) :
    LabelFour v w ↔ orbSize (M.pt v) (M.pt w) = 1824768 := by
  rcases (not_commute_iff_orbSize (M.pt_mem v) (M.pt_mem w)).1
    (M.not_commute_of_not_adj hne hna) with h4 | h3
  · have ho := (orderOf_eq_four_iff (M.pt_mem v) (M.pt_mem w)).2 h4
    rw [h4]
    rcases hL v w with e | e <;> rw [LabelFour, lblOrd, e, ho] <;> decide
  · have ho := (orderOf_eq_three_iff (M.pt_mem v) (M.pt_mem w)).2 h3
    rw [h3]
    rcases hL v w with e | e <;> rw [LabelFour, lblOrd, e, ho] <;> decide

theorem labelThree_or_labelFour (hL : M.LabelCompat) {v w : cgraph.neighborSet u} (hne : v ≠ w)
    (hna : ¬cgraph.Adj v w) :
    (LabelThree v w ∧ ¬LabelFour v w) ∨ (LabelFour v w ∧ ¬LabelThree v w) := by
  rw [M.labelThree_iff hL hne hna, M.labelFour_iff hL hne hna]
  rcases (not_commute_iff_orbSize (M.pt_mem v) (M.pt_mem w)).1
    (M.not_commute_of_not_adj hne hna) with h | h <;> rw [h] <;> decide

theorem ne_of_orbSize_eq {v w : cgraph.neighborSet u} {n : ℕ} (h : orbSize (M.pt v) (M.pt w) = n)
    (hn : n ≠ 1) : v ≠ w := by
  rintro rfl
  have h1 : orbSize (M.pt v) (M.pt v) = 1 := by
    obtain ⟨i, hi, ho⟩ := exists_orbSize_eq (M.pt_mem v) (M.pt_mem v)
    have h2 : orderOf (M.pt v * M.pt v) = 1 := by
      rw [mul_self_of_mem_rootClassStar (M.pt_mem v), orderOf_one]
    rw [h2] at ho
    rw [hi]
    revert ho
    fin_cases i <;> decide
  exact hn (h.symm.trans h1)

theorem labelThree_dist_iff (hL : M.LabelCompat) (v w : cgraph.neighborSet u) :
    (cgraph.dist v w = 2 ∧ LabelThree v w) ↔ orbSize (M.pt v) (M.pt w) = 2097152 := by
  rw [dist_eq_two_iff_of_mem]
  refine ⟨fun h => (M.labelThree_iff hL h.1.1 h.1.2).1 h.2, fun h => ?_⟩
  have hne := M.ne_of_orbSize_eq h (by decide)
  have hna : ¬cgraph.Adj v w := fun ha => (not_commute_iff_orbSize (M.pt_mem v)
    (M.pt_mem w)).2 (Or.inr h) ((M.adj_iff_commute hne).1 ha)
  exact ⟨⟨hne, hna⟩, (M.labelThree_iff hL hne hna).2 h⟩

theorem labelFour_dist_iff (hL : M.LabelCompat) (v w : cgraph.neighborSet u) :
    (cgraph.dist v w = 2 ∧ LabelFour v w) ↔ orbSize (M.pt v) (M.pt w) = 1824768 := by
  rw [dist_eq_two_iff_of_mem]
  refine ⟨fun h => (M.labelFour_iff hL h.1.1 h.1.2).1 h.2, fun h => ?_⟩
  have hne := M.ne_of_orbSize_eq h (by decide)
  have hna : ¬cgraph.Adj v w := fun ha => (not_commute_iff_orbSize (M.pt_mem v)
    (M.pt_mem w)).2 (Or.inl h) ((M.adj_iff_commute hne).1 ha)
  exact ⟨⟨hne, hna⟩, (M.labelFour_iff hL hne hna).2 h⟩

include M in
theorem nonempty_neighborSet : (cgraph.neighborSet u).Nonempty :=
  ⟨M.iv.symm ⟨rootInv, IsConj.refl rootInv⟩, (M.iv.symm ⟨rootInv, IsConj.refl rootInv⟩).2⟩

end RootModel

section Global

variable (hM : ∀ u : CVert, ∃ M : RootModel u, M.LabelCompat)

include hM in
theorem labelThree_or_labelFour_of_dist {v w : CVert} (h : cgraph.dist v w = 2) :
    (LabelThree v w ∧ ¬LabelFour v w) ∨ (LabelFour v w ∧ ¬LabelThree v w) := by
  obtain ⟨hne, hna, u, hvu, huw⟩ := cgraph_dist_eq_two_iff.1 h
  obtain ⟨M, hL⟩ := hM u
  exact M.labelThree_or_labelFour hL (v := ⟨v, hvu.symm⟩) (w := ⟨w, huw⟩)
    (fun e => hne (congrArg Subtype.val e)) hna

include hM in
theorem labelFour_iff_not_labelThree {v w : CVert} (h : cgraph.dist v w = 2) :
    LabelFour v w ↔ ¬LabelThree v w := by
  rcases labelThree_or_labelFour_of_dist hM h with h3 | h4
  · exact ⟨fun h4 => absurd h4 h3.2, fun hn => absurd h3.1 hn⟩
  · exact ⟨fun _ => h4.2, fun _ => h4.1⟩

include hM in
theorem exists_smul_eq_path {v u w v' u' w' : CVert} (huv : cgraph.Adj u v)
    (huw : cgraph.Adj u w) (hd : cgraph.dist v w = 2) (huv' : cgraph.Adj u' v')
    (huw' : cgraph.Adj u' w') (hd' : cgraph.dist v' w' = 2)
    (h : LabelThree v w ↔ LabelThree v' w') :
    ∃ s : Shat, cvMul v s = v' ∧ cvMul u s = u' ∧ cvMul w s = w' := by
  obtain ⟨s, hs⟩ := cvMul_transitive u u'
  obtain ⟨M, hL⟩ := hM u'
  have ha : cvMul v s ∈ cgraph.neighborSet u' := by
    have h1 := (cgraph_adj_cvMul u v s).2 huv
    rwa [hs] at h1
  have hb : cvMul w s ∈ cgraph.neighborSet u' := by
    have h1 := (cgraph_adj_cvMul u w s).2 huw
    rwa [hs] at h1
  have hds := dist_eq_two_cvMul hd s
  have horb : orbSize (M.pt ⟨_, ha⟩) (M.pt ⟨_, hb⟩) =
      orbSize (M.pt ⟨v', huv'⟩) (M.pt ⟨w', huw'⟩) := by
    by_cases h3 : LabelThree v w
    · rw [(M.labelThree_dist_iff hL ⟨_, ha⟩ ⟨_, hb⟩).1 ⟨hds, (labelThree_cvMul v w s).2 h3⟩,
        (M.labelThree_dist_iff hL ⟨v', huv'⟩ ⟨w', huw'⟩).1 ⟨hd', h.1 h3⟩]
    · have h4 := (labelFour_iff_not_labelThree hM hd).2 h3
      have h4' := (labelFour_iff_not_labelThree hM hd').2 fun h3' => h3 (h.2 h3')
      rw [(M.labelFour_dist_iff hL ⟨_, ha⟩ ⟨_, hb⟩).1 ⟨hds, (labelFour_cvMul v w s).2 h4⟩,
        (M.labelFour_dist_iff hL ⟨v', huv'⟩ ⟨w', huw'⟩).1 ⟨hd', h4'⟩]
  obtain ⟨y, hy, hya, hyb⟩ := M.exists_smul_eq_pair horb
  exact ⟨s * y, by rw [cvMul_mul]; exact hya, by rw [cvMul_mul, hs]; exact hy,
    by rw [cvMul_mul]; exact hyb⟩

theorem isDistTwoPath_cvMul {t : CVert × CVert × CVert} (ht : IsDistTwoPath t) (s : Shat) :
    IsDistTwoPath (cvMul t.1 s, cvMul t.2.1 s, cvMul t.2.2 s) :=
  ⟨(cgraph_adj_cvMul _ _ s).2 ht.1, (cgraph_adj_cvMul _ _ s).2 ht.2.1,
    dist_eq_two_cvMul ht.2.2 s⟩

include hM in
theorem tripleOrbit_eq {t : CVert × CVert × CVert} (ht : IsDistTwoPath t) :
    tripleOrbit t =
      {t' | IsDistTwoPath t' ∧ (LabelThree t.1 t.2.2 ↔ LabelThree t'.1 t'.2.2)} := by
  ext t'
  constructor
  · rintro ⟨s, rfl⟩
    exact ⟨isDistTwoPath_cvMul ht s, (labelThree_cvMul _ _ s).symm⟩
  · rintro ⟨ht', h⟩
    obtain ⟨s, h1, h2, h3⟩ := exists_smul_eq_path hM ht.1 ht.2.1 ht.2.2 ht'.1 ht'.2.1 ht'.2.2 h
    exact ⟨s, by rw [h1, h2, h3]⟩

include hM in
theorem mem_tripleOrbit_iff {t t' : CVert × CVert × CVert} (ht : IsDistTwoPath t)
    (ht' : IsDistTwoPath t') :
    t' ∈ tripleOrbit t ↔ (LabelThree t.1 t.2.2 ↔ LabelThree t'.1 t'.2.2) := by
  rw [tripleOrbit_eq hM ht]
  exact ⟨fun h => h.2, fun h => ⟨ht', h⟩⟩

theorem exists_path_of_model {u : CVert} (M : RootModel u) (hL : M.LabelCompat) (i : Fin 5)
    (hi : repSize i = 2097152 ∨ repSize i = 1824768) :
    ∃ v w : CVert, cgraph.Adj u v ∧ cgraph.Adj u w ∧ cgraph.dist v w = 2 ∧
      (LabelThree v w ↔ repSize i = 2097152) := by
  obtain ⟨v, hv⟩ := M.nonempty_neighborSet
  obtain ⟨q, hq, hqs⟩ := exists_orbSize_eq_repSize (M.pt_mem ⟨v, hv⟩) i
  obtain ⟨w, rfl⟩ := M.exists_pt_eq hq
  rcases hi with hi | hi
  · rw [hi] at hqs
    obtain ⟨hd, h3⟩ := (M.labelThree_dist_iff hL ⟨v, hv⟩ w).2 hqs
    exact ⟨v, w, hv, w.2, hd, iff_of_true h3 hi⟩
  · rw [hi] at hqs
    obtain ⟨hd, h4⟩ := (M.labelFour_dist_iff hL ⟨v, hv⟩ w).2 hqs
    refine ⟨v, w, hv, w.2, hd, iff_of_false ?_ (by rw [hi]; decide)⟩
    exact ((M.labelThree_or_labelFour hL (dist_eq_two_iff_of_mem.1 hd).1
      (dist_eq_two_iff_of_mem.1 hd).2).resolve_left fun h => h.2 h4).2

include hM in
theorem exists_path_labelThree : ∃ t, IsDistTwoPath t ∧ LabelThree t.1 t.2.2 := by
  obtain ⟨M, hL⟩ := hM cv0
  obtain ⟨v, w, hv, hw, hd, h⟩ := exists_path_of_model M hL 4 (Or.inl rfl)
  exact ⟨(v, cv0, w), ⟨hv, hw, hd⟩, h.2 rfl⟩

include hM in
theorem exists_path_labelFour : ∃ t, IsDistTwoPath t ∧ ¬LabelThree t.1 t.2.2 := by
  obtain ⟨M, hL⟩ := hM cv0
  obtain ⟨v, w, hv, hw, hd, h⟩ := exists_path_of_model M hL 3 (Or.inr rfl)
  exact ⟨(v, cv0, w), ⟨hv, hw, hd⟩, fun h3 => absurd (h.1 h3) (by decide)⟩

include hM in
theorem ncard_setOf_tripleOrbit :
    {O : Set (CVert × CVert × CVert) | ∃ t, IsDistTwoPath t ∧ O = tripleOrbit t}.ncard = 2 := by
  obtain ⟨t₃, ht₃, h₃⟩ := exists_path_labelThree hM
  obtain ⟨t₄, ht₄, h₄⟩ := exists_path_labelFour hM
  have e : {O : Set (CVert × CVert × CVert) | ∃ t, IsDistTwoPath t ∧ O = tripleOrbit t} =
      {tripleOrbit t₃, tripleOrbit t₄} := by
    ext O
    simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨t, ht, rfl⟩
      by_cases h3 : LabelThree t.1 t.2.2
      · left
        rw [tripleOrbit_eq hM ht, tripleOrbit_eq hM ht₃, iff_true_intro h3, iff_true_intro h₃]
      · right
        rw [tripleOrbit_eq hM ht, tripleOrbit_eq hM ht₄, iff_false_intro h3, iff_false_intro h₄]
    · rintro (rfl | rfl)
      exacts [⟨t₃, ht₃, rfl⟩, ⟨t₄, ht₄, rfl⟩]
  rw [e, Set.ncard_pair]
  intro h
  have h1 : t₄ ∈ tripleOrbit t₃ := by
    rw [h]
    exact ⟨1, by simp only [cvMul_one]⟩
  exact h₄ (((mem_tripleOrbit_iff hM ht₃ ht₄).1 h1).1 h₃)

include hM in
theorem vStabOrbit_eq {v w : CVert} (hw : cgraph.dist v w = 2) :
    vStabOrbit v w = {w' | cgraph.dist v w' = 2 ∧ (LabelThree v w ↔ LabelThree v w')} := by
  ext w'
  constructor
  · rintro ⟨s, hs, rfl⟩
    have hd := dist_eq_two_cvMul hw s
    have hl := labelThree_cvMul v w s
    rw [hs] at hd hl
    exact ⟨hd, hl.symm⟩
  · rintro ⟨hw', h⟩
    obtain ⟨-, -, u, hvu, huw⟩ := cgraph_dist_eq_two_iff.1 hw
    obtain ⟨-, -, u', hvu', huw'⟩ := cgraph_dist_eq_two_iff.1 hw'
    obtain ⟨s, hs, -, hsw⟩ := exists_smul_eq_path hM hvu.symm huw hw hvu'.symm huw' hw' h
    exact ⟨s, hs, hsw⟩

include hM in
theorem vStabOrbit_eq_sphereThree {v w : CVert} (hw : w ∈ sphereThree v) :
    vStabOrbit v w = sphereThree v := by
  rw [vStabOrbit_eq hM hw.1, sphereThree, iff_true_intro hw.2]
  simp only [true_iff]

include hM in
theorem vStabOrbit_eq_sphereFour {v w : CVert} (hw : w ∈ sphereFour v) :
    vStabOrbit v w = sphereFour v := by
  rw [vStabOrbit_eq hM hw.1, sphereFour,
    iff_false_intro ((labelFour_iff_not_labelThree hM hw.1).1 hw.2)]
  ext w'
  simp only [Set.mem_ofPred_eq, false_iff]
  exact and_congr_right fun hd => (labelFour_iff_not_labelThree hM hd).symm

include hM in
theorem setOf_dist_eq_two_eq_union (v : CVert) :
    {w | cgraph.dist v w = 2} = sphereThree v ∪ sphereFour v := by
  ext w
  simp only [Set.mem_ofPred_eq, Set.mem_union, sphereThree, sphereFour]
  constructor
  · intro h
    rcases labelThree_or_labelFour_of_dist hM h with h3 | h4
    exacts [Or.inl ⟨h, h3.1⟩, Or.inr ⟨h, h4.1⟩]
  · rintro (h | h)
    exacts [h.1, h.1]

include hM in
theorem disjoint_sphereThree_sphereFour (v : CVert) :
    Disjoint (sphereThree v) (sphereFour v) := by
  rw [Set.disjoint_left]
  intro w h3 h4
  exact (labelFour_iff_not_labelThree hM h3.1).1 h4.2 h3.2

theorem exists_mem_sphere_of_path {t : CVert × CVert × CVert} (ht : IsDistTwoPath t)
    (v : CVert) : ∃ w, cgraph.dist v w = 2 ∧ (LabelThree v w ↔ LabelThree t.1 t.2.2) := by
  obtain ⟨s, hs⟩ := cvMul_transitive t.1 v
  refine ⟨cvMul t.2.2 s, ?_, ?_⟩
  · rw [← hs]
    exact dist_eq_two_cvMul ht.2.2 s
  · rw [← hs]
    exact labelThree_cvMul _ _ s

include hM in
theorem sphereThree_nonempty (v : CVert) : (sphereThree v).Nonempty := by
  obtain ⟨t, ht, h3⟩ := exists_path_labelThree hM
  obtain ⟨w, hd, h⟩ := exists_mem_sphere_of_path ht v
  exact ⟨w, hd, h.2 h3⟩

include hM in
theorem sphereFour_nonempty (v : CVert) : (sphereFour v).Nonempty := by
  obtain ⟨t, ht, h4⟩ := exists_path_labelFour hM
  obtain ⟨w, hd, h⟩ := exists_mem_sphere_of_path ht v
  exact ⟨w, hd, (labelFour_iff_not_labelThree hM hd).2 fun h3 => h4 (h.1 h3)⟩

include hM in
theorem sphereThree_ne_sphereFour (v : CVert) : sphereThree v ≠ sphereFour v := by
  intro h
  obtain ⟨w, hw⟩ := sphereThree_nonempty hM v
  have hw4 : w ∈ sphereFour v := h ▸ hw
  exact Set.disjoint_left.1 (disjoint_sphereThree_sphereFour hM v) hw hw4

include hM in
theorem setOf_vStabOrbit_eq (v : CVert) :
    {O | ∃ w, cgraph.dist v w = 2 ∧ O = vStabOrbit v w} = {sphereThree v, sphereFour v} := by
  ext O
  simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨w, hw, rfl⟩
    have hw' : w ∈ sphereThree v ∪ sphereFour v := by
      rw [← setOf_dist_eq_two_eq_union hM]
      exact hw
    rcases hw' with h3 | h4
    exacts [Or.inl (vStabOrbit_eq_sphereThree hM h3), Or.inr (vStabOrbit_eq_sphereFour hM h4)]
  · rintro (rfl | rfl)
    · obtain ⟨w, hw⟩ := sphereThree_nonempty hM v
      exact ⟨w, hw.1, (vStabOrbit_eq_sphereThree hM hw).symm⟩
    · obtain ⟨w, hw⟩ := sphereFour_nonempty hM v
      exact ⟨w, hw.1, (vStabOrbit_eq_sphereFour hM hw).symm⟩

include hM in
theorem exists_smul_eq_commonNeighbor {v w u u' : CVert} (hd : cgraph.dist v w = 2)
    (hu : u ∈ cgraph.commonNeighbors v w) (hu' : u' ∈ cgraph.commonNeighbors v w) :
    ∃ s : Shat, cvMul v s = v ∧ cvMul w s = w ∧ cvMul u s = u' := by
  obtain ⟨s, h1, h2, h3⟩ :=
    exists_smul_eq_path hM hu.1.symm hu.2.symm hd hu'.1.symm hu'.2.symm hd Iff.rfl
  exact ⟨s, h1, h3, h2⟩

theorem commonNeighbors_cvMul (v w : CVert) (s : Shat) :
    cgraph.commonNeighbors (cvMul v s) (cvMul w s) =
      (fun x => cvMul x s) '' cgraph.commonNeighbors v w := by
  ext x
  constructor
  · intro hx
    refine ⟨cvMul x s⁻¹, ⟨?_, ?_⟩, cvMul_inv_cancel' x s⟩
    · exact (cgraph_adj_cvMul v _ s).1 (by rw [cvMul_inv_cancel']; exact hx.1)
    · exact (cgraph_adj_cvMul w _ s).1 (by rw [cvMul_inv_cancel']; exact hx.2)
  · rintro ⟨y, ⟨h1, h2⟩, rfl⟩
    exact ⟨(cgraph_adj_cvMul v y s).2 h1, (cgraph_adj_cvMul w y s).2 h2⟩

include hM in
theorem ncard_commonNeighbors_eq {v w v' w' : CVert} (hd : cgraph.dist v w = 2)
    (hd' : cgraph.dist v' w' = 2) (h : LabelThree v w ↔ LabelThree v' w') :
    (cgraph.commonNeighbors v w).ncard = (cgraph.commonNeighbors v' w').ncard := by
  obtain ⟨-, -, u, hvu, huw⟩ := cgraph_dist_eq_two_iff.1 hd
  obtain ⟨-, -, u', hvu', huw'⟩ := cgraph_dist_eq_two_iff.1 hd'
  obtain ⟨s, hsv, -, hsw⟩ := exists_smul_eq_path hM hvu.symm huw hd hvu'.symm huw' hd' h
  rw [← hsv, ← hsw, commonNeighbors_cvMul,
    Set.ncard_image_of_injective _ (cvMul_injective s)]

theorem ncard_commonNeighbors_pos {v w : CVert} (hd : cgraph.dist v w = 2) :
    0 < (cgraph.commonNeighbors v w).ncard := by
  obtain ⟨-, -, u, hvu, huw⟩ := cgraph_dist_eq_two_iff.1 hd
  exact (Set.ncard_pos (Set.toFinite _)).2 ⟨u, hvu, huw.symm⟩

theorem natCard_sigma_const {α : Type*} [Finite α] {β : α → Type*} [∀ a, Finite (β a)] {m : ℕ}
    (h : ∀ a, Nat.card (β a) = m) : Nat.card (Σ a, β a) = Nat.card α * m := by
  have := Fintype.ofFinite α
  rw [Nat.card_sigma, Finset.sum_congr rfl fun a _ => h a, Finset.sum_const, Finset.card_univ,
    smul_eq_mul, Nat.card_eq_fintype_card]

theorem natCard_paths_eq_end (v : CVert) (P : CVert → Prop) {μ : ℕ}
    (hμ : ∀ w, P w → (cgraph.commonNeighbors v w).ncard = μ) :
    Nat.card {p : CVert × CVert // p.1 ∈ cgraph.commonNeighbors v p.2 ∧ P p.2} =
      Nat.card {w // P w} * μ := by
  have e : {p : CVert × CVert // p.1 ∈ cgraph.commonNeighbors v p.2 ∧ P p.2} ≃
      Σ w : {w // P w}, cgraph.commonNeighbors v w :=
    { toFun := fun p => ⟨⟨p.1.2, p.2.2⟩, ⟨p.1.1, p.2.1⟩⟩
      invFun := fun x => ⟨(x.2.1, x.1.1), x.2.2, x.1.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e]
  exact natCard_sigma_const fun w => by rw [Nat.card_coe_set_eq, hμ w w.2]

theorem natCard_paths_eq_mid (v : CVert) (P : CVert → Prop) {m : ℕ}
    (hm : ∀ u, cgraph.Adj v u → Nat.card {w // cgraph.Adj u w ∧ P w} = m) :
    Nat.card {p : CVert × CVert // p.1 ∈ cgraph.commonNeighbors v p.2 ∧ P p.2} =
      Nat.card (cgraph.neighborSet v) * m := by
  have e : {p : CVert × CVert // p.1 ∈ cgraph.commonNeighbors v p.2 ∧ P p.2} ≃
      Σ u : cgraph.neighborSet v, {w // cgraph.Adj u w ∧ P w} :=
    { toFun := fun p => ⟨⟨p.1.1, p.2.1.1⟩, ⟨p.1.2, p.2.1.2.symm, p.2.2⟩⟩
      invFun := fun x => ⟨(x.1.1, x.2.1), ⟨x.1.2, x.2.2.1.symm⟩, x.2.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e]
  exact natCard_sigma_const fun u => hm u u.2

theorem natCard_neighborSet_eq (v : CVert) :
    Nat.card (cgraph.neighborSet v) = Nat.card (cgraph.neighborSet cv0) := by
  obtain ⟨s, rfl⟩ := cvMul_transitive cv0 v
  have e : cgraph.neighborSet (cvMul cv0 s) = (fun x => cvMul x s) '' cgraph.neighborSet cv0 := by
    ext x
    constructor
    · intro hx
      refine ⟨cvMul x s⁻¹, (cgraph_adj_cvMul cv0 _ s).1 ?_, cvMul_inv_cancel' x s⟩
      rw [cvMul_inv_cancel']
      exact hx
    · rintro ⟨y, hy, rfl⟩
      exact (cgraph_adj_cvMul cv0 y s).2 hy
  rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq, e,
    Set.ncard_image_of_injective _ (cvMul_injective s)]

include hM in
theorem natCard_adj_sphereThree {v u : CVert} (hvu : cgraph.Adj v u) :
    Nat.card {w // cgraph.Adj u w ∧ w ∈ sphereThree v} = 2097152 := by
  obtain ⟨M, hL⟩ := hM u
  have e : {w // cgraph.Adj u w ∧ w ∈ sphereThree v} ≃
      {w : cgraph.neighborSet u // orbSize (M.pt ⟨v, hvu.symm⟩) (M.pt w) = repSize 4} :=
    { toFun := fun w =>
        ⟨⟨w.1, w.2.1⟩, (M.labelThree_dist_iff hL ⟨v, hvu.symm⟩ ⟨w.1, w.2.1⟩).1 w.2.2⟩
      invFun := fun w => ⟨w.1.1, w.1.2, (M.labelThree_dist_iff hL ⟨v, hvu.symm⟩ w.1).2 w.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e, M.natCard_orbSize_eq]
  rfl

include hM in
theorem natCard_adj_sphereFour {v u : CVert} (hvu : cgraph.Adj v u) :
    Nat.card {w // cgraph.Adj u w ∧ w ∈ sphereFour v} = 1824768 := by
  obtain ⟨M, hL⟩ := hM u
  have e : {w // cgraph.Adj u w ∧ w ∈ sphereFour v} ≃
      {w : cgraph.neighborSet u // orbSize (M.pt ⟨v, hvu.symm⟩) (M.pt w) = repSize 3} :=
    { toFun := fun w =>
        ⟨⟨w.1, w.2.1⟩, (M.labelFour_dist_iff hL ⟨v, hvu.symm⟩ ⟨w.1, w.2.1⟩).1 w.2.2⟩
      invFun := fun w => ⟨w.1.1, w.1.2, (M.labelFour_dist_iff hL ⟨v, hvu.symm⟩ w.1).2 w.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e, M.natCard_orbSize_eq]
  rfl

include hM in
theorem ncard_sphereThree_mul (hval : Nat.card (cgraph.neighborSet cv0) = 3968055) (v : CVert)
    {μ : ℕ} (hμ : ∀ w ∈ sphereThree v, (cgraph.commonNeighbors v w).ncard = μ) :
    (sphereThree v).ncard * μ = 3968055 * 2097152 := by
  have h1 := natCard_paths_eq_end v (· ∈ sphereThree v) hμ
  rw [natCard_paths_eq_mid v (· ∈ sphereThree v) fun u hu => natCard_adj_sphereThree hM hu,
    natCard_neighborSet_eq, hval] at h1
  rw [← Nat.card_coe_set_eq]
  exact h1.symm

include hM in
theorem ncard_sphereFour_mul (hval : Nat.card (cgraph.neighborSet cv0) = 3968055) (v : CVert)
    {μ : ℕ} (hμ : ∀ w ∈ sphereFour v, (cgraph.commonNeighbors v w).ncard = μ) :
    (sphereFour v).ncard * μ = 3968055 * 1824768 := by
  have h1 := natCard_paths_eq_end v (· ∈ sphereFour v) hμ
  rw [natCard_paths_eq_mid v (· ∈ sphereFour v) fun u hu => natCard_adj_sphereFour hM hu,
    natCard_neighborSet_eq, hval] at h1
  rw [← Nat.card_coe_set_eq]
  exact h1.symm

end Global

end CFSG.Monster.B.TwoA.Amalgam
