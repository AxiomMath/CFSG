module

public import CFSG.LocalAnalysis.StandardType.GGK0LQDefs
public import CFSG.LocalAnalysis.StandardType.GGK0LQExt
public import CFSG.LocalAnalysis.StandardType.GGKacCompsSpec

public section

namespace CFSG.StandardType.GGK0LQ

open CFSG CFSG.Assembly CFSG.StandardType CFSG.StandardType.GGK0MarkedKacIface1587
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus

variable {Omega : Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
  {lab : LargeEvenLabel} {p : ℕ} {R : Type} [Group R] {I : Set (MulAut R)} {phi : MulAut R}

private lemma lk0xlqnodes_diagOf_marks_length (T : GGKacType) :
    (k0DiagOf T).marks.length = (absTag T).rank + 1 := by
  cases T <;> rfl

private lemma lk0xlqnodes_marks_length (A : K0LangMark Omega lab p R I phi) :
    A.row.diagram.marks.length = A.tau.rank + 1 := by
  rw [← A.tau_eq]
  exact lk0xlqnodes_diagOf_marks_length A.row.T

private lemma lk0xlqnodes_mark_zero (T : GGKacType) :
    (k0DiagOf T).marks.getD 0 0 = 1 := by
  cases T <;> rfl

private lemma lk0xlqnodes_insertBy_length {α : Type} (le : α → α → Bool) (a : α) (l : List α) :
    (k0InsertBy le a l).length = l.length + 1 := by
  induction l with
  | nil => simp [k0InsertBy]
  | cons b bs ih =>
      rw [k0InsertBy]
      split <;> simp [ih]

private lemma lk0xlqnodes_sortNat_length (l : List ℕ) :
    (k0SortNat l).length = l.length := by
  induction l with
  | nil => simp [k0SortNat, k0SortBy]
  | cons a as ih =>
      rw [k0SortNat] at ih
      rw [k0SortNat, k0SortBy, lk0xlqnodes_insertBy_length, ih]
      rfl

private lemma lk0xlqnodes_pairwise_lt_nodup {l : List ℕ} (h : l.Pairwise (· < ·)) :
    l.Nodup := by
  induction l with
  | nil => exact List.nodup_nil
  | cons a as ih =>
      rw [List.pairwise_cons] at h
      obtain ⟨hhd, htl⟩ := h
      exact List.nodup_cons.mpr ⟨fun ha => Nat.lt_irrefl a (hhd a ha), ih htl⟩

private lemma lk0xlqnodes_pi_eq_sum_single (n : ℕ) (v : Fin n → ℤ) :
    v = ∑ i : Fin n, v i • (Pi.single i 1 : Fin n → ℤ) := by
  funext k
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, Pi.single_apply, smul_eq_mul]
  rw [Finset.sum_eq_single k]
  · simp
  · intro b _ hbk
    simp [Ne.symm hbk]
  · intro hk
    exact absurd (Finset.mem_univ k) hk

private lemma lk0xlqnodes_nodeMap_weighted_zero (A : K0LangMark Omega lab p R I phi) :
    (∑ i : Fin A.row.diagram.marks.length,
      (A.row.diagram.marks.getD i.val 0 : ℤ) • A.nodeMap (Pi.single i 1)) = 0 := by
  let mv : Fin A.row.diagram.marks.length → ℤ := fun i =>
    (A.row.diagram.marks.getD i.val 0 : ℤ)
  change (∑ i : Fin A.row.diagram.marks.length, mv i • A.nodeMap (Pi.single i 1)) = 0
  have hmem : mv ∈ A.nodeMap.ker := by
    rw [A.nodeMap_ker]
    exact Submodule.subset_span (Set.mem_singleton mv)
  have hdecomp : mv = ∑ i, mv i • (Pi.single i 1 : Fin A.row.diagram.marks.length → ℤ) :=
    lk0xlqnodes_pi_eq_sum_single _ mv
  have hmap : A.nodeMap
      (∑ i, mv i • (Pi.single i 1 : Fin A.row.diagram.marks.length → ℤ)) =
      ∑ i, mv i • A.nodeMap (Pi.single i 1) := by
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => map_smul _ _ _
  rw [← hmap, ← hdecomp]
  exact LinearMap.mem_ker.1 hmem

private lemma lk0xlqnodes_go_head (img : List ℕ → List ℕ) (c : List ℕ) :
    ∀ (f : ℕ) (cur : List ℕ) (acc : List (List ℕ)), acc ≠ [] → acc.headD [] = c →
      (k0CompOrbit.go img c f cur acc).headD [] = c := by
  intro f
  induction f with
  | zero => intro cur acc _ h; exact h
  | succ f ih =>
      intro cur acc hne h
      simp only [k0CompOrbit.go]
      split
      · exact h
      · refine ih (img cur) (acc ++ [cur]) ?_ ?_
        · cases acc with
          | nil => exact absurd rfl hne
          | cons a as => simp
        · cases acc with
          | nil => exact absurd rfl hne
          | cons a as =>
              simp only [List.headD_cons] at h ⊢
              exact h

private lemma lk0xlqnodes_compOrbit_head (img : List ℕ → List ℕ) (fuel : ℕ) (c : List ℕ) :
    (k0CompOrbit img fuel c).headD [] = c := by
  unfold k0CompOrbit
  exact lk0xlqnodes_go_head img c fuel (img c) [c] (by simp) rfl

private lemma lk0xlqnodes_head_mem_comps (img : List ℕ → List ℕ) (fuel : ℕ) :
    ∀ (cs seen : List (List ℕ)) (orb : List (List ℕ)),
      orb ∈ k0CompOrbits img fuel cs seen → orb.headD [] ∈ cs := by
  intro cs
  induction cs with
  | nil => intro seen orb h; simp [k0CompOrbits] at h
  | cons c rest ih =>
      intro seen orb h
      simp only [k0CompOrbits] at h
      split at h
      · exact List.mem_cons_of_mem _ (ih seen orb h)
      · simp only [List.mem_cons] at h
        rcases h with rfl | h
        · rw [lk0xlqnodes_compOrbit_head]; exact List.mem_cons_self ..
        · exact List.mem_cons_of_mem _ (ih (seen ++ k0CompOrbit img fuel c) orb h)

private lemma lk0xlqnodes_orbit_mem (A : K0LangMark Omega lab p R I phi) (P : K0Positions A)
    (j : Fin A.row.D.orbits.length) :
    P.orbitNodes j ∈ k0CompOrbits (fun c => k0SortNat (c.map (fun i => A.row.rho.getD i 0)))
      ((k0DiagOf A.row.T).marks.length + 1)
      (k0Comps (k0DiagOf A.row.T) ((List.range (k0DiagOf A.row.T).marks.length).filter
        (fun i => decide (A.row.s.getD i 0 = 0)))) [] := by
  have hmem0 : P.orbitNodes j ∈ A.row.rawComponentOrbits :=
    (List.Perm.mem_iff P.orbitNodes_perm).mp (List.mem_ofFn.mpr ⟨j, rfl⟩)
  exact hmem0

theorem lq_nodes_mem_comps (A : K0LangMark Omega lab p R I phi) (P : K0Positions A)
    (j : Fin A.row.D.orbits.length) :
    (P.orbitNodes j).headD [] ∈
      k0Comps (k0DiagOf A.row.T) ((List.range (k0DiagOf A.row.T).marks.length).filter
        (fun i => decide (A.row.s.getD i 0 = 0))) :=
  lk0xlqnodes_head_mem_comps _ _ _ _ _ (lk0xlqnodes_orbit_mem A P j)

private lemma lk0xlqnodes_eqvGen_restrict {D : K0Diag} {zero l : List ℕ} {i : ℕ}
    (hC : ∀ a, Relation.EqvGen (fun a b => a ∈ zero ∧ b ∈ zero ∧ 0 < D.adj a b) i a → a ∈ l) :
    ∀ {a b : ℕ},
      Relation.EqvGen (fun a b => a ∈ zero ∧ b ∈ zero ∧ 0 < D.adj a b) a b →
      Relation.EqvGen (fun a b => a ∈ zero ∧ b ∈ zero ∧ 0 < D.adj a b) i a →
      Relation.EqvGen (fun a b => a ∈ l ∧ b ∈ l ∧ 0 < D.adj a b) a b := by
  intro a b hab
  refine Relation.EqvGen.rec (motive := fun a b _ =>
      Relation.EqvGen (fun a b => a ∈ zero ∧ b ∈ zero ∧ 0 < D.adj a b) i a →
      Relation.EqvGen (fun a b => a ∈ l ∧ b ∈ l ∧ 0 < D.adj a b) a b) ?_ ?_ ?_ ?_ hab
  · intro x y hxy hix
    have hiy : Relation.EqvGen (fun a b => a ∈ zero ∧ b ∈ zero ∧ 0 < D.adj a b) i y :=
      Relation.EqvGen.trans _ _ _ hix (Relation.EqvGen.rel x y hxy)
    exact Relation.EqvGen.rel x y ⟨hC x hix, hC y hiy, hxy.2.2⟩
  · intro x _; exact Relation.EqvGen.refl x
  · intro x y h ih hiy
    have hix : Relation.EqvGen (fun a b => a ∈ zero ∧ b ∈ zero ∧ 0 < D.adj a b) i x :=
      Relation.EqvGen.trans _ _ _ hiy (Relation.EqvGen.symm x y h)
    exact Relation.EqvGen.symm x y (ih hix)
  · intro x y z h1 h2 ih1 ih2 hix
    have hiy : Relation.EqvGen (fun a b => a ∈ zero ∧ b ∈ zero ∧ 0 < D.adj a b) i y :=
      Relation.EqvGen.trans _ _ _ hix h1
    exact Relation.EqvGen.trans x y z (ih1 hix) (ih2 hiy)

private lemma lk0xlqnodes_reach_pair {D : K0Diag} {x y : ℕ} (hxy : x ≠ y) :
    y ∈ k0Reach D [x, y] false x 0 → 0 < D.adj x y := by
  by_cases hadj : 0 < D.adj x y
  · exact fun _ => hadj
  · intro hy
    have hyx : y = x := by simpa [k0Reach, k0ReachAux, hadj] using hy
    exact absurd hyx.symm hxy

private lemma lk0xlqnodes_compType_singleton (D : K0Diag) (x : ℕ) :
    k0CompType D [x] = (.A, 1) := by
  simp [k0CompType, k0SortNat, k0SortBy, k0InsertBy]

private lemma lk0xlqnodes_compType_single_len (D : K0Diag) (l : List ℕ) (h : l.length = 1) :
    k0CompType D l = (.A, 1) := by
  match l with
  | [] => simp at h
  | [x] => exact lk0xlqnodes_compType_singleton D x
  | _ :: _ :: _ => simp at h

private lemma lk0xlqnodes_label_qs_false_iff (fam : LargeEvenLieTag) (r tw n : ℕ) :
    (k0LabelOf fam r tw n).qs = false ↔
      fam = .A ∧ ((tw = 1 ∧ r = 1) ∨ (tw ≠ 1 ∧ r = 2)) ∧ n = 1 := by
  cases fam <;> simp only [k0LabelOf] <;> (try split_ifs) <;>
    simp_all [decide_eq_false_iff_not]

theorem lq_descriptor_eq (A : K0LangMark Omega lab p R I phi) (P : K0Positions A)
    (j : Fin A.row.D.orbits.length) :
    A.row.D.orbits[j] =
      k0LabelOf (k0CompType (k0DiagOf A.row.T) (lqNodes A P j)).1
        (k0CompType (k0DiagOf A.row.T) (lqNodes A P j)).2 (lqTw A P j)
        ((P.orbitNodes j).length * lab.n) := by
  rw [P.orbit_descriptor j]
  rfl

theorem lq_qpow (A : K0LangMark Omega lab p R I phi) (P : K0Positions A)
    (j : Fin A.row.D.orbits.length) :
    A.setup.D.q ^ componentOrbitLength A.setup.ρ (componentRoots (rootCharHom A.a) (P.repr j)) =
      2 ^ A.row.D.orbits[j].lab.n := by
  rw [P.orbit_length j, A.q_eq, P.field_exp j, ← pow_mul,
    Nat.mul_comm lab.n ((P.orbitNodes j).length)]

theorem lq_nodes_basic (A : K0LangMark Omega lab p R I phi) (P : K0Positions A)
    (j : Fin A.row.D.orbits.length) :
    lqNodes A P j ≠ [] ∧ (lqNodes A P j).Nodup ∧
      ∀ x ∈ lqNodes A P j, x < A.tau.rank + 1 ∧ A.row.s.getD x 0 = 0 := by
  have hzero_nd : ((List.range (k0DiagOf A.row.T).marks.length).filter
      (fun i => decide (A.row.s.getD i 0 = 0))).Nodup :=
    (List.nodup_range).filter _
  have hmem : lqNodes A P j ∈ k0Comps (k0DiagOf A.row.T)
      ((List.range (k0DiagOf A.row.T).marks.length).filter
        (fun i => decide (A.row.s.getD i 0 = 0))) := by
    simpa only [lqNodes] using lq_nodes_mem_comps A P j
  have hspec := k0Comps_spec (k0DiagOf A.row.T) hzero_nd
  obtain ⟨hne, hpair, hsub⟩ := hspec.1 (lqNodes A P j) hmem
  have hlen := lk0xlqnodes_marks_length A
  refine ⟨hne, lk0xlqnodes_pairwise_lt_nodup hpair, ?_⟩
  intro x hx
  have hxz : x ∈ (List.range (k0DiagOf A.row.T).marks.length).filter
      (fun i => decide (A.row.s.getD i 0 = 0)) := hsub x hx
  rw [List.mem_filter] at hxz
  obtain ⟨hxr, hxd⟩ := hxz
  exact ⟨by rw [← hlen]; exact List.mem_range.mp hxr, of_decide_eq_true hxd⟩

theorem lq_nodeMap_eq (A : K0LangMark Omega lab p R I phi)
    (x : Fin A.row.diagram.marks.length) :
    A.nodeMap (Pi.single x 1) = lqExtRoot A.tau A.row.T x.val := by
  obtain ⟨n, hn⟩ := x
  match n with
  | 0 =>
      have hlen := lk0xlqnodes_marks_length A
      have hxval : (⟨0, hn⟩ : Fin A.row.diagram.marks.length).val = 0 := rfl
      rw [hxval]
      have hzero : (⟨0, hn⟩ : Fin A.row.diagram.marks.length) =
          Fin.cast hlen.symm (0 : Fin (A.tau.rank + 1)) := Fin.ext rfl
      rw [hzero]
      let mv : Fin A.row.diagram.marks.length → ℤ := fun i =>
        (A.row.diagram.marks.getD i.val 0 : ℤ)
      have hsum0 := lk0xlqnodes_nodeMap_weighted_zero (A := A)
      let F : Fin A.row.diagram.marks.length → (Fin A.tau.rank → ℤ) :=
        fun i => mv i • A.nodeMap (Pi.single i 1)
      have hreindex : (∑ i : Fin A.row.diagram.marks.length, F i) =
          ∑ i : Fin (A.tau.rank + 1), F (Fin.cast hlen.symm i) := by
        simpa [finCongr_apply] using
          (Equiv.sum_comp (finCongr hlen.symm) F).symm
      have hsumF : (∑ i : Fin A.row.diagram.marks.length, F i) = 0 := by
        simpa only [F, mv] using hsum0
      rw [Fin.sum_univ_succ] at hreindex
      have hsplit : F (Fin.cast hlen.symm 0) +
          ∑ i : Fin A.tau.rank, F (Fin.cast hlen.symm i.succ) = 0 := by
        rw [← hreindex]
        exact hsumF
      have hfirst : F (Fin.cast hlen.symm 0) =
          A.nodeMap (Pi.single (Fin.cast hlen.symm (0 : Fin (A.tau.rank + 1))) 1) := by
        simp only [F, mv]
        have h0 : (Fin.cast hlen.symm (0 : Fin (A.tau.rank + 1))).val = 0 := rfl
        rw [h0, lk0xlqnodes_mark_zero A.row.T]
        simp
      let th : Fin A.tau.rank → ℤ := fun j =>
        ((A.row.diagram.marks.getD (j.val + 1) 0 : ℕ) : ℤ)
      have htail : (∑ i : Fin A.tau.rank, F (Fin.cast hlen.symm i.succ)) = th := by
        have hterm : ∀ i : Fin A.tau.rank,
            F (Fin.cast hlen.symm i.succ) = th i • (Pi.single i 1 : Fin A.tau.rank → ℤ) := by
          intro i
          have hstd : A.nodeMap (Pi.single (Fin.cast hlen.symm i.succ) 1) = Pi.single i 1 :=
            A.node_std _ i rfl
          have hval : (Fin.cast hlen.symm i.succ).val = i.val + 1 := rfl
          simp only [F, mv, hstd, hval, th]
        rw [Finset.sum_congr rfl fun i _ => hterm i]
        exact (lk0xlqnodes_pi_eq_sum_single _ th).symm
      have hmain : A.nodeMap (Pi.single (Fin.cast hlen.symm (0 : Fin (A.tau.rank + 1))) 1) +
          th = 0 := by
        rw [← hfirst, ← htail]
        exact hsplit
      have hnode : A.nodeMap (Pi.single (Fin.cast hlen.symm (0 : Fin (A.tau.rank + 1))) 1) =
          -th := eq_neg_of_add_eq_zero_left hmain
      rw [hnode]
      funext j
      simp [lqExtRoot, Pi.neg_apply, th]
  | k + 1 =>
      have hk : k < A.tau.rank := by
        have := lk0xlqnodes_marks_length A
        omega
      have hroot : lqExtRoot A.tau A.row.T (k + 1) = Pi.single ⟨k, hk⟩ 1 := by
        funext j
        have hx0 : ¬ (k + 1 = 0) := by omega
        rw [lqExtRoot, if_neg hx0, Pi.single_apply]
        by_cases hj : j = ⟨k, hk⟩
        · subst hj; simp
        · have hne : j.val + 1 ≠ k + 1 := by
            intro h
            exact hj (Fin.ext (by show j.val = k; omega))
          rw [if_neg hne, if_neg hj]
      rw [hroot]
      exact A.node_std ⟨k + 1, hn⟩ ⟨k, hk⟩ rfl

theorem lq_qs_false_iff (A : K0LangMark Omega lab p R I phi) (P : K0Positions A)
    (j : Fin A.row.D.orbits.length) :
    A.row.D.orbits[j].qs = false ↔
      (k0CompType (k0DiagOf A.row.T) (lqNodes A P j)).1 = .A ∧
        ((lqTw A P j = 1 ∧ (k0CompType (k0DiagOf A.row.T) (lqNodes A P j)).2 = 1) ∨
          (lqTw A P j ≠ 1 ∧ (k0CompType (k0DiagOf A.row.T) (lqNodes A P j)).2 = 2)) ∧
        A.row.D.orbits[j].lab.n = 1 := by
  rw [lq_descriptor_eq A P j, lk0xlqnodes_label_qs_false_iff, k0LabelOf_lab_n]

theorem lq_compType_single (A : K0LangMark Omega lab p R I phi) (P : K0Positions A)
    (j : Fin A.row.D.orbits.length) (h : (lqNodes A P j).length = 1) :
    k0CompType (k0DiagOf A.row.T) (lqNodes A P j) = (.A, 1) := by
  exact lk0xlqnodes_compType_single_len (k0DiagOf A.row.T) (lqNodes A P j) h

theorem lq_orbit_n_pos (A : K0LangMark Omega lab p R I phi) (P : K0Positions A)
    (j : Fin A.row.D.orbits.length) (hn : 1 ≤ lab.n) : 1 ≤ A.row.D.orbits[j].lab.n := by
  rw [P.field_exp j]
  have hzero_nd : ((List.range (k0DiagOf A.row.T).marks.length).filter
      (fun i => decide (A.row.s.getD i 0 = 0))).Nodup :=
    (List.nodup_range).filter _
  have hmem := lq_nodes_mem_comps A P j
  have hne : (P.orbitNodes j).headD [] ≠ [] :=
    ((k0Comps_spec (k0DiagOf A.row.T) hzero_nd).1 ((P.orbitNodes j).headD []) hmem).1
  have horb_ne : P.orbitNodes j ≠ [] := by
    intro h
    exact hne (by simp [h])
  have hpos : 0 < (P.orbitNodes j).length := List.length_pos_iff.mpr horb_ne
  exact Nat.mul_pos hpos hn

theorem lq_compType_A_rank (D : K0Diag) (c : List ℕ) (h : (k0CompType D c).1 = .A) :
    (k0CompType D c).2 = c.length := by
  revert h
  unfold k0CompType
  dsimp only
  split
  · split
    · intro _
      exact lk0xlqnodes_sortNat_length c
    · split_ifs <;> (intro h; simp_all [lk0xlqnodes_sortNat_length])
  · split_ifs <;> (intro h; simp_all [lk0xlqnodes_sortNat_length])

theorem lq_compType_rank_ACD (D : K0Diag) (c : List ℕ)
    (h : (k0CompType D c).1 = .A ∨ (k0CompType D c).1 = .C ∨ (k0CompType D c).1 = .D) :
    (k0CompType D c).2 = c.length := by
  revert h
  unfold k0CompType
  dsimp only
  split
  · split
    · intro _
      exact lk0xlqnodes_sortNat_length c
    · split_ifs <;> (intro h; simp_all [lk0xlqnodes_sortNat_length])
  · split_ifs <;> (intro h; simp_all [lk0xlqnodes_sortNat_length])

theorem lq_pair_adj (A : K0LangMark Omega lab p R I phi) (P : K0Positions A)
    (j : Fin A.row.D.orbits.length) (h : (lqNodes A P j).length = 2) :
    ∃ x y : ℕ, lqNodes A P j = [x, y] ∧ x < y ∧ y < A.row.diagram.marks.length ∧
      0 < (k0DiagOf A.row.T).adj x y := by
  obtain ⟨x, y, hxy_eq⟩ := List.length_eq_two.mp h
  have hzero_nd : ((List.range (k0DiagOf A.row.T).marks.length).filter
      (fun i => decide (A.row.s.getD i 0 = 0))).Nodup :=
    (List.nodup_range).filter _
  have hmem : lqNodes A P j ∈ k0Comps (k0DiagOf A.row.T)
      ((List.range (k0DiagOf A.row.T).marks.length).filter
        (fun i => decide (A.row.s.getD i 0 = 0))) := by
    simpa only [lqNodes] using lq_nodes_mem_comps A P j
  have hspec := k0Comps_spec (k0DiagOf A.row.T) hzero_nd
  obtain ⟨_hne, hpair, hsub⟩ := hspec.1 (lqNodes A P j) hmem
  have hx_mem : x ∈ lqNodes A P j := by rw [hxy_eq]; simp
  have hy_mem : y ∈ lqNodes A P j := by rw [hxy_eq]; simp
  have hxy_lt : x < y := by
    have hp := hpair
    rw [hxy_eq] at hp
    simpa using hp
  have hx_ne : x ≠ y := Nat.ne_of_lt hxy_lt
  have hRxy : Relation.EqvGen (fun a b => a ∈ (List.range (k0DiagOf A.row.T).marks.length).filter
      (fun i => decide (A.row.s.getD i 0 = 0)) ∧
      b ∈ (List.range (k0DiagOf A.row.T).marks.length).filter
        (fun i => decide (A.row.s.getD i 0 = 0)) ∧ 0 < (k0DiagOf A.row.T).adj a b) x y :=
    (hspec.2.1 (lqNodes A P j) hmem x hx_mem y).1 hy_mem
  have hC : ∀ a, Relation.EqvGen (fun a b =>
        a ∈ (List.range (k0DiagOf A.row.T).marks.length).filter
          (fun i => decide (A.row.s.getD i 0 = 0)) ∧
        b ∈ (List.range (k0DiagOf A.row.T).marks.length).filter
          (fun i => decide (A.row.s.getD i 0 = 0)) ∧ 0 < (k0DiagOf A.row.T).adj a b) x a →
      a ∈ lqNodes A P j :=
    fun a ha => (hspec.2.1 (lqNodes A P j) hmem x hx_mem a).2 ha
  have hR' : Relation.EqvGen (fun a b => a ∈ lqNodes A P j ∧ b ∈ lqNodes A P j ∧
      0 < (k0DiagOf A.row.T).adj a b) x y :=
    lk0xlqnodes_eqvGen_restrict (D := k0DiagOf A.row.T) (zero :=
      (List.range (k0DiagOf A.row.T).marks.length).filter
        (fun i => decide (A.row.s.getD i 0 = 0))) (l := lqNodes A P j) (i := x) hC hRxy
      (Relation.EqvGen.refl x)
  have hnd_l : (lqNodes A P j).Nodup := lk0xlqnodes_pairwise_lt_nodup hpair
  have hy_reach : y ∈ k0Reach (k0DiagOf A.row.T) (lqNodes A P j) false x 0 :=
    ((k0Reach_spec (k0DiagOf A.row.T) hnd_l hx_mem).2 y).2 hR'
  rw [hxy_eq] at hy_reach
  have hadj : 0 < (k0DiagOf A.row.T).adj x y := lk0xlqnodes_reach_pair hx_ne hy_reach
  have hy_bound : y < (k0DiagOf A.row.T).marks.length := by
    have hyz := hsub y hy_mem
    rw [List.mem_filter] at hyz
    exact List.mem_range.mp hyz.1
  exact ⟨x, y, hxy_eq, hxy_lt, hy_bound, hadj⟩

end CFSG.StandardType.GGK0LQ

end
