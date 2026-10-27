module

public import CFSG.Perm.OrbitTree
import Mathlib.Order.Interval.Set.Nat

public section

namespace CFSG.Monster.B.TwoA.Census

structure NatCert where
  pts : Array ℕ
  edges : Array (Array ℕ)
  par : Array ℕ
  lab : Array ℕ

@[expose] def natPointOK (act : ℕ → ℕ → ℕ) (ngen : ℕ) (valid : ℕ → Bool) (c : NatCert)
    (i : ℕ) : Bool :=
  valid c.pts[i]! && (c.edges[i]!).size == ngen &&
    (List.range ngen).all (fun k => decide (c.edges[i]![k]! < c.pts.size) &&
      c.pts[c.edges[i]![k]!]! == act k c.pts[i]!) &&
    (i == 0 || (decide (c.par[i]! < i) && decide (c.lab[i]! < ngen) &&
      c.pts[i]! == act c.lab[i]! c.pts[c.par[i]!]!))

@[expose] def natCertOK (act : ℕ → ℕ → ℕ) (ngen : ℕ) (valid : ℕ → Bool) (root : ℕ)
    (c : NatCert) : Bool :=
  decide (0 < c.pts.size) && c.pts[0]! == root &&
    (List.range c.pts.size).all (natPointOK act ngen valid c) &&
    (c.pts.toList.mergeSort (fun a b => decide (a ≤ b))).Pairwise (· < ·)

@[expose] def natBfsStep (act : ℕ → ℕ → ℕ) (ngen : ℕ) (i : ℕ)
    (st : Array ℕ × Array ℕ × Array ℕ × Std.HashMap ℕ ℕ) :
    Array ℕ × Array ℕ × Array ℕ × Std.HashMap ℕ ℕ × Array ℕ :=
  (List.range ngen).foldl (fun (acc : Array ℕ × Array ℕ × Array ℕ × Std.HashMap ℕ ℕ ×
      Array ℕ) k =>
    let (pts, par, lab, idx, row) := acc
    let y := act k pts[i]!
    match idx.get? y with
    | some j => (pts, par, lab, idx, row.push j)
    | none => (pts.push y, par.push i, lab.push k, idx.insert y pts.size, row.push pts.size))
    (st.1, st.2.1, st.2.2.1, st.2.2.2, #[])

@[expose] def natBfsLoop (act : ℕ → ℕ → ℕ) (ngen : ℕ) :
    ℕ → ℕ → Array ℕ → Array (Array ℕ) → Array ℕ → Array ℕ → Std.HashMap ℕ ℕ → NatCert
  | 0, _, pts, edges, par, lab, _ => ⟨pts, edges, par, lab⟩
  | fuel + 1, i, pts, edges, par, lab, idx =>
    if i < pts.size then
      let (pts', par', lab', idx', row) := natBfsStep act ngen i (pts, par, lab, idx)
      natBfsLoop act ngen fuel (i + 1) pts' (edges.push row) par' lab' idx'
    else ⟨pts, edges, par, lab⟩

@[expose] def natBfs (act : ℕ → ℕ → ℕ) (ngen : ℕ) (root : ℕ) (fuel : ℕ) : NatCert :=
  natBfsLoop act ngen fuel 0 #[root] #[] #[0] #[0] ((∅ : Std.HashMap ℕ ℕ).insert root 0)

section Soundness

variable {act : ℕ → ℕ → ℕ} {ngen : ℕ} {valid : ℕ → Bool} {root : ℕ} {c : NatCert}

theorem natCertOK_pointOK (h : natCertOK act ngen valid root c = true) {i : ℕ}
    (hi : i < c.pts.size) : natPointOK act ngen valid c i = true := by
  simp only [natCertOK, Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  exact h.1.2 i hi

theorem natCertOK_pos (h : natCertOK act ngen valid root c = true) : 0 < c.pts.size := by
  simp only [natCertOK, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1.1

theorem natCertOK_root (h : natCertOK act ngen valid root c = true) : c.pts[0]! = root := by
  simp only [natCertOK, Bool.and_eq_true, beq_iff_eq] at h
  exact h.1.1.2

theorem natCertOK_valid (h : natCertOK act ngen valid root c = true) {i : ℕ}
    (hi : i < c.pts.size) : valid c.pts[i]! = true := by
  have := natCertOK_pointOK h hi
  simp only [natPointOK, Bool.and_eq_true] at this
  exact this.1.1.1

theorem natCertOK_edge (h : natCertOK act ngen valid root c = true) {i : ℕ}
    (hi : i < c.pts.size) {k : ℕ} (hk : k < ngen) :
    c.edges[i]![k]! < c.pts.size ∧ c.pts[c.edges[i]![k]!]! = act k c.pts[i]! := by
  have := natCertOK_pointOK h hi
  simp only [natPointOK, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq,
    beq_iff_eq] at this
  exact this.1.2 k hk

theorem natCertOK_tree (h : natCertOK act ngen valid root c = true) {i : ℕ} (hi0 : 0 < i)
    (hi : i < c.pts.size) :
    c.par[i]! < i ∧ c.lab[i]! < ngen ∧ c.pts[i]! = act c.lab[i]! c.pts[c.par[i]!]! := by
  have := natCertOK_pointOK h hi
  simp only [natPointOK, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at this
  rcases this.2 with h0 | ⟨⟨hp, hl⟩, e⟩
  · omega
  · exact ⟨hp, hl, e⟩

theorem natCertOK_inj (h : natCertOK act ngen valid root c = true) {i j : ℕ}
    (hi : i < c.pts.size) (hj : j < c.pts.size) (hij : c.pts[i]! = c.pts[j]!) : i = j := by
  simp only [natCertOK, Bool.and_eq_true] at h
  have hnd : c.pts.toList.Nodup := by
    have hp := List.mergeSort_perm c.pts.toList (fun a b => decide (a ≤ b))
    exact hp.nodup_iff.1 (List.Pairwise.imp (fun h' => ne_of_lt h') (of_decide_eq_true h.2))
  have hgi : c.pts.toList[i]'(by simpa using hi) = c.pts[i]! := by
    simp [getElem!_pos c.pts i hi]
  have hgj : c.pts.toList[j]'(by simpa using hj) = c.pts[j]! := by
    simp [getElem!_pos c.pts j hj]
  exact (List.Nodup.getElem_inj_iff hnd).1 (hgi.trans (hij.trans hgj.symm))

end Soundness

section Action

variable {G X : Type*} [Group G] [MulAction G X] {act : ℕ → ℕ → ℕ} {ngen : ℕ}
  {valid : ℕ → Bool} {root : ℕ} {c : NatCert} {dec : ℕ → X} {gens : ℕ → G}

theorem natCertOK_closed (h : natCertOK act ngen valid root c = true)
    (hact : ∀ k < ngen, ∀ a, valid a = true → dec (act k a) = gens k • dec a)
    {i : ℕ} (hi : i < c.pts.size) {s : G} (hs : s ∈ gens '' {k | k < ngen}) :
    ∃ j < c.pts.size, dec c.pts[j]! = s • dec c.pts[i]! := by
  obtain ⟨k, hk, rfl⟩ := hs
  obtain ⟨hj, e⟩ := natCertOK_edge h hi hk
  exact ⟨_, hj, by rw [e, hact k hk _ (natCertOK_valid h hi)]⟩

theorem natCertOK_treeWord (h : natCertOK act ngen valid root c = true)
    (hact : ∀ k < ngen, ∀ a, valid a = true → dec (act k a) = gens k • dec a)
    {i : ℕ} (hi : i < c.pts.size) :
    CFSG.Perm.treeWord (fun i => c.par[i]!) (fun i => c.lab[i]!) gens i • dec c.pts[0]! =
        dec c.pts[i]! ∧
      CFSG.Perm.treeWord (fun i => c.par[i]!) (fun i => c.lab[i]!) gens i ∈
        Subgroup.closure (gens '' {k | k < ngen}) := by
  refine ⟨CFSG.Perm.treeWord_smul (n := c.pts.size) (P := fun i => dec c.pts[i]!)
    (fun i h0 hi => (natCertOK_tree h h0 hi).1) (fun i h0 hi => ?_) hi,
    CFSG.Perm.treeWord_mem (n := c.pts.size) (fun i h0 hi => (natCertOK_tree h h0 hi).1)
      (fun i h0 hi => Subgroup.subset_closure
        (Set.mem_image_of_mem gens (natCertOK_tree h h0 hi).2.1)) hi⟩
  obtain ⟨hp, hl, e⟩ := natCertOK_tree h h0 hi
  show dec c.pts[i]! = gens c.lab[i]! • dec c.pts[c.par[i]!]!
  rw [e, hact _ hl _ (natCertOK_valid h (hp.trans hi))]

theorem orbit_of_natCertOK (h : natCertOK act ngen valid root c = true)
    (hact : ∀ k < ngen, ∀ a, valid a = true → dec (act k a) = gens k • dec a) :
    MulAction.orbit (Subgroup.closure (gens '' {k | k < ngen})) (dec root) =
      (fun i => dec c.pts[i]!) '' {i | i < c.pts.size} := by
  have h0 : dec c.pts[0]! = dec root := by rw [natCertOK_root h]
  rw [← h0]
  exact CFSG.Perm.orbit_closure_eq_image (P := fun i => dec c.pts[i]!) (natCertOK_pos h)
    (fun i hi s hs => natCertOK_closed h hact hi hs)
    (τ := CFSG.Perm.treeWord (fun i => c.par[i]!) (fun i => c.lab[i]!) gens)
    (fun i hi => (natCertOK_treeWord h hact hi).2) (fun i hi => (natCertOK_treeWord h hact hi).1)

theorem ncard_orbit_of_natCertOK (h : natCertOK act ngen valid root c = true)
    (hact : ∀ k < ngen, ∀ a, valid a = true → dec (act k a) = gens k • dec a)
    (hinj : ∀ a b, valid a = true → valid b = true → dec a = dec b → a = b) :
    (MulAction.orbit (Subgroup.closure (gens '' {k | k < ngen})) (dec root)).ncard =
      c.pts.size := by
  rw [orbit_of_natCertOK h hact,
    Set.InjOn.ncard_image (s := {i | i < c.pts.size}) (f := fun i => dec c.pts[i]!)
      (fun i hi j hj e => natCertOK_inj h hi hj
        (hinj _ _ (natCertOK_valid h hi) (natCertOK_valid h hj) e))]
  exact Set.ncard_Iio_nat _

end Action

end CFSG.Monster.B.TwoA.Census
