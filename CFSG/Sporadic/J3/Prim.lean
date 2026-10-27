module

public import CFSG.Sporadic.J3.Chain

public section

namespace CFSG.Sporadic.J3

open Native CFSG.Sporadic.Th CFSG.Perm CFSG.Perm.Native
open CFSG.Sporadic.Th.Native (ap Table)
open scoped Pointwise

theorem isPreprimitive_of_label_closure {G X : Type*} [Group G] [MulAction G X]
    [MulAction.IsPretransitive G X] (x₀ : X) (H : Subgroup G) (hH : ∀ h ∈ H, h • x₀ = x₀)
    {k : ℕ} (lab : X → Fin k) (horb : ∀ p q : X, lab p = lab q → ∃ h ∈ H, h • p = q)
    (hroot : ∀ p, lab p = lab x₀ → p = x₀) (t : Fin k → G) (ht : ∀ i, lab (t i • x₀) = i)
    (hclos : ∀ c, c ≠ lab x₀ → ∀ S : Set (Fin k), lab x₀ ∈ S → c ∈ S →
      (∀ i ∈ S, ∀ y : X, lab y ∈ S → lab ((t i)⁻¹ • y) ∈ S) → ∀ i, i ∈ S) :
    MulAction.IsPreprimitive G X := by
  refine MulAction.IsPreprimitive.of_isTrivialBlock_base x₀ fun {B} hxB hB => ?_
  have hcl : ∀ p q : X, p ∈ B → lab p = lab q → q ∈ B := by
    intro p q hp hpq
    obtain ⟨h, hh, rfl⟩ := horb p q hpq
    have hhx : h • x₀ ∈ B := by rw [hH h hh]; exact hxB
    rw [← hB.smul_eq_of_mem hxB hhx]
    exact Set.smul_mem_smul_set hp
  by_cases hsub : B.Subsingleton
  · exact Or.inl hsub
  right
  obtain ⟨y, hyB, hyx⟩ : ∃ y ∈ B, y ≠ x₀ := by
    by_contra hcon
    push Not at hcon
    exact hsub fun p hp q hq => by rw [hcon p hp, hcon q hq]
  let S : Set (Fin k) := {i | ∃ p ∈ B, lab p = i}
  have hmemS : ∀ p, lab p ∈ S → p ∈ B := fun p ⟨q, hq, hqp⟩ => hcl q p hq hqp
  have hclosed : ∀ i ∈ S, ∀ z : X, lab z ∈ S → lab ((t i)⁻¹ • z) ∈ S := by
    intro i hi z hz
    have hti : t i • x₀ ∈ B := hmemS _ (by rw [ht]; exact hi)
    have hB' : (t i)⁻¹ • B = B := hB.smul_eq_of_mem hti (by rw [inv_smul_smul]; exact hxB)
    refine ⟨(t i)⁻¹ • z, ?_, rfl⟩
    rw [← hB']
    exact Set.smul_mem_smul_set (hmemS z hz)
  have hall := hclos (lab y) (fun e => hyx (hroot y e)) S ⟨x₀, hxB, rfl⟩ ⟨y, hyB, rfl⟩ hclosed
  ext p
  exact ⟨fun _ => Set.mem_univ p, fun _ => hmemS p (hall (lab p))⟩

theorem eq_true_of_set!_eq_true {A : Array Bool} {i j : ℕ} {v : Bool}
    (h : (A.set! i v)[j]! = true) : (i = j ∧ v = true) ∨ A[j]! = true := by
  rw [Array.set!_eq_setIfInBounds] at h
  by_cases hj : j < A.size
  · rw [getElem!_pos _ j (by simpa using hj), Array.getElem_setIfInBounds hj] at h
    split_ifs at h with hij
    · exact Or.inl ⟨hij, h⟩
    · right; rw [getElem!_pos A j hj]; exact h
  · rw [getElem!_neg _ j (by simpa using hj)] at h
    exact absurd h (by decide)

theorem replicate_false_getElem! {k j : ℕ} : (Array.replicate k false)[j]! = false := by
  by_cases hj : j < k
  · rw [getElem!_pos _ j (by simpa using hj), Array.getElem_replicate]
  · rw [getElem!_neg _ j (by simpa using hj)]
    rfl

section Deriv

variable {n : ℕ} {T : Tree} {L : Array Table} {reps labs : Array ℕ} {S : Set ℕ}

theorem derivStep_inv
    (hstep : ∀ i < reps.size, ∀ y < n, i ∈ S → labs[y]! ∈ S →
      invLabel T L labs (ap T.pos reps[i]!) y ∈ S)
    {A : Array Bool} (hA : ∀ j, A[j]! = true → j ∈ S) (st : ℕ × ℕ) :
    ∀ j, (derivStep n T L reps labs A st)[j]! = true → j ∈ S := by
  intro j hj
  unfold derivStep at hj
  split_ifs at hj with hc
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hc
    rcases eq_true_of_set!_eq_true hj with ⟨rfl, -⟩ | hj'
    · exact hstep _ h1 _ h2 (hA _ h3) (hA _ h4)
    · exact hA j hj'
  · exact hA j hj

theorem derivOK_sound {k c : ℕ} {steps : List (ℕ × ℕ)}
    (h : derivOK n k T L reps labs c steps = true) (h0 : 0 ∈ S) (hc : c ∈ S)
    (hstep : ∀ i < reps.size, ∀ y < n, i ∈ S → labs[y]! ∈ S →
      invLabel T L labs (ap T.pos reps[i]!) y ∈ S) :
    ∀ j < k, j ∈ S := by
  unfold derivOK at h
  have hinit : ∀ j, (((Array.replicate k false).set! 0 true).set! c true)[j]! = true →
      j ∈ S := by
    intro j hj
    rcases eq_true_of_set!_eq_true hj with ⟨rfl, -⟩ | hj'
    · exact hc
    · rcases eq_true_of_set!_eq_true hj' with ⟨rfl, -⟩ | hj''
      · exact h0
      · rw [replicate_false_getElem!] at hj''
        exact absurd hj'' (by decide)
  have hfold : ∀ (l : List (ℕ × ℕ)) (A : Array Bool), (∀ j, A[j]! = true → j ∈ S) →
      ∀ j, (l.foldl (derivStep n T L reps labs) A)[j]! = true → j ∈ S := by
    intro l
    induction l with
    | nil => intro A hA; exact hA
    | cons st l ih => intro A hA; exact ih _ (derivStep_inv hstep hA st)
  intro j hj
  exact hfold steps _ hinit j ((allIn_eq_true.1 h) j (Nat.zero_le _) hj)

end Deriv

section Labels

variable {D : Data} {c : ℕ} (hF : Facts D c)
include hF

theorem subTreeFacts {j : ℕ} (hj : j < D.subReps.size) :
    TreeFacts D.n D.subTrees[j]! D.lv (pairG (gs D)) D.subReps[j]! :=
  treeOK_facts (fun l hl => rep_pairG_all hF l (levelLetters_lt hl)) (hF.subTrees j hj)

theorem labs_iff {j : ℕ} (hj : j < D.subReps.size) {p : ℕ} (hp : p < D.n) :
    D.labs[p]! = j ↔ ∃ t < D.subTrees[j]!.pts.size, ap D.subTrees[j]!.pts t = p := by
  constructor
  · intro h
    have hm := (hF.labs_mem p hp).2
    simp only [inTreeB, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hm
    rw [h] at hm
    exact ⟨_, hm.1, hm.2⟩
  · rintro ⟨t, ht, rfl⟩
    exact hF.labs_pts j hj t ht

@[expose] noncomputable def subLab (p : Fin D.n) : Fin D.subReps.size :=
  ⟨D.labs[p.val]!, (hF.labs_mem p.val p.isLt).1⟩

theorem subLab_val (p : Fin D.n) : (subLab hF p).val = D.labs[p.val]! := rfl

omit hF in
theorem orbit_conj {H : Subgroup (J D)} {x p q : Fin D.n} (hp : p ∈ MulAction.orbit H x)
    (hq : q ∈ MulAction.orbit H x) : ∃ g ∈ H, g • p = q := by
  obtain ⟨⟨u, hu⟩, rfl⟩ := hp
  obtain ⟨⟨v, hv⟩, rfl⟩ := hq
  refine ⟨v * u⁻¹, H.mul_mem hv (H.inv_mem hu), ?_⟩
  show (v * u⁻¹) • (u • x) = v • x
  rw [mul_smul, inv_smul_smul]

theorem subLab_orb (p q : Fin D.n) (h : subLab hF p = subLab hF q) :
    ∃ g ∈ lvl D 1, g • p = q := by
  have hpq : D.labs[p.val]! = D.labs[q.val]! := congrArg Fin.val h
  have hjk : D.labs[q.val]! < D.subReps.size := (hF.labs_mem q.val q.isLt).1
  have hTF := subTreeFacts hF hjk
  exact orbit_conj ((hTF.mem_orbit_iff p).2 ((labs_iff hF hjk p.isLt).1 hpq))
    ((hTF.mem_orbit_iff q).2 ((labs_iff hF hjk q.isLt).1 rfl))

theorem labs_rep {j : ℕ} (hj : j < D.subReps.size) : D.labs[D.subReps[j]!]! = j := by
  have hTF := subTreeFacts hF hj
  have := hF.labs_pts j hj 0 hTF.size_pos
  rwa [hTF.root] at this

theorem subLab_root : (subLab hF (root D hF.n_pos)).val = 0 := by
  rw [subLab_val]
  have := labs_rep hF hF.k_pos
  rwa [hF.rep0] at this

theorem subLab_eq_root (p : Fin D.n) (h : subLab hF p = subLab hF (root D hF.n_pos)) :
    p = root D hF.n_pos := by
  have h0 : D.labs[p.val]! = 0 := by
    rw [← subLab_val hF, h, subLab_root hF]
  obtain ⟨t, ht, hp⟩ := (labs_iff hF hF.k_pos p.isLt).1 h0
  rw [hF.S0] at ht
  obtain rfl : t = 0 := by omega
  have hTF := subTreeFacts hF hF.k_pos
  apply Fin.ext
  rw [← hp, hTF.root, hF.rep0]

end Labels

@[expose] noncomputable def tRep (D : Data) (i : Fin D.subReps.size) : J D :=
  treeG D.trees[0]! (pairG (gs D)) (ap D.trees[0]!.pos D.subReps[i.val]!)

section Prim

variable {D : Data} {c : ℕ} (hF : Facts D c)
include hF

theorem mem_tree_zero (horb : D.orbSizes[0]! = D.n) (p : ℕ) (hp : p < D.n) :
    ap D.trees[0]!.pos p < D.trees[0]!.pts.size ∧ ap D.trees[0]!.pts (ap D.trees[0]!.pos p) = p := by
  have hT := (chain hF).1 0 hF.base_pos
  rw [hF.base0] at hT
  have hcard := hT.card_orbit
  rw [trees_zero_size hF, horb] at hcard
  have hfin : (MulAction.orbit (lettersGroup (levelLetters D.letters D.base 0) (pairG (gs D)))
      (⟨0, hT.r_lt⟩ : Fin D.n)) = Set.univ := by
    apply Set.eq_of_subset_of_ncard_le (Set.subset_univ _) _ (Set.toFinite _)
    rw [Set.ncard_univ, Nat.card_fin, ← Nat.card_coe_set_eq, hcard]
  have hmem : (⟨p, hp⟩ : Fin D.n) ∈ MulAction.orbit
      (lettersGroup (levelLetters D.letters D.base 0) (pairG (gs D))) (⟨0, hT.r_lt⟩ : Fin D.n) := by
    rw [hfin]; exact Set.mem_univ _
  obtain ⟨k, hk, hkp⟩ := (hT.mem_orbit_iff _).1 hmem
  have hkp' : ap D.trees[0]!.pts k = p := hkp
  rw [← hkp', hT.pos_pts k hk]
  exact ⟨hk, rfl⟩

theorem tRep_smul_root (horb : D.orbSizes[0]! = D.n) (i : Fin D.subReps.size) :
    (tRep D i • root D hF.n_pos).val = D.subReps[i.val]! := by
  have hT := (chain hF).1 0 hF.base_pos
  have hlt := (subTreeFacts hF i.isLt).r_lt
  obtain ⟨hk, hkp⟩ := mem_tree_zero hF horb _ hlt
  rw [smul_val_eq_idx]
  have := hT.elt _ hk
  rw [hF.base0, hkp] at this
  exact this

theorem isPreprimitive (horb : D.orbSizes[0]! = D.n) :
    MulAction.IsPreprimitive (J D) (Fin D.n) := by
  have := isPretransitive hF horb
  refine isPreprimitive_of_label_closure (root D hF.n_pos) (lvl D 1) (fun g hg => ?_)
    (subLab hF) (subLab_orb hF) (subLab_eq_root hF) (tRep D) (fun i => ?_) ?_
  · have : g ∈ MulAction.stabilizer (J D) (root D hF.n_pos) := by
      rw [stabilizer_root hF]; exact hg
    exact this
  · apply Fin.ext
    rw [subLab_val, tRep_smul_root hF horb, labs_rep hF i.isLt]
  · intro c' hc' S hS0 hSc hclosed
    have hc1 : 1 ≤ c'.val := by
      by_contra h0
      apply hc'
      apply Fin.ext
      rw [subLab_root hF]
      omega
    let S' : Set ℕ := {j | ∃ h : j < D.subReps.size, (⟨j, h⟩ : Fin D.subReps.size) ∈ S}
    have hW := walkFacts hF hF.base_pos
    have hall := derivOK_sound (S := S') (hF.derivs c'.val hc1 c'.isLt)
      ⟨hF.k_pos, by
        have e : (⟨0, hF.k_pos⟩ : Fin D.subReps.size) = subLab hF (root D hF.n_pos) :=
          Fin.ext (subLab_root hF).symm
        rw [e]; exact hS0⟩ ⟨c'.isLt, hSc⟩ (by
        rintro i hi y hy ⟨_, hiS⟩ ⟨_, hyS⟩
        have hlt := (subTreeFacts hF hi).r_lt
        obtain ⟨hk, -⟩ := mem_tree_zero hF horb _ hlt
        obtain ⟨-, he⟩ := walkInv_spec (lG := pairG (gs D)) hW hk #[y] (by
          intro j hj
          simp only [List.size_toArray, List.length_cons, List.length_nil] at hj
          obtain rfl : j = 0 := by omega
          simpa using hy)
        have hy' : (#[y] : Array ℕ)[0]! = y := rfl
        have he0 := he 0 (by simp)
        rw [hy'] at he0
        have hcl := hclosed ⟨i, hi⟩ hiS ⟨y, hy⟩ hyS
        have e : invLabel D.trees[0]! D.letters D.labs (ap D.trees[0]!.pos D.subReps[i]!) y =
            (subLab hF ((tRep D ⟨i, hi⟩)⁻¹ • ⟨y, hy⟩)).val := by
          rw [subLab_val, smul_val_eq_idx]
          unfold invLabel
          rw [he0]
          rfl
        show invLabel D.trees[0]! D.letters D.labs (ap D.trees[0]!.pos D.subReps[i]!) y ∈ S'
        rw [e]
        exact ⟨(subLab hF _).isLt, hcl⟩)
    intro i
    obtain ⟨_, hi⟩ := hall i.val i.isLt
    exact hi

end Prim

end CFSG.Sporadic.J3
