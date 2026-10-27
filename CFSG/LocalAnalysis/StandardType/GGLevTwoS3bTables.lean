module

public import CFSG.LocalAnalysis.StandardType.GGLevTwoS3bPerm
public import CFSG.LocalAnalysis.StandardType.GGLevTwoS3bReduce

public section

namespace CFSG.StandardType.LevTwo

open CFSG.LieType.RootSystem
open scoped Matrix

@[expose] def levTwoS3t_edgeB (N : ℕ) (perms : List (List ℕ)) (i j : ℕ) : Prop :=
  i < N ∧ j < N ∧ ∃ p ∈ perms, p.getD i 0 = j

theorem levTwoS3t_edgeB_symm {N : ℕ} {perms : List (List ℕ)}
    (hinv : ∀ p ∈ perms, ∀ i, i < N → p.getD (p.getD i 0) 0 = i)
    {i j : ℕ} (h : levTwoS3t_edgeB N perms i j) : levTwoS3t_edgeB N perms j i := by
  obtain ⟨hiN, hjN, p, hp, hpx⟩ := h
  exact ⟨hjN, hiN, p, hp, by rw [← hpx]; exact hinv p hp i hiN⟩

theorem levTwoS3t_reachB_symm {N : ℕ} {perms : List (List ℕ)}
    (hinv : ∀ p ∈ perms, ∀ i, i < N → p.getD (p.getD i 0) 0 = i) {i j : ℕ}
    (h : Relation.ReflTransGen (levTwoS3t_edgeB N perms) i j) :
    Relation.ReflTransGen (levTwoS3t_edgeB N perms) j i := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih =>
      exact (Relation.ReflTransGen.single (levTwoS3t_edgeB_symm hinv hbc)).trans ih

theorem levTwoS3t_bfsMask_reachB {N : ℕ} (perms : List (List ℕ))
    (hrange : ∀ p ∈ perms, ∀ i, i < N → p.getD i 0 < N) (r : ℕ) (_hr : r < N) :
    ∀ (fuel : ℕ) (q : List ℕ) (vis : ℕ),
      (∀ i ∈ q, i < N ∧ Relation.ReflTransGen (levTwoS3t_edgeB N perms) r i) →
      (∀ i, vis.testBit i = true → i < N ∧ Relation.ReflTransGen (levTwoS3t_edgeB N perms) r i) →
      ∀ i, (levTwoS3b_bfsMask perms fuel q vis).testBit i = true →
        i < N ∧ Relation.ReflTransGen (levTwoS3t_edgeB N perms) r i := by
  intro fuel
  induction fuel with
  | zero => intro q vis _ hvis i hi; exact hvis i hi
  | succ f ih =>
      intro q vis hq hvis
      cases q with
      | nil => intro i hi; exact hvis i hi
      | cons b rest =>
          simp only [levTwoS3b_bfsMask]
          obtain ⟨hr1, hr2⟩ := levTwoS3b_foldl_inv (perms.map (fun p => p.getD b 0)) vis []
            (fun i hi => by
              obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hi
              obtain ⟨hbN, hbReach⟩ := hq b List.mem_cons_self
              exact ⟨hrange p hp b hbN,
                hbReach.trans (Relation.ReflTransGen.single
                  ⟨hbN, hrange p hp b hbN, p, hp, rfl⟩)⟩)
            hvis (fun i hi => by simp at hi)
          exact ih _ _ (fun i hi => by
            rcases List.mem_append.mp hi with hi | hi
            · exact hq i (List.mem_cons_of_mem b hi)
            · exact hr2 i hi) hr1

theorem levTwoS3t_bfsMask_reachB_single {N : ℕ} (perms : List (List ℕ))
    (hrange : ∀ p ∈ perms, ∀ i, i < N → p.getD i 0 < N) (r : ℕ) (hr : r < N) (i : ℕ)
    (h : (levTwoS3b_bfsMask perms 300 [r] (1 <<< r)).testBit i = true) :
    Relation.ReflTransGen (levTwoS3t_edgeB N perms) r i :=
  (levTwoS3t_bfsMask_reachB perms hrange r hr 300 [r] (1 <<< r)
    (fun i hi => by
      simp only [List.mem_singleton] at hi
      subst hi
      exact ⟨hr, Relation.ReflTransGen.refl⟩)
    (fun i hi => by
      rw [levTwoS3b_testBit_one_shiftLeft] at hi
      subst hi
      exact ⟨hr, Relation.ReflTransGen.refl⟩)
    i h).2

theorem levTwoS3t_Cl_of_reachB {ι : Type} [Fintype ι] [DecidableEq ι] {R : Matrix ι ι ℤ}
    {hR : TauCeti.IsFiniteType R} {N : ℕ} {perms : List (List ℕ)} {roots : List (ι → ℤ)}
    {S : Set (ι → ℤ)}
    (hvalid : ∀ p ∈ perms,
      (∃ g ∈ S, levTwoS3b_reflectStep hR roots g p) ∨ levTwoS3b_negStep roots p)
    (hS : ∀ β ∈ S, IsRt hR β) {i j : ℕ}
    (h : Relation.ReflTransGen (levTwoS3t_edgeB N perms) i j)
    (hi : Cl hR S (roots.getD i 0)) : Cl hR S (roots.getD j 0) := by
  have hperm := levTwoS3b_hperm_of_valid (S := S) hS (fun p hp =>
    match hvalid p hp with
    | Or.inl ⟨g, hgS, hstep⟩ => Or.inl ⟨g, Cl.base hgS, hstep⟩
    | Or.inr hneg => Or.inr hneg)
  refine Relation.ReflTransGen.rec (a := i)
    (motive := fun j _ => Cl hR S (roots.getD i 0) → Cl hR S (roots.getD j 0))
    (fun h => h) (fun {b c} hab hbc ih hcl => ?_) h hi
  obtain ⟨-, -, p, hp, hpc⟩ := hbc
  rw [← hpc]
  exact hperm p hp b (ih hcl)

theorem levTwoS3t_testBit_foldl_or : ∀ (l : List ℕ) (acc i : ℕ),
    (l.foldl (fun a b => a ||| (1 <<< b)) acc).testBit i = true →
      acc.testBit i = true ∨ i ∈ l
  | [], _, _, h => Or.inl h
  | b :: l, acc, i, h => by
      rw [List.foldl_cons] at h
      rcases levTwoS3t_testBit_foldl_or l (acc ||| (1 <<< b)) i h with h' | h'
      · rw [Nat.testBit_lor, Bool.or_eq_true] at h'
        rcases h' with h'' | h''
        · exact Or.inl h''
        · exact Or.inr (List.mem_cons.mpr (Or.inl (by
            rw [levTwoS3b_testBit_one_shiftLeft] at h''
            exact h'')))
      · exact Or.inr (List.mem_cons_of_mem b h')

@[expose] def levTwoS3t_idxOf {ι : Type} [DecidableEq ι] (roots : List ι) (β : ι) : ℕ :=
  roots.findIdx (· = β)

@[expose] def levTwoS3t_clsOf {ι : Type} [DecidableEq ι] (roots : List ι) (cl : List (ℕ × ℕ))
    (hpos : 0 < cl.length) (β : ι) : Fin cl.length :=
  if h : cl.findIdx (fun p => p.2.testBit (levTwoS3t_idxOf roots β)) < cl.length then ⟨_, h⟩
  else ⟨0, hpos⟩

@[expose] def levTwoS3t_coversWith {ι : Type} (reflPerm : (ι → ℤ) → List ℕ)
    (cl : List (ℕ × ℕ)) (rep : Fin cl.length → ι → ℤ) (perms : List (List ℕ))
    (seed : List ℕ) (T T' : List (Fin cl.length)) : Bool :=
  let reps := T'.map (fun a => (cl.getD a.1 (0, 0)).1)
  let extra := T'.map (fun a => reflPerm (rep a))
  let q0 := seed ++ reps
  let vis0 := q0.foldl (fun acc b => acc ||| (1 <<< b)) 0
  let orb := levTwoS3b_bfsMask (perms ++ extra) 300 q0 vis0
  T.all (fun a => orb.testBit ((cl.getD a.1 (0, 0)).1))

theorem levTwoS3t_Cl_of_coversWith {ι : Type} [Fintype ι] [DecidableEq ι] {R : Matrix ι ι ℤ}
    {hR : TauCeti.IsFiniteType R} {cl : List (ℕ × ℕ)} (reflPerm : (ι → ℤ) → List ℕ)
    (rep : Fin cl.length → ι → ℤ) (perms : List (List ℕ)) (seed : List ℕ) (roots : List (ι → ℤ))
    (Φ : Set (ι → ℤ))
    (hΦrt : ∀ β ∈ Φ, IsRt hR β)
    (hseed : ∀ i ∈ seed, roots.getD i 0 ∈ Φ)
    (hvalidP : ∀ p ∈ perms,
      (∃ g ∈ Φ, levTwoS3b_reflectStep hR roots g p) ∨ levTwoS3b_negStep roots p)
    (hrep_mem : ∀ a, rep a ∈ roots)
    (hrep_eq : ∀ a, rep a = roots.getD (cl.getD a.1 (0, 0)).1 0)
    (hrefl : ∀ a : Fin cl.length, levTwoS3b_reflectStep hR roots (rep a) (reflPerm (rep a)))
    (hRl : ∀ β, IsRt hR β ↔ β ∈ roots)
    (T T' : List (Fin cl.length))
    (hcover : levTwoS3t_coversWith reflPerm cl rep perms seed T T' = true) :
    ∀ a ∈ T, Cl hR (Φ ∪ ((T'.map rep).toFinset : Set (ι → ℤ))) (rep a) := by
  intro a ha
  set S : Set (ι → ℤ) := Φ ∪ ((T'.map rep).toFinset : Set (ι → ℤ)) with hSdef
  have hSrt : ∀ β ∈ S, IsRt hR β := by
    intro β hβ
    rw [hSdef] at hβ
    rcases hβ with hβ | hβ
    · exact hΦrt β hβ
    · rw [Finset.mem_coe, List.mem_toFinset] at hβ
      obtain ⟨b, -, rfl⟩ := List.mem_map.mp hβ
      exact (hRl _).2 (hrep_mem b)
  have hvalidAll : ∀ p ∈ perms ++ T'.map (fun a => reflPerm (rep a)),
      (∃ g, Cl hR S g ∧ levTwoS3b_reflectStep hR roots g p) ∨ levTwoS3b_negStep roots p := by
    intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · rcases hvalidP p hp with ⟨g, hg, hstep⟩ | hneg
      · exact Or.inl ⟨g, Cl.base (by rw [hSdef]; exact Or.inl hg), hstep⟩
      · exact Or.inr hneg
    · obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hp
      exact Or.inl ⟨rep b, Cl.base (by
        rw [hSdef]
        exact Or.inr (by rw [Finset.mem_coe, List.mem_toFinset]; exact List.mem_map.mpr ⟨b, hb, rfl⟩)),
        hrefl b⟩
  have hperm := levTwoS3b_hperm_of_valid (S := S) hSrt hvalidAll
  have hall := List.all_eq_true.mp (by simpa only [levTwoS3t_coversWith] using hcover)
  have hq : ∀ i ∈ seed ++ T'.map (fun a => (cl.getD a.1 (0, 0)).1),
      Cl hR S (roots.getD i 0) := by
    intro i hi
    rcases List.mem_append.mp hi with hi | hi
    · exact Cl.base (by rw [hSdef]; exact Or.inl (hseed i hi))
    · obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hi
      rw [← hrep_eq b]
      exact Cl.base (by
        rw [hSdef]
        exact Or.inr (by rw [Finset.mem_coe, List.mem_toFinset]; exact List.mem_map.mpr ⟨b, hb, rfl⟩))
  have hv : ∀ i, ((seed ++ T'.map (fun a => (cl.getD a.1 (0, 0)).1)).foldl
      (fun acc b => acc ||| (1 <<< b)) 0).testBit i = true → Cl hR S (roots.getD i 0) := by
    intro i hi
    rcases levTwoS3t_testBit_foldl_or (seed ++ T'.map (fun a => (cl.getD a.1 (0, 0)).1)) 0 i hi with h0 | hi'
    · simp at h0
    · exact hq i hi'
  have hbridge := levTwoS3b_Cl_of_bfsMask hperm 300
    (seed ++ T'.map (fun a => (cl.getD a.1 (0, 0)).1))
    ((seed ++ T'.map (fun a => (cl.getD a.1 (0, 0)).1)).foldl (fun acc b => acc ||| (1 <<< b)) 0)
    hq hv ((cl.getD a.1 (0, 0)).1) (hall a ha)
  rw [hrep_eq a]
  exact hbridge

end CFSG.StandardType.LevTwo

