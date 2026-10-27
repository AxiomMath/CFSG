module

public import CFSG.LocalAnalysis.StandardType.GGLevTwoS3bTables2

public section

namespace CFSG.StandardType.LevTwo

open CFSG.LieType.RootSystem
open scoped Matrix

@[expose] def levTwoS3u_vec (n : ℕ) (v : List ℤ) : Fin n → ℤ := fun i => v.getD i.val 0

theorem levTwoS3u_vec_ofFn (n : ℕ) (f : Fin n → ℤ) :
    levTwoS3u_vec n (List.ofFn f) = f := by
  funext i
  simp [levTwoS3u_vec, List.getElem_ofFn]

theorem levTwoS3u_ofFn_vec (n : ℕ) {v : List ℤ} (hv : v.length = n) :
    List.ofFn (levTwoS3u_vec n v) = v := by
  apply List.ext_getElem
  · simp [List.length_ofFn, hv]
  · intro i h1 h2
    simp only [levTwoS3u_vec, List.getElem_ofFn]
    exact List.getD_eq_getElem v 0 h2

theorem levTwoS3u_vec_neg (n : ℕ) (v : List ℤ) :
    levTwoS3u_vec n (v.map (fun x => -x)) = -(levTwoS3u_vec n v) := by
  funext i
  by_cases hi : i.val < v.length
  · simp only [levTwoS3u_vec, Pi.neg_apply]
    rw [List.getD_eq_getElem _ _ (by simpa [List.length_map] using hi),
      List.getD_eq_getElem _ _ hi, List.getElem_map]
  · simp only [levTwoS3u_vec, Pi.neg_apply]
    rw [List.getD_eq_default _ _ (by simpa [List.length_map] using Nat.le_of_not_lt hi),
      List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt hi)]
    simp

theorem levTwoS3u_getD_map (n : ℕ) (roots : List (List ℤ)) (j : ℕ) :
    (roots.map (levTwoS3u_vec n)).getD j 0 = levTwoS3u_vec n (roots.getD j []) := by
  by_cases h : j < roots.length
  · rw [List.getD_eq_getElem _ _ (by simpa [List.length_map] using h),
      List.getD_eq_getElem _ _ h, List.getElem_map]
  · rw [List.getD_eq_default _ _ (by simpa [List.length_map] using Nat.le_of_not_lt h),
      List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt h)]
    funext i
    simp [levTwoS3u_vec]

@[expose] def levTwoS3u_idx {n : ℕ} (roots : List (List ℤ)) (β : Fin n → ℤ) : ℕ :=
  roots.idxOf (List.ofFn β)

theorem levTwoS3u_idx_vec_get {n : ℕ} {roots : List (List ℤ)} (hnodup : roots.Nodup)
    (hlen : ∀ l ∈ roots, l.length = n) (i : Fin roots.length) :
    levTwoS3u_idx roots (levTwoS3u_vec n (roots.get i)) = i.val := by
  rw [levTwoS3u_idx, levTwoS3u_ofFn_vec n (hlen (roots.get i) (List.get_mem roots i))]
  exact List.get_idxOf hnodup i

theorem levTwoS3u_nodup_map_vec {n : ℕ} {roots : List (List ℤ)} (hnodup : roots.Nodup)
    (hlen : ∀ l ∈ roots, l.length = n) :
    (roots.map (levTwoS3u_vec n)).Nodup :=
  hnodup.map_on (fun x hx y hy hxy => by
    have h := congrArg List.ofFn hxy
    rwa [levTwoS3u_ofFn_vec n (hlen x hx), levTwoS3u_ofFn_vec n (hlen y hy)] at h)

theorem levTwoS3u_isRt_iff_mem_ofFn {n : ℕ} {R : Matrix (Fin n) (Fin n) ℤ}
    {hR : TauCeti.IsFiniteType R} {roots : List (List ℤ)}
    (hlen : ∀ l ∈ roots, l.length = n)
    (hRl : ∀ β : Fin n → ℤ, IsRt hR β ↔ List.ofFn β ∈ roots) :
    ∀ β : Fin n → ℤ, IsRt hR β ↔ β ∈ roots.map (levTwoS3u_vec n) := by
  intro β
  rw [hRl β, List.mem_map]
  constructor
  · intro h
    exact ⟨List.ofFn β, h, levTwoS3u_vec_ofFn n β⟩
  · rintro ⟨l, hl, hlβ⟩
    rw [← hlβ, levTwoS3u_ofFn_vec n (hlen l hl)]
    exact hl

@[expose] def levTwoS3u_repOf {n : ℕ} (roots : List (List ℤ)) (cl : List (ℕ × ℕ))
    (a : Fin cl.length) : Fin n → ℤ :=
  levTwoS3u_vec n (roots.getD (cl.getD a.val (0, 0)).1 [])

@[expose] def levTwoS3u_clsOf {n : ℕ} (roots : List (List ℤ)) (cl : List (ℕ × ℕ))
    (hpos : 0 < cl.length) (β : Fin n → ℤ) : Fin cl.length :=
  if h : cl.findIdx (fun p => p.2.testBit (levTwoS3u_idx roots β)) < cl.length then ⟨_, h⟩
  else ⟨0, hpos⟩

theorem levTwoS3u_rep_mem {n : ℕ} {roots : List (List ℤ)} {cl : List (ℕ × ℕ)}
    (hcl_rep_lt : ∀ a : Fin cl.length, (cl.getD a.val (0, 0)).1 < roots.length) :
    ∀ a : Fin cl.length, levTwoS3u_repOf (n := n) roots cl a ∈ roots.map (levTwoS3u_vec n) := by
  intro a
  refine List.mem_map.mpr ⟨roots.getD (cl.getD a.val (0, 0)).1 [], ?_, rfl⟩
  rw [List.getD_eq_getElem _ _ (hcl_rep_lt a)]
  exact List.getElem_mem _

theorem levTwoS3u_repOf_eq_get {n : ℕ} (roots : List (List ℤ)) (cl : List (ℕ × ℕ))
    (a : Fin cl.length) (hrlt : (cl.getD a.val (0, 0)).1 < roots.length) :
    levTwoS3u_repOf (n := n) roots cl a
      = (roots.map (levTwoS3u_vec n)).get
          ⟨(cl.getD a.val (0, 0)).1, by rw [List.length_map]; exact hrlt⟩ := by
  simp only [levTwoS3u_repOf]
  rw [List.getD_eq_get _ _ ⟨_, hrlt⟩]
  simp only [List.get_eq_getElem, List.getElem_map]

theorem levTwoS3u_notMem_patSet_of_not_bit {n : ℕ} {roots : List (List ℤ)} (hnodup : roots.Nodup)
    (hlen : ∀ l ∈ roots, l.length = n) {pm : ℕ} {cl : List (ℕ × ℕ)}
    (hcl_rep_lt : ∀ a : Fin cl.length, (cl.getD a.val (0, 0)).1 < roots.length)
    (hrep_notpat : ∀ a : Fin cl.length, ¬ pm.testBit (cl.getD a.val (0, 0)).1) :
    ∀ a : Fin cl.length, levTwoS3u_repOf (n := n) roots cl a ∉
      {β : Fin n → ℤ | ∃ i : Fin (roots.map (levTwoS3u_vec n)).length,
        (roots.map (levTwoS3u_vec n)).get i = β ∧ pm.testBit i.val} := by
  intro a hmem
  obtain ⟨i, hi, hbit⟩ := hmem
  have hrlt : (cl.getD a.val (0, 0)).1 < roots.length := hcl_rep_lt a
  have hnodupV := levTwoS3u_nodup_map_vec hnodup hlen
  have hrep := levTwoS3u_repOf_eq_get (n := n) roots cl a hrlt
  have hidx : i.val = (cl.getD a.val (0, 0)).1 := by
    have h2 : (roots.map (levTwoS3u_vec n)).get i
        = (roots.map (levTwoS3u_vec n)).get
            ⟨(cl.getD a.val (0, 0)).1, by rw [List.length_map]; exact hrlt⟩ := by
      rw [hi, hrep]
    exact congrArg Fin.val (List.nodup_iff_injective_get.mp hnodupV h2)
  exact hrep_notpat a (by rw [← hidx]; exact hbit)

theorem levTwoS3u_isRt_of_mem_patSet {n : ℕ} {R : Matrix (Fin n) (Fin n) ℤ}
    {hR : TauCeti.IsFiniteType R} {roots : List (List ℤ)}
    (hRl : ∀ β : Fin n → ℤ, IsRt hR β ↔ β ∈ roots.map (levTwoS3u_vec n))
    {pm : ℕ} {Φ : Set (Fin n → ℤ)}
    (hΦ : ∀ β, β ∈ Φ ↔ ∃ i : Fin (roots.map (levTwoS3u_vec n)).length,
      (roots.map (levTwoS3u_vec n)).get i = β ∧ pm.testBit i.val) :
    ∀ β ∈ Φ, IsRt hR β := by
  intro β hβ
  obtain ⟨i, rfl, -⟩ := (hΦ β).mp hβ
  exact (hRl _).mpr (List.get_mem _ i)

theorem levTwoS3u_foldl_testBit_mono (inPat : List ℤ → Bool) (roots : List (List ℤ)) :
    ∀ (l : List ℕ) (acc i : ℕ), acc.testBit i = true →
      (l.foldl (fun acc j => if inPat (roots.getD j []) then acc ||| (1 <<< j) else acc)
        acc).testBit i = true := by
  intro l
  induction l with
  | nil => intro acc i hi; exact hi
  | cons j l ih =>
      intro acc i hi
      rw [List.foldl_cons]
      by_cases h : inPat (roots.getD j [])
      · rw [if_pos h]
        exact ih (acc ||| (1 <<< j)) i (by rw [Nat.testBit_lor]; simp [hi])
      · rw [if_neg h]
        exact ih acc i hi

theorem levTwoS3u_foldl_testBit_of_mem (inPat : List ℤ → Bool) (roots : List (List ℤ)) :
    ∀ (l : List ℕ) (acc i : ℕ), i ∈ l → inPat (roots.getD i []) = true →
      (l.foldl (fun acc j => if inPat (roots.getD j []) then acc ||| (1 <<< j) else acc)
        acc).testBit i = true := by
  intro l
  induction l with
  | nil => intro acc i hi _; simp at hi
  | cons j l ih =>
      intro acc i hi hin
      rw [List.foldl_cons]
      rcases List.mem_cons.mp hi with rfl | hi
      · rw [if_pos hin]
        exact levTwoS3u_foldl_testBit_mono inPat roots l (acc ||| (1 <<< i)) i
          (by rw [Nat.testBit_lor]; simp)
      · by_cases hj : inPat (roots.getD j [])
        · rw [if_pos hj]
          exact ih (acc ||| (1 <<< j)) i hi hin
        · rw [if_neg hj]
          exact ih acc i hi hin

theorem levTwoS3u_patMask_testBit (N : ℕ) (inPat : List ℤ → Bool) (roots : List (List ℤ))
    {i : ℕ} (hi : i < N) (hin : inPat (roots.getD i []) = true) :
    ((List.range N).foldl
      (fun acc j => if inPat (roots.getD j []) then acc ||| (1 <<< j) else acc) 0).testBit i =
        true :=
  levTwoS3u_foldl_testBit_of_mem inPat roots (List.range N) 0 i (List.mem_range.mpr hi) hin

theorem levTwoS3u_gen_mem {n N : ℕ} {roots : List (List ℤ)} (hN : roots.length = N)
    (inPat : List ℤ → Bool) {pm : ℕ}
    (hpm : pm = (List.range N).foldl
      (fun acc i => if inPat (roots.getD i []) then acc ||| (1 <<< i) else acc) 0)
    {g : List ℤ} (hg : g ∈ roots) (hin : inPat g = true) :
    levTwoS3u_vec n g ∈ {β : Fin n → ℤ | ∃ i : Fin (roots.map (levTwoS3u_vec n)).length,
      (roots.map (levTwoS3u_vec n)).get i = β ∧ pm.testBit i.val} := by
  have hi : roots.idxOf g < roots.length := List.idxOf_lt_length_iff.mpr hg
  have hiN : roots.idxOf g < N := by rw [← hN]; exact hi
  refine ⟨⟨roots.idxOf g, by rw [List.length_map]; exact hi⟩, ?_, ?_⟩
  · rw [List.get_eq_getElem, List.getElem_map, List.getElem_idxOf hi]
  · rw [hpm]
    exact levTwoS3u_patMask_testBit N inPat roots hiN (by
      rw [List.getD_eq_getElem _ _ hi, List.getElem_idxOf hi]; exact hin)

theorem levTwoS3u_reflectStep_of_list {n : ℕ} {R : Matrix (Fin n) (Fin n) ℤ}
    {hR : TauCeti.IsFiniteType R} {roots : List (List ℤ)}
    (hlen : ∀ l ∈ roots, l.length = n)
    (hRl : ∀ β : Fin n → ℤ, IsRt hR β ↔ β ∈ roots.map (levTwoS3u_vec n))
    {reflv : List ℤ → List ℤ → List ℤ}
    (hweyl : ∀ (g v : List ℤ), g.length = n → v.length = n →
      IsRt hR (levTwoS3u_vec n g) → IsRt hR (levTwoS3u_vec n v) →
      weylAction hR (rRefl hR (levTwoS3u_vec n g)) (levTwoS3u_vec n v) =
        levTwoS3u_vec n (reflv g v))
    {g : List ℤ} (hg : g.length = n) (hgrt : IsRt hR (levTwoS3u_vec n g)) {p : List ℕ}
    (hstep : ∀ i, i < roots.length → roots.getD (p.getD i 0) [] = reflv g (roots.getD i [])) :
    levTwoS3b_reflectStep hR (roots.map (levTwoS3u_vec n)) (levTwoS3u_vec n g) p := by
  intro i hi
  rw [List.length_map] at hi
  have hlen_i : (roots.getD i []).length = n := by
    rw [List.getD_eq_getElem _ _ hi]
    exact hlen _ (List.getElem_mem hi)
  have hget : roots.getD i [] ∈ roots := by
    rw [List.getD_eq_getElem _ _ hi]
    exact List.getElem_mem hi
  have hvrt : IsRt hR (levTwoS3u_vec n (roots.getD i [])) :=
    (hRl _).mpr (List.mem_map.mpr ⟨roots.getD i [], hget, rfl⟩)
  calc (roots.map (levTwoS3u_vec n)).getD (p.getD i 0) 0
      = levTwoS3u_vec n (roots.getD (p.getD i 0) []) := levTwoS3u_getD_map n roots _
    _ = levTwoS3u_vec n (reflv g (roots.getD i [])) := by rw [hstep i hi]
    _ = weylAction hR (rRefl hR (levTwoS3u_vec n g)) (levTwoS3u_vec n (roots.getD i [])) :=
        (hweyl g (roots.getD i []) hg hlen_i hgrt hvrt).symm
    _ = weylAction hR (rRefl hR (levTwoS3u_vec n g))
          ((roots.map (levTwoS3u_vec n)).getD i 0) := by rw [levTwoS3u_getD_map]

theorem levTwoS3u_negStep_of_list {n : ℕ} {roots : List (List ℤ)} {p : List ℕ}
    (hstep : ∀ i, i < roots.length →
      roots.getD (p.getD i 0) [] = (roots.getD i []).map (fun x => -x)) :
    levTwoS3b_negStep (roots.map (levTwoS3u_vec n)) p := by
  intro i hi
  rw [List.length_map] at hi
  rw [levTwoS3u_getD_map, levTwoS3u_getD_map, hstep i hi, levTwoS3u_vec_neg]

theorem levTwoS3u_inv_of_all {n : ℕ} {base perms : List (List ℕ)}
    (hbase : base.all (fun p => (List.range n).all
      (fun i => p.getD (p.getD i 0) 0 == i)) = true)
    (hsub : ∀ p ∈ perms, p ∈ base) :
    ∀ p ∈ perms, ∀ i, i < n → p.getD (p.getD i 0) 0 = i := by
  intro p hp i hi
  have hpbase := (List.all_eq_true.mp hbase) p (hsub p hp)
  have hi' := (List.all_eq_true.mp hpbase) i (List.mem_range.mpr hi)
  exact beq_iff_eq.mp hi'

theorem levTwoS3u_range_of_all {n : ℕ} {base perms : List (List ℕ)}
    (hbase : base.all (fun p => (List.range n).all
      (fun i => decide (p.getD i 0 < n))) = true)
    (hsub : ∀ p ∈ perms, p ∈ base) :
    ∀ p ∈ perms, ∀ i, i < n → p.getD i 0 < n := by
  intro p hp i hi
  have hpbase := (List.all_eq_true.mp hbase) p (hsub p hp)
  have hi' := (List.all_eq_true.mp hpbase) i (List.mem_range.mpr hi)
  exact of_decide_eq_true hi'

end CFSG.StandardType.LevTwo
