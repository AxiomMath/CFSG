module

public import CFSG.LocalAnalysis.StandardType.GGLevTwoS3bSem
public import CFSG.LocalAnalysis.StandardType.GGLevTwoS3bE8Link
public import CFSG.LocalAnalysis.StandardType.GGLevTwoS3bTables3
import CFSG.LocalAnalysis.StandardType.GGLevTwoS3aDict
import CFSG.LocalAnalysis.StandardType.GGLevTwoS3bClsK

public section

namespace CFSG.StandardType.LevTwo

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsL33d
open CFSG.LieType.RootSystem
open scoped Matrix

@[expose] def levTwoS3b_e8_rootVecs : List (Fin (Tag.rank Tag.E8) → ℤ) :=
  levTwoS3b_roots.map (levTwoS3u_vec (Tag.rank Tag.E8))

@[expose] def levTwoS3b_e8_patSetMask (m : ℕ) : Set (Fin (Tag.rank Tag.E8) → ℤ) :=
  {β | ∃ i : Fin levTwoS3b_e8_rootVecs.length,
    levTwoS3b_e8_rootVecs.get i = β ∧ (levTwoS3b_patMask m).testBit i.val}

@[expose] def levTwoS3b_e8_gensOf (m : ℕ) : List ((Fin (Tag.rank Tag.E8) → ℤ) × List ℕ) :=
  (levTwoS3b_nodesOf m).map (fun x =>
    (levTwoS3u_vec (Tag.rank Tag.E8) (levTwoS3b_genVec x), levTwoS3b_e8Perms.getD x []))

@[expose] def levTwoS3b_e8_permsOf (m : ℕ) : List (List ℕ) :=
  levTwoS3b_e8NegPerm :: (levTwoS3b_nodesOf m).map (fun x => levTwoS3b_e8Perms.getD x [])

private theorem levTwoS3b_e8_foldl_testBit_imp (inPat : List ℤ → Bool) (roots : List (List ℤ)) :
    ∀ (l : List ℕ) (acc i : ℕ),
      (l.foldl (fun acc j => if inPat (roots.getD j []) then acc ||| (1 <<< j) else acc) acc).testBit i = true →
      acc.testBit i = true ∨ (i ∈ l ∧ inPat (roots.getD i []) = true) := by
  intro l
  induction l with
  | nil => intro acc i h; exact Or.inl h
  | cons j l ih =>
      intro acc i h
      rw [List.foldl_cons] at h
      rcases ih (if inPat (roots.getD j []) then acc ||| (1 <<< j) else acc) i h with h1 | h2
      · by_cases hj : inPat (roots.getD j [])
        · rw [if_pos hj] at h1
          rw [Nat.testBit_lor, Bool.or_eq_true] at h1
          rcases h1 with h1 | h1
          · exact Or.inl h1
          · rw [levTwoS3b_testBit_one_shiftLeft] at h1
            exact Or.inr ⟨by rw [h1]; exact List.mem_cons_self .., by rw [h1]; exact hj⟩
        · rw [if_neg hj] at h1
          exact Or.inl h1
      · exact Or.inr ⟨List.mem_cons_of_mem j h2.1, h2.2⟩

private theorem levTwoS3b_e8_patMask_testBit_imp (m i : ℕ)
    (hbit : (levTwoS3b_patMask m).testBit i = true) :
    levTwoS3b_inPat m (levTwoS3b_roots.getD i []) = true := by
  have h := levTwoS3b_e8_foldl_testBit_imp (levTwoS3b_inPat m) levTwoS3b_roots
    (List.range 240) 0 i (by simpa only [levTwoS3b_patMask] using hbit)
  rcases h with h0 | ⟨_, hin⟩
  · exact absurd h0 (by simp)
  · exact hin

private theorem levTwoS3b_e8_rootVecs_get (i : Fin levTwoS3b_e8_rootVecs.length) :
    levTwoS3b_e8_rootVecs.get i =
      levTwoS3u_vec (Tag.rank Tag.E8) (levTwoS3b_roots.getD i.val []) := by
  rw [← levTwoS3u_getD_map (Tag.rank Tag.E8) levTwoS3b_roots i.val,
    List.get_eq_getElem, ← List.getD_eq_getElem levTwoS3b_e8_rootVecs 0 i.isLt]
  rfl

theorem levTwoS3b_e8_patSet_eq (m : ℕ) :
    levTwoS3b_e8_patSet m = levTwoS3b_e8_patSetMask m := by
  ext β
  constructor
  · rintro ⟨i, hi, hveq, hpat⟩
    refine ⟨⟨i, ?_⟩, ?_, ?_⟩
    · show i < 240; exact hi
    · rw [levTwoS3b_e8_rootVecs_get]
      exact hveq
    · exact levTwoS3u_patMask_testBit 240 (levTwoS3b_inPat m) levTwoS3b_roots hi hpat
  · rintro ⟨i, hget, hbit⟩
    have hi : i.val < 240 := i.isLt
    refine ⟨i.val, hi, ?_, ?_⟩
    · have hget' := hget
      rw [levTwoS3b_e8_rootVecs_get i] at hget'
      exact hget'
    · exact levTwoS3b_e8_patMask_testBit_imp m i.val hbit

theorem levTwoS3b_e8_hlen : ∀ l ∈ levTwoS3b_roots, l.length = Tag.rank Tag.E8 := by
  intro l hl
  simpa only [levTwoS3b_roots, Tag.rank] using length_of_mem_artifactRoots hl

theorem levTwoS3b_e8_hnodup :
    levTwoS3b_roots.Nodup := by
  simpa only [levTwoS3b_roots] using nodup_artifactRoots (τ := Tag.E8)

theorem levTwoS3b_e8_hRl :
    ∀ β : Fin (Tag.rank Tag.E8) → ℤ,
      IsRt (isFiniteType_cartan Tag.E8) β ↔ β ∈ levTwoS3b_e8_rootVecs := by
  have hRl0 : ∀ β : Fin (Tag.rank Tag.E8) → ℤ,
      IsRt (isFiniteType_cartan Tag.E8) β ↔ List.ofFn β ∈ levTwoS3b_roots := by
    intro β
    rw [levTwoS3a_isRt_iff]
    change IsRoot Tag.E8 β ↔ List.ofFn β ∈ Tag.artifactRoots Tag.E8
    exact isRoot_iff_mem_artifactRoots
  exact levTwoS3u_isRt_iff_mem_ofFn levTwoS3b_e8_hlen hRl0

private theorem levTwoS3b_e8_genVec_length (x : ℕ) :
    (levTwoS3b_genVec x).length = Tag.rank Tag.E8 := by
  rcases x with _ | j <;> rfl

private theorem levTwoS3b_e8_genVec_mem_all :
    (List.range 9).all (fun x => decide (levTwoS3b_genVec x ∈ levTwoS3b_roots)) = true := by
  decide +kernel

private theorem levTwoS3b_e8_perm_valid_all (x : Fin 9) :
    ∀ i : Fin 240,
      levTwoS3b_roots.getD ((levTwoS3b_e8Perms.getD x.val []).getD i.val 0) [] =
        levTwoS3b_reflv (levTwoS3b_genVec x.val) (levTwoS3b_roots.getD i.val []) := by
  fin_cases x
  · exact levTwoS3b_e8Perm_valid_0
  · exact levTwoS3b_e8Perm_valid_1
  · exact levTwoS3b_e8Perm_valid_2
  · exact levTwoS3b_e8Perm_valid_3
  · exact levTwoS3b_e8Perm_valid_4
  · exact levTwoS3b_e8Perm_valid_5
  · exact levTwoS3b_e8Perm_valid_6
  · exact levTwoS3b_e8Perm_valid_7
  · exact levTwoS3b_e8Perm_valid_8

theorem levTwoS3b_e8_gens_mem (m : ℕ)
    (hcheck : (List.range 9).all (fun x =>
      !(m.testBit x) || levTwoS3b_inPat m (levTwoS3b_genVec x)) = true) :
    ∀ gp ∈ levTwoS3b_e8_gensOf m, gp.1 ∈ levTwoS3b_e8_patSetMask m := by
  intro gp hgp
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hgp
  have hxmem : x ∈ List.range 9 := (List.mem_filter.mp hx).1
  have hxbit : m.testBit x = true := (List.mem_filter.mp hx).2
  have hg : levTwoS3b_genVec x ∈ levTwoS3b_roots :=
    of_decide_eq_true ((List.all_eq_true.mp levTwoS3b_e8_genVec_mem_all) x hxmem)
  have hin : levTwoS3b_inPat m (levTwoS3b_genVec x) = true := by
    have hthis := (List.all_eq_true.mp hcheck) x hxmem
    rw [Bool.or_eq_true] at hthis
    rcases hthis with h | h
    · simp [hxbit] at h
    · exact h
  exact levTwoS3u_gen_mem (n := Tag.rank Tag.E8) (N := 240) (by decide +kernel) (levTwoS3b_inPat m)
    (pm := levTwoS3b_patMask m) (by rfl) hg hin

theorem levTwoS3b_e8_gens_step
    (m : ℕ) :
    ∀ gp ∈ levTwoS3b_e8_gensOf m,
      levTwoS3b_reflectStep (isFiniteType_cartan Tag.E8) levTwoS3b_e8_rootVecs gp.1 gp.2 := by
  intro gp hgp
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hgp
  have hxmem : x ∈ List.range 9 := (List.mem_filter.mp hx).1
  have hx9 : x < 9 := List.mem_range.mp hxmem
  have hg : levTwoS3b_genVec x ∈ levTwoS3b_roots :=
    of_decide_eq_true ((List.all_eq_true.mp levTwoS3b_e8_genVec_mem_all) x hxmem)
  have hgrt : IsRt (isFiniteType_cartan Tag.E8)
      (levTwoS3u_vec (Tag.rank Tag.E8) (levTwoS3b_genVec x)) :=
    (levTwoS3b_e8_hRl _).mpr (List.mem_map.mpr ⟨_, hg, rfl⟩)
  exact levTwoS3u_reflectStep_of_list levTwoS3b_e8_hlen (fun β => levTwoS3b_e8_hRl β)
    (reflv := levTwoS3b_reflv)
    (fun g v hgv hvv hig hiv =>
      levTwoS3b_e8_weylAction_reflv (levTwoS3a_isRt_iff.mp hig) (levTwoS3a_isRt_iff.mp hiv)
        hgv hvv)
    (levTwoS3b_e8_genVec_length x) hgrt
    (fun i hi => levTwoS3b_e8_perm_valid_all ⟨x, hx9⟩ ⟨i, hi⟩)

theorem levTwoS3b_e8_negStep :
    levTwoS3b_negStep levTwoS3b_e8_rootVecs levTwoS3b_e8NegPerm :=
  levTwoS3u_negStep_of_list (n := Tag.rank Tag.E8) (roots := levTwoS3b_roots)
    (fun i hi => levTwoS3b_e8NegPerm_valid ⟨i, hi⟩)

private theorem levTwoS3b_e8_permsOf_sub (m : ℕ) :
    ∀ p ∈ levTwoS3b_e8_permsOf m, p ∈ levTwoS3b_e8NegPerm :: levTwoS3b_e8Perms := by
  intro p hp
  rcases List.mem_cons.mp hp with rfl | hp
  · exact List.mem_cons_self ..
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hp
    have hx9 : x < 9 := List.mem_range.mp (List.mem_filter.mp hx).1
    have hlen : levTwoS3b_e8Perms.length = 9 := by decide +kernel
    have hx' : x < levTwoS3b_e8Perms.length := by rw [hlen]; exact hx9
    rw [List.getD_eq_get _ _ ⟨x, hx'⟩]
    exact List.mem_cons_of_mem _ (List.get_mem _ _)

private theorem levTwoS3b_e8_base_inv :
    (levTwoS3b_e8NegPerm :: levTwoS3b_e8Perms).all (fun p =>
      (List.range levTwoS3b_e8_rootVecs.length).all
        (fun i => p.getD (p.getD i 0) 0 == i)) = true := by
  decide +kernel

private theorem levTwoS3b_e8_base_range :
    (levTwoS3b_e8NegPerm :: levTwoS3b_e8Perms).all (fun p =>
      (List.range levTwoS3b_e8_rootVecs.length).all (fun i => decide (p.getD i 0 <
        levTwoS3b_e8_rootVecs.length))) = true := by
  decide +kernel

theorem levTwoS3b_e8_inv (m : ℕ) :
    ∀ p ∈ levTwoS3b_e8_permsOf m, ∀ i, i < levTwoS3b_e8_rootVecs.length →
      p.getD (p.getD i 0) 0 = i :=
  levTwoS3u_inv_of_all levTwoS3b_e8_base_inv (levTwoS3b_e8_permsOf_sub m)

theorem levTwoS3b_e8_range (m : ℕ) :
    ∀ p ∈ levTwoS3b_e8_permsOf m, ∀ i, i < levTwoS3b_e8_rootVecs.length →
      p.getD i 0 < levTwoS3b_e8_rootVecs.length :=
  levTwoS3u_range_of_all levTwoS3b_e8_base_range (levTwoS3b_e8_permsOf_sub m)

private theorem levTwoS3b_e8_tcRoot_of_data
    (m : ℕ)
    (hgen : (List.range 9).all (fun x =>
      !(m.testBit x) || levTwoS3b_inPat m (levTwoS3b_genVec x)) = true)
    (cl : List (ℕ × ℕ)) (hpos : 0 < cl.length) (hlen2 : cl.length ≤ 2)
    (hcl_rep_lt : ∀ a : Fin cl.length,
      (cl.getD a.val (0, 0)).1 < levTwoS3b_e8_rootVecs.length)
    (hrep_notpat : ∀ a : Fin cl.length,
      ¬ (levTwoS3b_patMask m).testBit (cl.getD a.val (0, 0)).1)
    (hrep_cls : ∀ a : Fin cl.length,
      levTwoS3u_clsOf levTwoS3b_roots cl hpos
        (levTwoS3u_repOf (n := Tag.rank Tag.E8) levTwoS3b_roots cl a) = a)
    (hcls_orbit : ∀ i : Fin levTwoS3b_e8_rootVecs.length,
      ¬ (levTwoS3b_patMask m).testBit i.val →
      (cl.getD (levTwoS3u_clsOf levTwoS3b_roots cl hpos
        (levTwoS3b_e8_rootVecs.get i)).1 (0, 0)).2.testBit i.val = true)
    (hcl_bfs : ∀ a : Fin cl.length,
      levTwoS3b_bfsMask (levTwoS3b_e8_permsOf m) 300
        [(cl.getD a.val (0, 0)).1] (1 <<< (cl.getD a.val (0, 0)).1) =
          (cl.getD a.val (0, 0)).2) :
    TCRoot (isFiniteType_cartan Tag.E8) (levTwoS3b_e8_patSetMask m) := by
  have hrep_mem : ∀ a : Fin cl.length,
      levTwoS3u_repOf (n := Tag.rank Tag.E8) levTwoS3b_roots cl a ∈ levTwoS3b_e8_rootVecs :=
    levTwoS3u_rep_mem (fun a => hcl_rep_lt a)
  have hrep_notMem : ∀ a : Fin cl.length,
      levTwoS3u_repOf (n := Tag.rank Tag.E8) levTwoS3b_roots cl a ∉ levTwoS3b_e8_patSetMask m :=
    levTwoS3u_notMem_patSet_of_not_bit levTwoS3b_e8_hnodup levTwoS3b_e8_hlen
      (fun a => hcl_rep_lt a) hrep_notpat
  have hrep_notMem_imp : ∀ a : Fin cl.length,
      (∃ r ∈ levTwoS3b_e8_rootVecs, r ∉ levTwoS3b_e8_patSetMask m ∧
        levTwoS3u_clsOf levTwoS3b_roots cl hpos r = a) →
      levTwoS3u_repOf (n := Tag.rank Tag.E8) levTwoS3b_roots cl a ∉ levTwoS3b_e8_patSetMask m :=
    fun a _ => hrep_notMem a
  exact levTwoS3t_tcRoot_of_tables_of_cover
    (roots := levTwoS3b_e8_rootVecs) (hRl := levTwoS3b_e8_hRl)
    (pm := levTwoS3b_patMask m) (Φ := levTwoS3b_e8_patSetMask m) (hΦ := fun _ => Iff.rfl)
    (hΦrt := levTwoS3u_isRt_of_mem_patSet levTwoS3b_e8_hRl (fun _ => Iff.rfl))
    (gens := levTwoS3b_e8_gensOf m) (negP := levTwoS3b_e8NegPerm)
    (perms := levTwoS3b_e8_permsOf m)
    (hperms := by
      simp only [levTwoS3b_e8_permsOf, levTwoS3b_e8_gensOf, List.map_map]
      rfl)
    (hgen_mem := levTwoS3b_e8_gens_mem m hgen)
    (hgen_step := levTwoS3b_e8_gens_step m)
    (hneg := levTwoS3b_e8_negStep)
    (hinv := levTwoS3b_e8_inv m) (hrange := levTwoS3b_e8_range m)
    (cl := cl) (cls := levTwoS3u_clsOf levTwoS3b_roots cl hpos)
    (rep := levTwoS3u_repOf (n := Tag.rank Tag.E8) levTwoS3b_roots cl)
    (hrep_mem := hrep_mem) (hrep_cls := hrep_cls) (hrep_notMem := hrep_notMem_imp)
    (hcls_orbit := hcls_orbit)
    (hcl_bfs := fun a ha => hcl_bfs ⟨a, ha⟩)
    (hcl_rep_lt := fun a ha => hcl_rep_lt ⟨a, ha⟩)
    (hcover := levTwoS3t_cover_refl
      (levTwoS3u_repOf (n := Tag.rank Tag.E8) levTwoS3b_roots cl) levTwoS3b_e8_rootVecs
      (levTwoS3b_e8_patSetMask m) (levTwoS3u_clsOf levTwoS3b_roots cl hpos)
      hrep_mem hrep_cls hrep_notMem_imp hlen2)

private theorem levTwoS3b_e8_bfs_254_0 :
    levTwoS3b_bfsMask (levTwoS3b_e8_permsOf 254) 300
      [((levTwoS3b_e8ClassData_254).getD 0 (0, 0)).1]
      (1 <<< ((levTwoS3b_e8ClassData_254).getD 0 (0, 0)).1) =
      ((levTwoS3b_e8ClassData_254).getD 0 (0, 0)).2 := by
  decide +kernel

private theorem levTwoS3b_e8_bfs_254_1 :
    levTwoS3b_bfsMask (levTwoS3b_e8_permsOf 254) 300
      [((levTwoS3b_e8ClassData_254).getD 1 (0, 0)).1]
      (1 <<< ((levTwoS3b_e8ClassData_254).getD 1 (0, 0)).1) =
      ((levTwoS3b_e8ClassData_254).getD 1 (0, 0)).2 := by
  decide +kernel

private theorem levTwoS3b_e8_bfs_507_0 :
    levTwoS3b_bfsMask (levTwoS3b_e8_permsOf 507) 300
      [((levTwoS3b_e8ClassData_507).getD 0 (0, 0)).1]
      (1 <<< ((levTwoS3b_e8ClassData_507).getD 0 (0, 0)).1) =
      ((levTwoS3b_e8ClassData_507).getD 0 (0, 0)).2 := by
  decide +kernel

private theorem levTwoS3b_e8_bfs_508_0 :
    levTwoS3b_bfsMask (levTwoS3b_e8_permsOf 508) 300
      [((levTwoS3b_e8ClassData_508).getD 0 (0, 0)).1]
      (1 <<< ((levTwoS3b_e8ClassData_508).getD 0 (0, 0)).1) =
      ((levTwoS3b_e8ClassData_508).getD 0 (0, 0)).2 := by
  decide +kernel

private theorem levTwoS3b_e8_bfs_508_1 :
    levTwoS3b_bfsMask (levTwoS3b_e8_permsOf 508) 300
      [((levTwoS3b_e8ClassData_508).getD 1 (0, 0)).1]
      (1 <<< ((levTwoS3b_e8ClassData_508).getD 1 (0, 0)).1) =
      ((levTwoS3b_e8ClassData_508).getD 1 (0, 0)).2 := by
  decide +kernel

private theorem levTwoS3b_e8_bfs_509_0 :
    levTwoS3b_bfsMask (levTwoS3b_e8_permsOf 509) 300
      [((levTwoS3b_e8ClassData_509).getD 0 (0, 0)).1]
      (1 <<< ((levTwoS3b_e8ClassData_509).getD 0 (0, 0)).1) =
      ((levTwoS3b_e8ClassData_509).getD 0 (0, 0)).2 := by
  decide +kernel

private theorem levTwoS3b_e8_bfs_254 :
    ∀ a : Fin (levTwoS3b_e8ClassData_254).length,
      levTwoS3b_bfsMask (levTwoS3b_e8_permsOf 254) 300
        [((levTwoS3b_e8ClassData_254).getD a.val (0, 0)).1]
        (1 <<< ((levTwoS3b_e8ClassData_254).getD a.val (0, 0)).1) =
        ((levTwoS3b_e8ClassData_254).getD a.val (0, 0)).2 := by
  intro a
  fin_cases a
  · exact levTwoS3b_e8_bfs_254_0
  · exact levTwoS3b_e8_bfs_254_1

private theorem levTwoS3b_e8_bfs_507 :
    ∀ a : Fin (levTwoS3b_e8ClassData_507).length,
      levTwoS3b_bfsMask (levTwoS3b_e8_permsOf 507) 300
        [((levTwoS3b_e8ClassData_507).getD a.val (0, 0)).1]
        (1 <<< ((levTwoS3b_e8ClassData_507).getD a.val (0, 0)).1) =
        ((levTwoS3b_e8ClassData_507).getD a.val (0, 0)).2 := by
  intro a
  fin_cases a
  · exact levTwoS3b_e8_bfs_507_0

private theorem levTwoS3b_e8_bfs_508 :
    ∀ a : Fin (levTwoS3b_e8ClassData_508).length,
      levTwoS3b_bfsMask (levTwoS3b_e8_permsOf 508) 300
        [((levTwoS3b_e8ClassData_508).getD a.val (0, 0)).1]
        (1 <<< ((levTwoS3b_e8ClassData_508).getD a.val (0, 0)).1) =
        ((levTwoS3b_e8ClassData_508).getD a.val (0, 0)).2 := by
  intro a
  fin_cases a
  · exact levTwoS3b_e8_bfs_508_0
  · exact levTwoS3b_e8_bfs_508_1

private theorem levTwoS3b_e8_bfs_509 :
    ∀ a : Fin (levTwoS3b_e8ClassData_509).length,
      levTwoS3b_bfsMask (levTwoS3b_e8_permsOf 509) 300
        [((levTwoS3b_e8ClassData_509).getD a.val (0, 0)).1]
        (1 <<< ((levTwoS3b_e8ClassData_509).getD a.val (0, 0)).1) =
        ((levTwoS3b_e8ClassData_509).getD a.val (0, 0)).2 := by
  intro a
  fin_cases a
  · exact levTwoS3b_e8_bfs_509_0

private theorem levTwoS3b_e8_cls_orbit_254 :
    ∀ i : Fin levTwoS3b_e8_rootVecs.length,
      ¬ (levTwoS3b_patMask 254).testBit i.val →
      ((levTwoS3b_e8ClassData_254).getD (levTwoS3u_clsOf levTwoS3b_roots
        levTwoS3b_e8ClassData_254 (by decide +kernel)
        (levTwoS3b_e8_rootVecs.get i)).1 (0, 0)).2.testBit i.val = true :=
  levTwoS3u_clsOrbit_of levTwoS3b_e8_hnodup levTwoS3b_e8_hlen _ _ _ (by decide +kernel)

private theorem levTwoS3b_e8_cls_orbit_507 :
    ∀ i : Fin levTwoS3b_e8_rootVecs.length,
      ¬ (levTwoS3b_patMask 507).testBit i.val →
      ((levTwoS3b_e8ClassData_507).getD (levTwoS3u_clsOf levTwoS3b_roots
        levTwoS3b_e8ClassData_507 (by decide +kernel)
        (levTwoS3b_e8_rootVecs.get i)).1 (0, 0)).2.testBit i.val = true :=
  levTwoS3u_clsOrbit_of levTwoS3b_e8_hnodup levTwoS3b_e8_hlen _ _ _ (by decide +kernel)

private theorem levTwoS3b_e8_cls_orbit_508 :
    ∀ i : Fin levTwoS3b_e8_rootVecs.length,
      ¬ (levTwoS3b_patMask 508).testBit i.val →
      ((levTwoS3b_e8ClassData_508).getD (levTwoS3u_clsOf levTwoS3b_roots
        levTwoS3b_e8ClassData_508 (by decide +kernel)
        (levTwoS3b_e8_rootVecs.get i)).1 (0, 0)).2.testBit i.val = true :=
  levTwoS3u_clsOrbit_of levTwoS3b_e8_hnodup levTwoS3b_e8_hlen _ _ _ (by decide +kernel)

private theorem levTwoS3b_e8_cls_orbit_509 :
    ∀ i : Fin levTwoS3b_e8_rootVecs.length,
      ¬ (levTwoS3b_patMask 509).testBit i.val →
      ((levTwoS3b_e8ClassData_509).getD (levTwoS3u_clsOf levTwoS3b_roots
        levTwoS3b_e8ClassData_509 (by decide +kernel)
        (levTwoS3b_e8_rootVecs.get i)).1 (0, 0)).2.testBit i.val = true :=
  levTwoS3u_clsOrbit_of levTwoS3b_e8_hnodup levTwoS3b_e8_hlen _ _ _ (by decide +kernel)

theorem levTwoS3b_e8_tcRoot_254 :
    TCRoot (isFiniteType_cartan Tag.E8) (levTwoS3b_e8_patSet 254) := by
  rw [levTwoS3b_e8_patSet_eq]
  exact levTwoS3b_e8_tcRoot_of_data 254 (by decide +kernel) levTwoS3b_e8ClassData_254
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) levTwoS3b_e8_cls_orbit_254 levTwoS3b_e8_bfs_254

theorem levTwoS3b_e8_tcRoot_507 :
    TCRoot (isFiniteType_cartan Tag.E8) (levTwoS3b_e8_patSet 507) := by
  rw [levTwoS3b_e8_patSet_eq]
  exact levTwoS3b_e8_tcRoot_of_data 507 (by decide +kernel) levTwoS3b_e8ClassData_507
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) levTwoS3b_e8_cls_orbit_507 levTwoS3b_e8_bfs_507

theorem levTwoS3b_e8_tcRoot_508 :
    TCRoot (isFiniteType_cartan Tag.E8) (levTwoS3b_e8_patSet 508) := by
  rw [levTwoS3b_e8_patSet_eq]
  exact levTwoS3b_e8_tcRoot_of_data 508 (by decide +kernel) levTwoS3b_e8ClassData_508
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) levTwoS3b_e8_cls_orbit_508 levTwoS3b_e8_bfs_508

theorem levTwoS3b_e8_tcRoot_509 :
    TCRoot (isFiniteType_cartan Tag.E8) (levTwoS3b_e8_patSet 509) := by
  rw [levTwoS3b_e8_patSet_eq]
  exact levTwoS3b_e8_tcRoot_of_data 509 (by decide +kernel) levTwoS3b_e8ClassData_509
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) levTwoS3b_e8_cls_orbit_509 levTwoS3b_e8_bfs_509

private theorem levTwoS3b_e8_patMask_all_510 :
    ∀ i : Fin levTwoS3b_e8_rootVecs.length, (levTwoS3b_patMask 510).testBit i.val = true := by
  decide +kernel

theorem levTwoS3b_e8_tcRoot_510 :
    TCRoot (isFiniteType_cartan Tag.E8) (levTwoS3b_e8_patSet 510) := by
  rw [levTwoS3b_e8_patSet_eq]
  refine levTwoS3t_tcRoot_of_all (roots := levTwoS3b_e8_rootVecs) (levTwoS3b_e8_hRl) ?_
  intro β hβ
  obtain ⟨i, rfl⟩ := List.mem_iff_get.mp ((levTwoS3b_e8_hRl β).mp hβ)
  exact ⟨i, rfl, levTwoS3b_e8_patMask_all_510 i⟩

end CFSG.StandardType.LevTwo
