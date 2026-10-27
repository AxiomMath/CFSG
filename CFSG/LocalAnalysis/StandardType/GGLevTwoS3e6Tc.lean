module

public import CFSG.LocalAnalysis.StandardType.GGLevTwoS3e6Link
public import CFSG.LocalAnalysis.StandardType.GGLevTwoS3bTables3
public import CFSG.LocalAnalysis.StandardType.GGLevTwoS3bTables4
import CFSG.LocalAnalysis.StandardType.GGLevTwoS3aDict

public section

namespace CFSG.StandardType.LevTwo

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsL33d
open CFSG.LieType.RootSystem
open scoped Matrix

@[expose] def levTwoS3e6_rootVecs : List (Fin (Tag.rank Tag.E6) → ℤ) :=
  levTwoS3e6_roots.map (levTwoS3u_vec (Tag.rank Tag.E6))

theorem levTwoS3e6_rootVecs_len : levTwoS3e6_rootVecs.length = 72 := by
  simp [levTwoS3e6_rootVecs, levTwoS3e6_roots_len]

private theorem levTwoS3e6_hlen : ∀ l ∈ levTwoS3e6_roots, l.length = Tag.rank Tag.E6 := by
  intro l hl
  exact of_decide_eq_true (List.all_eq_true.mp levTwoS3e6_roots_all_length l hl)

theorem levTwoS3e6_rootVecs_getElem (i : Fin levTwoS3e6_rootVecs.length) :
    levTwoS3e6_rootVecs.get i =
      levTwoS3u_vec (Tag.rank Tag.E6) (levTwoS3e6_roots.getD i.val []) := by
  have hlen : levTwoS3e6_rootVecs.length = levTwoS3e6_roots.length := by
    simp [levTwoS3e6_rootVecs]
  have hi : i.val < levTwoS3e6_roots.length := Nat.lt_of_lt_of_eq i.isLt hlen
  rw [List.get_eq_getElem]
  simp only [levTwoS3e6_rootVecs]
  rw [List.getElem_map]
  exact congrArg (levTwoS3u_vec (Tag.rank Tag.E6))
    (List.getD_eq_getElem _ _ hi).symm

theorem levTwoS3e6_mem_patSet_iff (m : ℕ) (β : Fin (Tag.rank Tag.E6) → ℤ) :
    β ∈ levTwoS3e6_patSet m ↔
      ∃ i : Fin levTwoS3e6_rootVecs.length,
        levTwoS3e6_rootVecs.get i = β ∧ (levTwoS3e6_patMask m).testBit i.val := by
  simp only [levTwoS3e6_patSet, Set.mem_setOf_eq]
  constructor
  · rintro ⟨i, hi, hvec, hbit⟩
    refine ⟨⟨i, by rw [levTwoS3e6_rootVecs_len]; exact hi⟩, ?_, hbit⟩
    rw [levTwoS3e6_rootVecs_getElem]
    exact hvec
  · rintro ⟨i, hvec, hbit⟩
    have hi72 : i.val < 72 := Nat.lt_of_lt_of_eq i.isLt levTwoS3e6_rootVecs_len
    refine ⟨i.val, hi72, ?_, hbit⟩
    rw [levTwoS3e6_rootVecs_getElem] at hvec
    exact hvec

@[expose] def levTwoS3e6_patSetF (m : ℕ) : Set (Fin (Tag.rank Tag.E6) → ℤ) :=
  {β | ∃ i : Fin levTwoS3e6_rootVecs.length,
    levTwoS3e6_rootVecs.get i = β ∧ (levTwoS3e6_patMask m).testBit i.val}

theorem levTwoS3e6_patSetF_eq (m : ℕ) : levTwoS3e6_patSetF m = levTwoS3e6_patSet m :=
  Set.ext (fun β => (levTwoS3e6_mem_patSet_iff m β).symm)

theorem levTwoS3e6_rootVecs_isRoot_iff
    (β : Fin (Tag.rank Tag.E6) → ℤ) :
    IsRt (isFiniteType_cartan Tag.E6) β ↔ β ∈ levTwoS3e6_rootVecs := by
  have hRl0 : ∀ β : Fin (Tag.rank Tag.E6) → ℤ,
      IsRt (isFiniteType_cartan Tag.E6) β ↔ List.ofFn β ∈ levTwoS3e6_roots := by
    intro β
    rw [levTwoS3a_isRt_iff]
    change IsRoot Tag.E6 β ↔ List.ofFn β ∈ Tag.artifactRoots Tag.E6
    exact isRoot_iff_mem_artifactRoots
  simpa only [levTwoS3e6_rootVecs] using levTwoS3u_isRt_iff_mem_ofFn levTwoS3e6_hlen hRl0 β

theorem levTwoS3e6_genVec_length (x : ℕ) :
    (levTwoS3e6_genVec x).length = Tag.rank Tag.E6 := by
  rcases x with _ | j
  · rfl
  · simp only [levTwoS3e6_genVec, levTwoS3e6_unit, List.length_map, List.length_range]
    decide +kernel

theorem levTwoS3e6_genVec_mem_all :
    (List.range 7).all (fun x => decide (levTwoS3e6_genVec x ∈ levTwoS3e6_roots)) = true := by
  decide +kernel

theorem levTwoS3e6_perm_valid_all (x : Fin 7) :
    ∀ i : Fin 72,
      levTwoS3e6_roots.getD ((levTwoS3e6_e6Perms.getD x.val []).getD i.val 0) [] =
        levTwoS3e6_reflv (levTwoS3e6_genVec x.val) (levTwoS3e6_roots.getD i.val []) := by
  fin_cases x
  · exact levTwoS3e6_e6Perm_valid_0
  · exact levTwoS3e6_e6Perm_valid_1
  · exact levTwoS3e6_e6Perm_valid_2
  · exact levTwoS3e6_e6Perm_valid_3
  · exact levTwoS3e6_e6Perm_valid_4
  · exact levTwoS3e6_e6Perm_valid_5
  · exact levTwoS3e6_e6Perm_valid_6

@[expose] def levTwoS3e6_e6GensOfMask (m : ℕ) : List ((Fin (Tag.rank Tag.E6) → ℤ) × List ℕ) :=
  (levTwoS3e6_nodesOf m).map (fun x =>
    (levTwoS3u_vec (Tag.rank Tag.E6) (levTwoS3e6_genVec x), levTwoS3e6_e6Perms.getD x []))

@[expose] def levTwoS3e6_e6BasePermsLit (m : ℕ) : List (List ℕ) :=
  levTwoS3e6_e6NegPerm :: (levTwoS3e6_nodesOf m).map (fun x => levTwoS3e6_e6Perms.getD x [])

@[expose] def levTwoS3e6_reflPerm (β : Fin (Tag.rank Tag.E6) → ℤ) : List ℕ :=
  levTwoS3e6_permOf (List.ofFn β)

private theorem levTwoS3e6_gens_mem (m : ℕ)
    (hcheck : (List.range 7).all (fun x =>
      !(m.testBit x) || levTwoS3e6_inPat m (levTwoS3e6_genVec x)) = true) :
    ∀ gp ∈ levTwoS3e6_e6GensOfMask m, gp.1 ∈ levTwoS3e6_patSet m := by
  intro gp hgp
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hgp
  have hxmem : x ∈ List.range 7 := (List.mem_filter.mp hx).1
  have hxbit : m.testBit x = true := (List.mem_filter.mp hx).2
  have hin : levTwoS3e6_inPat m (levTwoS3e6_genVec x) = true := by
    have hthis := List.all_eq_true.mp hcheck x hxmem
    rw [Bool.or_eq_true] at hthis
    rcases hthis with h | h
    · simp [hxbit] at h
    · exact h
  change levTwoS3u_vec (Tag.rank Tag.E6) (levTwoS3e6_genVec x) ∈ levTwoS3e6_patSet m
  rw [levTwoS3e6_mem_patSet]
  refine ⟨?_, ?_⟩
  · exact (levTwoS3e6_isRoot_iff_mem).mpr (by
      rw [levTwoS3u_ofFn_vec (Tag.rank Tag.E6) (levTwoS3e6_genVec_length x)]
      exact of_decide_eq_true (List.all_eq_true.mp levTwoS3e6_genVec_mem_all x hxmem))
  · rw [levTwoS3u_ofFn_vec (Tag.rank Tag.E6) (levTwoS3e6_genVec_length x)]
    exact hin

private theorem levTwoS3e6_gens_step
    (m : ℕ) :
    ∀ gp ∈ levTwoS3e6_e6GensOfMask m,
      levTwoS3b_reflectStep (isFiniteType_cartan Tag.E6) levTwoS3e6_rootVecs gp.1 gp.2 := by
  intro gp hgp
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hgp
  have hxmem : x ∈ List.range 7 := (List.mem_filter.mp hx).1
  have hx7 : x < 7 := List.mem_range.mp hxmem
  have hg : levTwoS3e6_genVec x ∈ levTwoS3e6_roots :=
    of_decide_eq_true (List.all_eq_true.mp levTwoS3e6_genVec_mem_all x hxmem)
  have hgrt : IsRt (isFiniteType_cartan Tag.E6)
      (levTwoS3u_vec (Tag.rank Tag.E6) (levTwoS3e6_genVec x)) :=
    (levTwoS3e6_rootVecs_isRoot_iff _).mpr (List.mem_map.mpr ⟨_, hg, rfl⟩)
  exact levTwoS3u_reflectStep_of_list (n := Tag.rank Tag.E6) (roots := levTwoS3e6_roots)
    levTwoS3e6_hlen (fun β => levTwoS3e6_rootVecs_isRoot_iff β) (reflv := levTwoS3e6_reflv)
    (fun g v hgv hvv hig hiv =>
      levTwoS3e6_e6_weylAction_reflv (levTwoS3a_isRt_iff.mp hig) (levTwoS3a_isRt_iff.mp hiv)
        hgv hvv)
    (levTwoS3e6_genVec_length x) hgrt
    (fun i hi => levTwoS3e6_perm_valid_all ⟨x, hx7⟩
      ⟨i, by rwa [levTwoS3e6_roots_len] at hi⟩)

private theorem levTwoS3e6_negStep :
    levTwoS3b_negStep levTwoS3e6_rootVecs levTwoS3e6_e6NegPerm :=
  levTwoS3u_negStep_of_list (n := Tag.rank Tag.E6) (roots := levTwoS3e6_roots)
    (fun i hi => levTwoS3e6_e6NegPerm_valid
      ⟨i, by rwa [levTwoS3e6_roots_len] at hi⟩)

theorem levTwoS3e6_reflStep_of_list_check
    {g : List ℤ} (hglen : g.length = Tag.rank Tag.E6)
    (hgrt : IsRt (isFiniteType_cartan Tag.E6) (levTwoS3u_vec (Tag.rank Tag.E6) g))
    (hcheck : ∀ i : Fin 72,
      levTwoS3e6_roots.getD ((levTwoS3e6_permOf g).getD i.val 0) [] =
        levTwoS3e6_reflv g (levTwoS3e6_roots.getD i.val [])) :
    levTwoS3b_reflectStep (isFiniteType_cartan Tag.E6) levTwoS3e6_rootVecs
      (levTwoS3u_vec (Tag.rank Tag.E6) g) (levTwoS3e6_permOf g) := by
  refine levTwoS3u_reflectStep_of_list (n := Tag.rank Tag.E6) (roots := levTwoS3e6_roots)
    levTwoS3e6_hlen (fun β => levTwoS3e6_rootVecs_isRoot_iff β) (reflv := levTwoS3e6_reflv)
    (fun g v hgv hvv hig hiv =>
      levTwoS3e6_e6_weylAction_reflv (levTwoS3a_isRt_iff.mp hig) (levTwoS3a_isRt_iff.mp hiv)
        hgv hvv) hglen hgrt
    (fun i hi => hcheck ⟨i, by rwa [levTwoS3e6_roots_len] at hi⟩)

private theorem levTwoS3e6_permsOf_sub (m : ℕ) :
    ∀ p ∈ levTwoS3e6_e6BasePermsLit m, p ∈ levTwoS3e6_e6NegPerm :: levTwoS3e6_e6Perms := by
  intro p hp
  rcases List.mem_cons.mp hp with rfl | hp
  · exact List.mem_cons_self ..
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hp
    have hx7 : x < 7 := List.mem_range.mp (List.mem_filter.mp hx).1
    have hlen : levTwoS3e6_e6Perms.length = 7 := by decide +kernel
    have hx' : x < levTwoS3e6_e6Perms.length := by rw [hlen]; exact hx7
    rw [List.getD_eq_get _ _ ⟨x, hx'⟩]
    exact List.mem_cons_of_mem _ (List.get_mem _ _)

private theorem levTwoS3e6_e6Base_inv :
    (levTwoS3e6_e6NegPerm :: levTwoS3e6_e6Perms).all (fun p =>
      (List.range levTwoS3e6_rootVecs.length).all
        (fun i => p.getD (p.getD i 0) 0 == i)) = true := by
  decide +kernel

private theorem levTwoS3e6_e6Base_range :
    (levTwoS3e6_e6NegPerm :: levTwoS3e6_e6Perms).all (fun p =>
      (List.range levTwoS3e6_rootVecs.length).all (fun i => decide (p.getD i 0 <
        levTwoS3e6_rootVecs.length))) = true := by
  decide +kernel

private theorem levTwoS3e6_inv (m : ℕ) :
    ∀ p ∈ levTwoS3e6_e6BasePermsLit m, ∀ i, i < levTwoS3e6_rootVecs.length →
      p.getD (p.getD i 0) 0 = i :=
  levTwoS3u_inv_of_all levTwoS3e6_e6Base_inv (levTwoS3e6_permsOf_sub m)

private theorem levTwoS3e6_range (m : ℕ) :
    ∀ p ∈ levTwoS3e6_e6BasePermsLit m, ∀ i, i < levTwoS3e6_rootVecs.length →
      p.getD i 0 < levTwoS3e6_rootVecs.length :=
  levTwoS3u_range_of_all levTwoS3e6_e6Base_range (levTwoS3e6_permsOf_sub m)

private theorem levTwoS3e6_inPat_all_63 :
    (List.range 72).all (fun i => levTwoS3e6_inPat 63 (levTwoS3e6_roots.getD i [])) = true := by
  decide +kernel

private theorem levTwoS3e6_inPat_all_125 :
    (List.range 72).all (fun i => levTwoS3e6_inPat 125 (levTwoS3e6_roots.getD i [])) = true := by
  decide +kernel

private theorem levTwoS3e6_inPat_all_126 :
    (List.range 72).all (fun i => levTwoS3e6_inPat 126 (levTwoS3e6_roots.getD i [])) = true := by
  decide +kernel

private theorem levTwoS3e6_patMask_testBit_of_all {m : ℕ}
    (h : (List.range 72).all (fun i => levTwoS3e6_inPat m (levTwoS3e6_roots.getD i [])) = true)
    (i : Fin 72) : (levTwoS3e6_patMask m).testBit i.val = true := by
  rw [levTwoS3e6_patMask_testBit]
  exact ⟨i.isLt, List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt)⟩

private theorem levTwoS3e6_tcRoot_of_all_of_inPat {m : ℕ}
    (h : (List.range 72).all (fun i => levTwoS3e6_inPat m (levTwoS3e6_roots.getD i [])) = true) :
    TCRoot (isFiniteType_cartan Tag.E6) (levTwoS3e6_patSet m) := by
  refine levTwoS3t_tcRoot_of_all (roots := levTwoS3e6_rootVecs)
    levTwoS3e6_rootVecs_isRoot_iff ?_
  intro β hβ
  rw [levTwoS3e6_mem_patSet_iff]
  have hmem := (levTwoS3e6_rootVecs_isRoot_iff β).mp hβ
  obtain ⟨i, hi, hri⟩ := List.getElem_of_mem hmem
  exact ⟨⟨i, hi⟩, hri, levTwoS3e6_patMask_testBit_of_all h ⟨i, hi⟩⟩

theorem levTwoS3e6_tcRoot_63 :
    TCRoot (isFiniteType_cartan Tag.E6) (levTwoS3e6_patSet 63) :=
  levTwoS3e6_tcRoot_of_all_of_inPat levTwoS3e6_inPat_all_63

theorem levTwoS3e6_tcRoot_125 :
    TCRoot (isFiniteType_cartan Tag.E6) (levTwoS3e6_patSet 125) :=
  levTwoS3e6_tcRoot_of_all_of_inPat levTwoS3e6_inPat_all_125

theorem levTwoS3e6_tcRoot_126 :
    TCRoot (isFiniteType_cartan Tag.E6) (levTwoS3e6_patSet 126) :=
  levTwoS3e6_tcRoot_of_all_of_inPat levTwoS3e6_inPat_all_126

private theorem levTwoS3e6_tcRoot_of_data
    (m : ℕ)
    (hgen : (List.range 7).all (fun x =>
      !(m.testBit x) || levTwoS3e6_inPat m (levTwoS3e6_genVec x)) = true)
    (cl : List (ℕ × ℕ)) (hpos : 0 < cl.length) (hlen2 : cl.length ≤ 2)
    (hcl_rep_lt : ∀ a : Fin cl.length,
      (cl.getD a.val (0, 0)).1 < levTwoS3e6_rootVecs.length)
    (hrep_notpat : ∀ a : Fin cl.length,
      ¬ (levTwoS3e6_patMask m).testBit (cl.getD a.val (0, 0)).1)
    (hrep_cls : ∀ a : Fin cl.length,
      levTwoS3u_clsOf levTwoS3e6_roots cl hpos
        (levTwoS3u_repOf (n := Tag.rank Tag.E6) levTwoS3e6_roots cl a) = a)
    (hcls_orbit : ∀ i : Fin levTwoS3e6_rootVecs.length,
      ¬ (levTwoS3e6_patMask m).testBit i.val →
      (cl.getD (levTwoS3u_clsOf levTwoS3e6_roots cl hpos
        (levTwoS3e6_rootVecs.get i)).1 (0, 0)).2.testBit i.val = true)
    (hcl_bfs : ∀ a : Fin cl.length,
      levTwoS3b_bfsMask (levTwoS3e6_e6BasePermsLit m) 300
        [(cl.getD a.val (0, 0)).1] (1 <<< (cl.getD a.val (0, 0)).1) =
          (cl.getD a.val (0, 0)).2) :
    TCRoot (isFiniteType_cartan Tag.E6) (levTwoS3e6_patSet m) := by
  have hrep_mem : ∀ a : Fin cl.length,
      levTwoS3u_repOf (n := Tag.rank Tag.E6) levTwoS3e6_roots cl a ∈ levTwoS3e6_rootVecs :=
    levTwoS3u_rep_mem (fun a => hcl_rep_lt a)
  have hrep_notMemF : ∀ a : Fin cl.length,
      levTwoS3u_repOf (n := Tag.rank Tag.E6) levTwoS3e6_roots cl a ∉ levTwoS3e6_patSetF m :=
    levTwoS3u_notMem_patSet_of_not_bit levTwoS3e6_roots_nodup levTwoS3e6_hlen hcl_rep_lt
      hrep_notpat
  have hrep_notMem : ∀ a : Fin cl.length,
      levTwoS3u_repOf (n := Tag.rank Tag.E6) levTwoS3e6_roots cl a ∉ levTwoS3e6_patSet m := by
    intro a
    rw [← levTwoS3e6_patSetF_eq]
    exact hrep_notMemF a
  have hrep_notMem_imp : ∀ a : Fin cl.length,
      (∃ r ∈ levTwoS3e6_rootVecs, r ∉ levTwoS3e6_patSet m ∧
        levTwoS3u_clsOf levTwoS3e6_roots cl hpos r = a) →
      levTwoS3u_repOf (n := Tag.rank Tag.E6) levTwoS3e6_roots cl a ∉ levTwoS3e6_patSet m :=
    fun a _ => hrep_notMem a
  have hΦrt : ∀ β ∈ levTwoS3e6_patSet m, IsRt (isFiniteType_cartan Tag.E6) β := by
    intro β hβ
    rw [← levTwoS3e6_patSetF_eq] at hβ
    exact levTwoS3u_isRt_of_mem_patSet levTwoS3e6_rootVecs_isRoot_iff (fun _ => Iff.rfl) β hβ
  exact levTwoS3t_tcRoot_of_tables_of_cover
    (roots := levTwoS3e6_rootVecs) (hRl := levTwoS3e6_rootVecs_isRoot_iff)
    (pm := levTwoS3e6_patMask m) (Φ := levTwoS3e6_patSet m)
    (hΦ := levTwoS3e6_mem_patSet_iff m) (hΦrt := hΦrt)
    (gens := levTwoS3e6_e6GensOfMask m) (negP := levTwoS3e6_e6NegPerm)
    (perms := levTwoS3e6_e6BasePermsLit m)
    (hperms := by
      simp only [levTwoS3e6_e6BasePermsLit, levTwoS3e6_e6GensOfMask, List.map_map]
      rfl)
    (hgen_mem := levTwoS3e6_gens_mem m hgen)
    (hgen_step := levTwoS3e6_gens_step m)
    (hneg := levTwoS3e6_negStep)
    (hinv := levTwoS3e6_inv m) (hrange := levTwoS3e6_range m)
    (cl := cl) (cls := levTwoS3u_clsOf levTwoS3e6_roots cl hpos)
    (rep := levTwoS3u_repOf (n := Tag.rank Tag.E6) levTwoS3e6_roots cl)
    (hrep_mem := hrep_mem) (hrep_cls := hrep_cls) (hrep_notMem := hrep_notMem_imp)
    (hcls_orbit := hcls_orbit)
    (hcl_bfs := fun a ha => hcl_bfs ⟨a, ha⟩)
    (hcl_rep_lt := fun a ha => hcl_rep_lt ⟨a, ha⟩)
    (hcover := levTwoS3t_cover_refl
      (levTwoS3u_repOf (n := Tag.rank Tag.E6) levTwoS3e6_roots cl) levTwoS3e6_rootVecs
      (levTwoS3e6_patSet m) (levTwoS3u_clsOf levTwoS3e6_roots cl hpos)
      hrep_mem hrep_cls hrep_notMem_imp hlen2)

theorem levTwoS3e6_tcRoot_of_data_ws
    (m : ℕ)
    (hgen : (List.range 7).all (fun x =>
      !(m.testBit x) || levTwoS3e6_inPat m (levTwoS3e6_genVec x)) = true)
    (cl : List (ℕ × ℕ)) (hpos : 0 < cl.length)
    (hcl_rep_lt : ∀ a : Fin cl.length,
      (cl.getD a.val (0, 0)).1 < levTwoS3e6_rootVecs.length)
    (hrep_notpat : ∀ a : Fin cl.length,
      ¬ (levTwoS3e6_patMask m).testBit (cl.getD a.val (0, 0)).1)
    (hrep_cls : ∀ a : Fin cl.length,
      levTwoS3u_clsOf levTwoS3e6_roots cl hpos
        (levTwoS3u_repOf (n := Tag.rank Tag.E6) levTwoS3e6_roots cl a) = a)
    (hcls_orbit : ∀ i : Fin levTwoS3e6_rootVecs.length,
      ¬ (levTwoS3e6_patMask m).testBit i.val →
      (cl.getD (levTwoS3u_clsOf levTwoS3e6_roots cl hpos
        (levTwoS3e6_rootVecs.get i)).1 (0, 0)).2.testBit i.val = true)
    (hcl_bfs : ∀ a : Fin cl.length,
      levTwoS3b_bfsMask (levTwoS3e6_e6BasePermsLit m) 300
        [(cl.getD a.val (0, 0)).1] (1 <<< (cl.getD a.val (0, 0)).1) =
          (cl.getD a.val (0, 0)).2)
    (hrefl : ∀ a : Fin cl.length,
      levTwoS3b_reflectStep (isFiniteType_cartan Tag.E6) levTwoS3e6_rootVecs
        (levTwoS3u_repOf (n := Tag.rank Tag.E6) levTwoS3e6_roots cl a)
        (levTwoS3e6_reflPerm (levTwoS3u_repOf (n := Tag.rank Tag.E6) levTwoS3e6_roots cl a)))
    (ws : List (List (Fin cl.length) × List (Fin cl.length)))
    (hws : ws.all (fun w => decide (w.2.length ≤ 2) && w.2.all (fun a => decide (a ∈ w.1)) &&
      levTwoS3t_coversWith levTwoS3e6_reflPerm cl
        (levTwoS3u_repOf (n := Tag.rank Tag.E6) levTwoS3e6_roots cl)
        (levTwoS3e6_e6BasePermsLit m) [] w.1 w.2) = true)
    (hall : ∀ T : Finset (Fin cl.length), ∃ w ∈ ws, ∀ a, a ∈ w.1 ↔ a ∈ T) :
    TCRoot (isFiniteType_cartan Tag.E6) (levTwoS3e6_patSet m) := by
  have hrep_mem : ∀ a : Fin cl.length,
      levTwoS3u_repOf (n := Tag.rank Tag.E6) levTwoS3e6_roots cl a ∈ levTwoS3e6_rootVecs :=
    levTwoS3u_rep_mem (fun a => hcl_rep_lt a)
  have hrep_notMemF : ∀ a : Fin cl.length,
      levTwoS3u_repOf (n := Tag.rank Tag.E6) levTwoS3e6_roots cl a ∉ levTwoS3e6_patSetF m :=
    levTwoS3u_notMem_patSet_of_not_bit levTwoS3e6_roots_nodup levTwoS3e6_hlen hcl_rep_lt
      hrep_notpat
  have hrep_notMem : ∀ a : Fin cl.length,
      levTwoS3u_repOf (n := Tag.rank Tag.E6) levTwoS3e6_roots cl a ∉ levTwoS3e6_patSet m := by
    intro a
    rw [← levTwoS3e6_patSetF_eq]
    exact hrep_notMemF a
  have hrep_notMem_imp : ∀ a : Fin cl.length,
      (∃ r ∈ levTwoS3e6_rootVecs, r ∉ levTwoS3e6_patSet m ∧
        levTwoS3u_clsOf levTwoS3e6_roots cl hpos r = a) →
      levTwoS3u_repOf (n := Tag.rank Tag.E6) levTwoS3e6_roots cl a ∉ levTwoS3e6_patSet m :=
    fun a _ => hrep_notMem a
  have hrep_eq : ∀ a : Fin cl.length,
      levTwoS3u_repOf (n := Tag.rank Tag.E6) levTwoS3e6_roots cl a
        = levTwoS3e6_rootVecs.getD (cl.getD a.val (0, 0)).1 0 :=
    fun a => (levTwoS3u_getD_map (Tag.rank Tag.E6) levTwoS3e6_roots _).symm
  have hcoverW := levTwoS3v_hcoverW_of_table (cl := cl)
    (rep := levTwoS3u_repOf (n := Tag.rank Tag.E6) levTwoS3e6_roots cl)
    levTwoS3e6_reflPerm (levTwoS3e6_e6BasePermsLit m) [] ws hws hall
  have hΦrt : ∀ β ∈ levTwoS3e6_patSet m, IsRt (isFiniteType_cartan Tag.E6) β := by
    intro β hβ
    rw [← levTwoS3e6_patSetF_eq] at hβ
    exact levTwoS3u_isRt_of_mem_patSet levTwoS3e6_rootVecs_isRoot_iff (fun _ => Iff.rfl) β hβ
  exact levTwoS3v_tcRoot_of_tables_ws
    (roots := levTwoS3e6_rootVecs) (hRl := levTwoS3e6_rootVecs_isRoot_iff)
    (pm := levTwoS3e6_patMask m) (Φ := levTwoS3e6_patSet m)
    (hΦ := levTwoS3e6_mem_patSet_iff m) (hΦrt := hΦrt)
    (gens := levTwoS3e6_e6GensOfMask m) (negP := levTwoS3e6_e6NegPerm)
    (perms := levTwoS3e6_e6BasePermsLit m)
    (hperms := by
      simp only [levTwoS3e6_e6BasePermsLit, levTwoS3e6_e6GensOfMask, List.map_map]
      rfl)
    (reflPerm := levTwoS3e6_reflPerm)
    (hgen_mem := levTwoS3e6_gens_mem m hgen)
    (hgen_step := levTwoS3e6_gens_step m)
    (hneg := levTwoS3e6_negStep)
    (hinv := levTwoS3e6_inv m) (hrange := levTwoS3e6_range m)
    (cl := cl) (cls := levTwoS3u_clsOf levTwoS3e6_roots cl hpos)
    (rep := levTwoS3u_repOf (n := Tag.rank Tag.E6) levTwoS3e6_roots cl)
    (hrep_mem := hrep_mem) (hrep_cls := hrep_cls) (hrep_notMem := hrep_notMem_imp)
    (hrep_eq := hrep_eq) (hrefl := hrefl)
    (hcls_orbit := hcls_orbit)
    (hcl_bfs := fun a ha => hcl_bfs ⟨a, ha⟩)
    (hcl_rep_lt := fun a ha => hcl_rep_lt ⟨a, ha⟩)
    (seed := []) (hseed := by intro i hi; simp at hi)
    (hcoverW := hcoverW)

theorem levTwoS3e6_tcRoot_31 :
    TCRoot (isFiniteType_cartan Tag.E6) (levTwoS3e6_patSet 31) :=
  levTwoS3e6_tcRoot_of_data 31 (by decide +kernel) levTwoS3e6_e6ClassData_31 (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

theorem levTwoS3e6_tcRoot_61 :
    TCRoot (isFiniteType_cartan Tag.E6) (levTwoS3e6_patSet 61) :=
  levTwoS3e6_tcRoot_of_data 61 (by decide +kernel) levTwoS3e6_e6ClassData_61 (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

theorem levTwoS3e6_tcRoot_62 :
    TCRoot (isFiniteType_cartan Tag.E6) (levTwoS3e6_patSet 62) :=
  levTwoS3e6_tcRoot_of_data 62 (by decide +kernel) levTwoS3e6_e6ClassData_62 (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

theorem levTwoS3e6_tcRoot_117 :
    TCRoot (isFiniteType_cartan Tag.E6) (levTwoS3e6_patSet 117) :=
  levTwoS3e6_tcRoot_of_data 117 (by decide +kernel) levTwoS3e6_e6ClassData_117 (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

theorem levTwoS3e6_tcRoot_122 :
    TCRoot (isFiniteType_cartan Tag.E6) (levTwoS3e6_patSet 122) :=
  levTwoS3e6_tcRoot_of_data 122 (by decide +kernel) levTwoS3e6_e6ClassData_122 (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

theorem levTwoS3e6_tcRoot_124 :
    TCRoot (isFiniteType_cartan Tag.E6) (levTwoS3e6_patSet 124) :=
  levTwoS3e6_tcRoot_of_data 124 (by decide +kernel) levTwoS3e6_e6ClassData_124 (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
end CFSG.StandardType.LevTwo
