module

public import CFSG.LocalAnalysis.StandardType.GGLevTwoS3e7Sem
public import CFSG.LocalAnalysis.StandardType.GGLevTwoS3bTables3
import CFSG.LocalAnalysis.StandardType.GGLevTwoS3aDict

public section

namespace CFSG.StandardType.LevTwo

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsL33d
open CFSG.LieType.RootSystem
open scoped Matrix

@[expose] def levTwoS3e7_rootVecs : List (Fin (Tag.rank Tag.E7) → ℤ) :=
  levTwoS3e7_roots.map (levTwoS3u_vec (Tag.rank Tag.E7))

@[expose] def levTwoS3e7_patSetFin (m : ℕ) : Set (Fin (Tag.rank Tag.E7) → ℤ) :=
  {β | ∃ i : Fin levTwoS3e7_rootVecs.length,
    levTwoS3e7_rootVecs.get i = β ∧ (levTwoS3e7_patMask m).testBit i.val}

@[expose] def levTwoS3e7_gensOf (m : ℕ) : List ((Fin (Tag.rank Tag.E7) → ℤ) × List ℕ) :=
  (levTwoS3e7_nodesOf m).map (fun x =>
    (levTwoS3u_vec (Tag.rank Tag.E7) (levTwoS3e7_genVec x), levTwoS3e7_perms.getD x []))

@[expose] def levTwoS3e7_permsOf (m : ℕ) : List (List ℕ) :=
  levTwoS3e7_negPermList :: (levTwoS3e7_nodesOf m).map (fun x => levTwoS3e7_perms.getD x [])

private theorem levTwoS3e7_hlen : ∀ l ∈ levTwoS3e7_roots, l.length = Tag.rank Tag.E7 := by
  intro l hl
  simp only [levTwoS3e7_roots] at hl
  exact length_of_mem_artifactRoots hl

private theorem levTwoS3e7_hnodup :
    levTwoS3e7_roots.Nodup := by
  simpa only [levTwoS3e7_roots] using nodup_artifactRoots (τ := Tag.E7)

private theorem levTwoS3e7_hRl :
    ∀ β : Fin (Tag.rank Tag.E7) → ℤ,
      IsRt (isFiniteType_cartan Tag.E7) β ↔ β ∈ levTwoS3e7_rootVecs := by
  have hRl0 : ∀ β : Fin (Tag.rank Tag.E7) → ℤ,
      IsRt (isFiniteType_cartan Tag.E7) β ↔ List.ofFn β ∈ levTwoS3e7_roots := by
    intro β
    rw [levTwoS3a_isRt_iff]
    change IsRoot Tag.E7 β ↔ List.ofFn β ∈ Tag.artifactRoots Tag.E7
    exact isRoot_iff_mem_artifactRoots
  exact levTwoS3u_isRt_iff_mem_ofFn levTwoS3e7_hlen hRl0

private theorem levTwoS3e7_genVec_length (x : ℕ) :
    (levTwoS3e7_genVec x).length = Tag.rank Tag.E7 := by
  rcases x with _ | j <;> rfl

private theorem levTwoS3e7_genVec_mem_all :
    (List.range 8).all (fun x => decide (levTwoS3e7_genVec x ∈ levTwoS3e7_roots)) = true := by
  decide +kernel

private theorem levTwoS3e7_perm_valid_all (x : Fin 8) :
    ∀ i : Fin 126,
      levTwoS3e7_roots.getD ((levTwoS3e7_perms.getD x.val []).getD i.val 0) [] =
        levTwoS3e7_reflv (levTwoS3e7_genVec x.val) (levTwoS3e7_roots.getD i.val []) := by
  fin_cases x
  · exact levTwoS3e7_perm_valid_0
  · exact levTwoS3e7_perm_valid_1
  · exact levTwoS3e7_perm_valid_2
  · exact levTwoS3e7_perm_valid_3
  · exact levTwoS3e7_perm_valid_4
  · exact levTwoS3e7_perm_valid_5
  · exact levTwoS3e7_perm_valid_6
  · exact levTwoS3e7_perm_valid_7

private theorem levTwoS3e7_gens_mem (m : ℕ)
    (hcheck : (List.range 8).all (fun x =>
      !(m.testBit x) || levTwoS3e7_inPat m (levTwoS3e7_genVec x)) = true) :
    ∀ gp ∈ levTwoS3e7_gensOf m, gp.1 ∈ levTwoS3e7_patSetFin m := by
  intro gp hgp
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hgp
  have hxmem : x ∈ List.range 8 := (List.mem_filter.mp hx).1
  have hxbit : m.testBit x = true := (List.mem_filter.mp hx).2
  have hg : levTwoS3e7_genVec x ∈ levTwoS3e7_roots :=
    of_decide_eq_true ((List.all_eq_true.mp levTwoS3e7_genVec_mem_all) x hxmem)
  have hin : levTwoS3e7_inPat m (levTwoS3e7_genVec x) = true := by
    have hthis := (List.all_eq_true.mp hcheck) x hxmem
    rw [Bool.or_eq_true] at hthis
    rcases hthis with h | h
    · simp [hxbit] at h
    · exact h
  exact levTwoS3u_gen_mem (n := Tag.rank Tag.E7) (N := 126) (by decide +kernel) (levTwoS3e7_inPat m)
    (pm := levTwoS3e7_patMask m) (by rfl) hg hin

private theorem levTwoS3e7_gens_step
    (m : ℕ) :
    ∀ gp ∈ levTwoS3e7_gensOf m,
      levTwoS3b_reflectStep (isFiniteType_cartan Tag.E7) levTwoS3e7_rootVecs gp.1 gp.2 := by
  intro gp hgp
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hgp
  have hxmem : x ∈ List.range 8 := (List.mem_filter.mp hx).1
  have hx8 : x < 8 := List.mem_range.mp hxmem
  have hg : levTwoS3e7_genVec x ∈ levTwoS3e7_roots :=
    of_decide_eq_true ((List.all_eq_true.mp levTwoS3e7_genVec_mem_all) x hxmem)
  have hgrt : IsRt (isFiniteType_cartan Tag.E7)
      (levTwoS3u_vec (Tag.rank Tag.E7) (levTwoS3e7_genVec x)) :=
    (levTwoS3e7_hRl _).mpr (List.mem_map.mpr ⟨_, hg, rfl⟩)
  exact levTwoS3u_reflectStep_of_list levTwoS3e7_hlen (fun β => levTwoS3e7_hRl β)
    (reflv := levTwoS3e7_reflv)
    (fun g v hgv hvv hig hiv =>
      levTwoS3e7_weylAction_reflv (levTwoS3a_isRt_iff.mp hig) (levTwoS3a_isRt_iff.mp hiv)
        hgv hvv)
    (levTwoS3e7_genVec_length x) hgrt
    (fun i hi => levTwoS3e7_perm_valid_all ⟨x, hx8⟩ ⟨i, hi⟩)

private theorem levTwoS3e7_negStep :
    levTwoS3b_negStep levTwoS3e7_rootVecs levTwoS3e7_negPermList :=
  levTwoS3u_negStep_of_list (n := Tag.rank Tag.E7) (roots := levTwoS3e7_roots)
    (fun i hi => levTwoS3e7_negPerm_valid ⟨i, hi⟩)

private theorem levTwoS3e7_permsOf_sub (m : ℕ) :
    ∀ p ∈ levTwoS3e7_permsOf m, p ∈ levTwoS3e7_negPermList :: levTwoS3e7_perms := by
  intro p hp
  rcases List.mem_cons.mp hp with rfl | hp
  · exact List.mem_cons_self ..
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hp
    have hx8 : x < 8 := List.mem_range.mp (List.mem_filter.mp hx).1
    have hlen : levTwoS3e7_perms.length = 8 := by decide +kernel
    have hx' : x < levTwoS3e7_perms.length := by rw [hlen]; exact hx8
    rw [List.getD_eq_get _ _ ⟨x, hx'⟩]
    exact List.mem_cons_of_mem _ (List.get_mem _ _)

private theorem levTwoS3e7_base_inv :
    (levTwoS3e7_negPermList :: levTwoS3e7_perms).all (fun p =>
      (List.range levTwoS3e7_rootVecs.length).all
        (fun i => p.getD (p.getD i 0) 0 == i)) = true := by
  decide +kernel

private theorem levTwoS3e7_base_range :
    (levTwoS3e7_negPermList :: levTwoS3e7_perms).all (fun p =>
      (List.range levTwoS3e7_rootVecs.length).all (fun i => decide (p.getD i 0 <
        levTwoS3e7_rootVecs.length))) = true := by
  decide +kernel

private theorem levTwoS3e7_inv (m : ℕ) :
    ∀ p ∈ levTwoS3e7_permsOf m, ∀ i, i < levTwoS3e7_rootVecs.length →
      p.getD (p.getD i 0) 0 = i :=
  levTwoS3u_inv_of_all levTwoS3e7_base_inv (levTwoS3e7_permsOf_sub m)

private theorem levTwoS3e7_range (m : ℕ) :
    ∀ p ∈ levTwoS3e7_permsOf m, ∀ i, i < levTwoS3e7_rootVecs.length →
      p.getD i 0 < levTwoS3e7_rootVecs.length :=
  levTwoS3u_range_of_all levTwoS3e7_base_range (levTwoS3e7_permsOf_sub m)

private theorem levTwoS3e7_tcRoot_of_data
    (m : ℕ)
    (hgen : (List.range 8).all (fun x =>
      !(m.testBit x) || levTwoS3e7_inPat m (levTwoS3e7_genVec x)) = true)
    (cl : List (ℕ × ℕ)) (hpos : 0 < cl.length) (hlen2 : cl.length ≤ 2)
    (hcl_rep_lt : ∀ a : Fin cl.length,
      (cl.getD a.val (0, 0)).1 < levTwoS3e7_rootVecs.length)
    (hrep_notpat : ∀ a : Fin cl.length,
      ¬ (levTwoS3e7_patMask m).testBit (cl.getD a.val (0, 0)).1)
    (hrep_cls : ∀ a : Fin cl.length,
      levTwoS3u_clsOf levTwoS3e7_roots cl hpos
        (levTwoS3u_repOf (n := Tag.rank Tag.E7) levTwoS3e7_roots cl a) = a)
    (hcls_orbit : ∀ i : Fin levTwoS3e7_rootVecs.length,
      ¬ (levTwoS3e7_patMask m).testBit i.val →
      (cl.getD (levTwoS3u_clsOf levTwoS3e7_roots cl hpos
        (levTwoS3e7_rootVecs.get i)).1 (0, 0)).2.testBit i.val = true)
    (hcl_bfs : ∀ a : Fin cl.length,
      levTwoS3b_bfsMask (levTwoS3e7_permsOf m) 300
        [(cl.getD a.val (0, 0)).1] (1 <<< (cl.getD a.val (0, 0)).1) =
          (cl.getD a.val (0, 0)).2) :
    TCRoot (isFiniteType_cartan Tag.E7) (levTwoS3e7_patSetFin m) := by
  have hrep_mem : ∀ a : Fin cl.length,
      levTwoS3u_repOf (n := Tag.rank Tag.E7) levTwoS3e7_roots cl a ∈ levTwoS3e7_rootVecs :=
    levTwoS3u_rep_mem (fun a => hcl_rep_lt a)
  have hrep_notMem : ∀ a : Fin cl.length,
      levTwoS3u_repOf (n := Tag.rank Tag.E7) levTwoS3e7_roots cl a ∉ levTwoS3e7_patSetFin m :=
    levTwoS3u_notMem_patSet_of_not_bit levTwoS3e7_hnodup levTwoS3e7_hlen
      (fun a => hcl_rep_lt a) hrep_notpat
  have hrep_notMem_imp : ∀ a : Fin cl.length,
      (∃ r ∈ levTwoS3e7_rootVecs, r ∉ levTwoS3e7_patSetFin m ∧
        levTwoS3u_clsOf levTwoS3e7_roots cl hpos r = a) →
      levTwoS3u_repOf (n := Tag.rank Tag.E7) levTwoS3e7_roots cl a ∉ levTwoS3e7_patSetFin m :=
    fun a _ => hrep_notMem a
  exact levTwoS3t_tcRoot_of_tables_of_cover
    (roots := levTwoS3e7_rootVecs) (hRl := levTwoS3e7_hRl)
    (pm := levTwoS3e7_patMask m) (Φ := levTwoS3e7_patSetFin m) (hΦ := fun _ => Iff.rfl)
    (hΦrt := levTwoS3u_isRt_of_mem_patSet levTwoS3e7_hRl (fun _ => Iff.rfl))
    (gens := levTwoS3e7_gensOf m) (negP := levTwoS3e7_negPermList)
    (perms := levTwoS3e7_permsOf m)
    (hperms := by
      simp only [levTwoS3e7_permsOf, levTwoS3e7_gensOf, List.map_map]
      rfl)
    (hgen_mem := levTwoS3e7_gens_mem m hgen)
    (hgen_step := levTwoS3e7_gens_step m)
    (hneg := levTwoS3e7_negStep)
    (hinv := levTwoS3e7_inv m) (hrange := levTwoS3e7_range m)
    (cl := cl) (cls := levTwoS3u_clsOf levTwoS3e7_roots cl hpos)
    (rep := levTwoS3u_repOf (n := Tag.rank Tag.E7) levTwoS3e7_roots cl)
    (hrep_mem := hrep_mem) (hrep_cls := hrep_cls) (hrep_notMem := hrep_notMem_imp)
    (hcls_orbit := hcls_orbit)
    (hcl_bfs := fun a ha => hcl_bfs ⟨a, ha⟩)
    (hcl_rep_lt := fun a ha => hcl_rep_lt ⟨a, ha⟩)
    (hcover := levTwoS3t_cover_refl
      (levTwoS3u_repOf (n := Tag.rank Tag.E7) levTwoS3e7_roots cl) levTwoS3e7_rootVecs
      (levTwoS3e7_patSetFin m) (levTwoS3u_clsOf levTwoS3e7_roots cl hpos)
      hrep_mem hrep_cls hrep_notMem_imp hlen2)

theorem levTwoS3e7_tcRoot_63 :
    TCRoot (isFiniteType_cartan Tag.E7) (levTwoS3e7_patSetFin 63) :=
  levTwoS3e7_tcRoot_of_data 63 (by decide +kernel) levTwoS3e7_classData_63 (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

theorem levTwoS3e7_tcRoot_123 :
    TCRoot (isFiniteType_cartan Tag.E7) (levTwoS3e7_patSetFin 123) :=
  levTwoS3e7_tcRoot_of_data 123 (by decide +kernel) levTwoS3e7_classData_123 (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

theorem levTwoS3e7_tcRoot_126 :
    TCRoot (isFiniteType_cartan Tag.E7) (levTwoS3e7_patSetFin 126) :=
  levTwoS3e7_tcRoot_of_data 126 (by decide +kernel) levTwoS3e7_classData_126 (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

theorem levTwoS3e7_tcRoot_250 :
    TCRoot (isFiniteType_cartan Tag.E7) (levTwoS3e7_patSetFin 250) :=
  levTwoS3e7_tcRoot_of_data 250 (by decide +kernel) levTwoS3e7_classData_250 (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

theorem levTwoS3e7_tcRoot_251 :
    TCRoot (isFiniteType_cartan Tag.E7) (levTwoS3e7_patSetFin 251) :=
  levTwoS3e7_tcRoot_of_data 251 (by decide +kernel) levTwoS3e7_classData_251 (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

theorem levTwoS3e7_tcRoot_252 :
    TCRoot (isFiniteType_cartan Tag.E7) (levTwoS3e7_patSetFin 252) :=
  levTwoS3e7_tcRoot_of_data 252 (by decide +kernel) levTwoS3e7_classData_252 (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

private theorem levTwoS3e7_patMask_all_127 :
    ∀ i : Fin levTwoS3e7_rootVecs.length, (levTwoS3e7_patMask 127).testBit i.val = true := by
  decide +kernel

theorem levTwoS3e7_tcRoot_127 :
    TCRoot (isFiniteType_cartan Tag.E7) (levTwoS3e7_patSetFin 127) := by
  refine levTwoS3t_tcRoot_of_all (roots := levTwoS3e7_rootVecs) (levTwoS3e7_hRl) ?_
  intro β hβ
  obtain ⟨i, rfl⟩ := List.mem_iff_get.mp ((levTwoS3e7_hRl β).mp hβ)
  exact ⟨i, rfl, levTwoS3e7_patMask_all_127 i⟩

private theorem levTwoS3e7_patMask_all_254 :
    ∀ i : Fin levTwoS3e7_rootVecs.length, (levTwoS3e7_patMask 254).testBit i.val = true := by
  decide +kernel

theorem levTwoS3e7_tcRoot_254 :
    TCRoot (isFiniteType_cartan Tag.E7) (levTwoS3e7_patSetFin 254) := by
  refine levTwoS3t_tcRoot_of_all (roots := levTwoS3e7_rootVecs) (levTwoS3e7_hRl) ?_
  intro β hβ
  obtain ⟨i, rfl⟩ := List.mem_iff_get.mp ((levTwoS3e7_hRl β).mp hβ)
  exact ⟨i, rfl, levTwoS3e7_patMask_all_254 i⟩

end CFSG.StandardType.LevTwo
