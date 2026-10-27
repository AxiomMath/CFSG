module

public import CFSG.LocalAnalysis.StandardType.GGLevTwoS3bE8Tc
public import CFSG.LocalAnalysis.StandardType.GGLevTwoS3bTables4
import CFSG.LocalAnalysis.StandardType.GGLevTwoS3aDict
import CFSG.LocalAnalysis.StandardType.GGLevTwoS3bClsK
import CFSG.LocalAnalysis.StandardType.GGLevTwoS3bCovK

public section

namespace CFSG.StandardType.LevTwo

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsL33d
open CFSG.LieType.RootSystem
open scoped Matrix

@[expose] def levTwoS3b_e8_reflPerm (β : Fin (Tag.rank Tag.E8) → ℤ) : List ℕ :=
  levTwoS3b_permOf (List.ofFn β)

theorem levTwoS3b_e8_reflStep_of_list_check
    {g : List ℤ} (hglen : g.length = Tag.rank Tag.E8)
    (hgrt : IsRt (isFiniteType_cartan Tag.E8) (levTwoS3u_vec (Tag.rank Tag.E8) g))
    (hcheck : ∀ i : Fin 240,
      levTwoS3b_roots.getD ((levTwoS3b_permOf g).getD i.val 0) [] =
        levTwoS3b_reflv g (levTwoS3b_roots.getD i.val [])) :
    levTwoS3b_reflectStep (isFiniteType_cartan Tag.E8) levTwoS3b_e8_rootVecs
      (levTwoS3u_vec (Tag.rank Tag.E8) g) (levTwoS3b_permOf g) := by
  refine levTwoS3u_reflectStep_of_list (n := Tag.rank Tag.E8) (roots := levTwoS3b_roots)
    levTwoS3b_e8_hlen (fun β => levTwoS3b_e8_hRl β) (reflv := levTwoS3b_reflv)
    (fun g v hgv hvv hig hiv =>
      levTwoS3b_e8_weylAction_reflv (levTwoS3a_isRt_iff.mp hig) (levTwoS3a_isRt_iff.mp hiv)
        hgv hvv) hglen hgrt
    (fun i hi => hcheck ⟨i, by rwa [levTwoS3b_e8_roots_length240] at hi⟩)

@[expose] def levTwoS3b_e8Ws_501 : List (List (Fin 4) × List (Fin 4)) :=
  [([], []), ([0], [0]), ([1], [1]), ([2], [2]), ([3], [3]), ([0, 1], [0, 1]),
   ([0, 2], [0, 2]), ([0, 3], [0, 3]), ([1, 2], [1, 2]), ([1, 3], [1, 3]), ([2, 3], [2, 3]),
   ([0, 1, 2], [0, 1]), ([0, 1, 3], [0, 1]), ([0, 2, 3], [0, 2]), ([1, 2, 3], [1, 2]),
   ([0, 1, 2, 3], [0, 1])]

@[expose] def levTwoS3b_e8Ws_505 : List (List (Fin 3) × List (Fin 3)) :=
  [([], []), ([0], [0]), ([1], [1]), ([2], [2]), ([0, 1], [0, 1]), ([0, 2], [0, 2]),
   ([1, 2], [1, 2]), ([0, 1, 2], [2])]

@[expose] def levTwoS3b_e8Ws_506 : List (List (Fin 3) × List (Fin 3)) :=
  [([], []), ([0], [0]), ([1], [1]), ([2], [2]), ([0, 1], [0, 1]), ([0, 2], [0, 2]),
   ([1, 2], [1, 2]), ([0, 1, 2], [2])]

private theorem levTwoS3b_e8_hws_501 :
    levTwoS3b_e8Ws_501.all (fun w => decide (w.2.length ≤ 2) &&
      w.2.all (fun a => decide (a ∈ w.1)) &&
      levTwoS3t_coversWith levTwoS3b_e8_reflPerm levTwoS3b_e8ClassData_501
        (levTwoS3u_repOf (n := Tag.rank Tag.E8) levTwoS3b_roots levTwoS3b_e8ClassData_501)
        (levTwoS3b_e8_permsOf 501) [] w.1 w.2) = true :=
  levTwoS3b_e8_hws_of_K 501 levTwoS3b_e8ClassData_501 levTwoS3b_e8_reflPerm (fun _ => rfl)
    (by decide +kernel) levTwoS3b_e8Ws_501 (by decide +kernel)

private theorem levTwoS3b_e8_hws_505 :
    levTwoS3b_e8Ws_505.all (fun w => decide (w.2.length ≤ 2) &&
      w.2.all (fun a => decide (a ∈ w.1)) &&
      levTwoS3t_coversWith levTwoS3b_e8_reflPerm levTwoS3b_e8ClassData_505
        (levTwoS3u_repOf (n := Tag.rank Tag.E8) levTwoS3b_roots levTwoS3b_e8ClassData_505)
        (levTwoS3b_e8_permsOf 505) [] w.1 w.2) = true :=
  levTwoS3b_e8_hws_of_K 505 levTwoS3b_e8ClassData_505 levTwoS3b_e8_reflPerm (fun _ => rfl)
    (by decide +kernel) levTwoS3b_e8Ws_505 (by decide +kernel)

private theorem levTwoS3b_e8_hws_506 :
    levTwoS3b_e8Ws_506.all (fun w => decide (w.2.length ≤ 2) &&
      w.2.all (fun a => decide (a ∈ w.1)) &&
      levTwoS3t_coversWith levTwoS3b_e8_reflPerm levTwoS3b_e8ClassData_506
        (levTwoS3u_repOf (n := Tag.rank Tag.E8) levTwoS3b_roots levTwoS3b_e8ClassData_506)
        (levTwoS3b_e8_permsOf 506) [] w.1 w.2) = true :=
  levTwoS3b_e8_hws_of_K 506 levTwoS3b_e8ClassData_506 levTwoS3b_e8_reflPerm (fun _ => rfl)
    (by decide +kernel) levTwoS3b_e8Ws_506 (by decide +kernel)

private theorem levTwoS3b_e8_hall_501 :
    ∀ T : Finset (Fin 4), ∃ w ∈ levTwoS3b_e8Ws_501, ∀ a : Fin 4, a ∈ w.1 ↔ a ∈ T := by
  decide +kernel

private theorem levTwoS3b_e8_hall_505 :
    ∀ T : Finset (Fin 3), ∃ w ∈ levTwoS3b_e8Ws_505, ∀ a : Fin 3, a ∈ w.1 ↔ a ∈ T := by
  decide +kernel

private theorem levTwoS3b_e8_hall_506 :
    ∀ T : Finset (Fin 3), ∃ w ∈ levTwoS3b_e8Ws_506, ∀ a : Fin 3, a ∈ w.1 ↔ a ∈ T := by
  decide +kernel

private theorem levTwoS3b_e8_bfs_501_0 :
    levTwoS3b_bfsMask (levTwoS3b_e8_permsOf 501) 300
      [((levTwoS3b_e8ClassData_501).getD 0 (0, 0)).1]
      (1 <<< ((levTwoS3b_e8ClassData_501).getD 0 (0, 0)).1) =
      ((levTwoS3b_e8ClassData_501).getD 0 (0, 0)).2 := by
  rw [levTwoS3b_e8_bfsMask_K]
  decide +kernel

private theorem levTwoS3b_e8_bfs_501_1 :
    levTwoS3b_bfsMask (levTwoS3b_e8_permsOf 501) 300
      [((levTwoS3b_e8ClassData_501).getD 1 (0, 0)).1]
      (1 <<< ((levTwoS3b_e8ClassData_501).getD 1 (0, 0)).1) =
      ((levTwoS3b_e8ClassData_501).getD 1 (0, 0)).2 := by
  rw [levTwoS3b_e8_bfsMask_K]
  decide +kernel

private theorem levTwoS3b_e8_bfs_501_2 :
    levTwoS3b_bfsMask (levTwoS3b_e8_permsOf 501) 300
      [((levTwoS3b_e8ClassData_501).getD 2 (0, 0)).1]
      (1 <<< ((levTwoS3b_e8ClassData_501).getD 2 (0, 0)).1) =
      ((levTwoS3b_e8ClassData_501).getD 2 (0, 0)).2 := by
  rw [levTwoS3b_e8_bfsMask_K]
  decide +kernel

private theorem levTwoS3b_e8_bfs_501_3 :
    levTwoS3b_bfsMask (levTwoS3b_e8_permsOf 501) 300
      [((levTwoS3b_e8ClassData_501).getD 3 (0, 0)).1]
      (1 <<< ((levTwoS3b_e8ClassData_501).getD 3 (0, 0)).1) =
      ((levTwoS3b_e8ClassData_501).getD 3 (0, 0)).2 := by
  rw [levTwoS3b_e8_bfsMask_K]
  decide +kernel

private theorem levTwoS3b_e8_bfs_505_0 :
    levTwoS3b_bfsMask (levTwoS3b_e8_permsOf 505) 300
      [((levTwoS3b_e8ClassData_505).getD 0 (0, 0)).1]
      (1 <<< ((levTwoS3b_e8ClassData_505).getD 0 (0, 0)).1) =
      ((levTwoS3b_e8ClassData_505).getD 0 (0, 0)).2 := by
  rw [levTwoS3b_e8_bfsMask_K]
  decide +kernel

private theorem levTwoS3b_e8_bfs_505_1 :
    levTwoS3b_bfsMask (levTwoS3b_e8_permsOf 505) 300
      [((levTwoS3b_e8ClassData_505).getD 1 (0, 0)).1]
      (1 <<< ((levTwoS3b_e8ClassData_505).getD 1 (0, 0)).1) =
      ((levTwoS3b_e8ClassData_505).getD 1 (0, 0)).2 := by
  rw [levTwoS3b_e8_bfsMask_K]
  decide +kernel

private theorem levTwoS3b_e8_bfs_505_2 :
    levTwoS3b_bfsMask (levTwoS3b_e8_permsOf 505) 300
      [((levTwoS3b_e8ClassData_505).getD 2 (0, 0)).1]
      (1 <<< ((levTwoS3b_e8ClassData_505).getD 2 (0, 0)).1) =
      ((levTwoS3b_e8ClassData_505).getD 2 (0, 0)).2 := by
  rw [levTwoS3b_e8_bfsMask_K]
  decide +kernel

private theorem levTwoS3b_e8_bfs_506_0 :
    levTwoS3b_bfsMask (levTwoS3b_e8_permsOf 506) 300
      [((levTwoS3b_e8ClassData_506).getD 0 (0, 0)).1]
      (1 <<< ((levTwoS3b_e8ClassData_506).getD 0 (0, 0)).1) =
      ((levTwoS3b_e8ClassData_506).getD 0 (0, 0)).2 := by
  rw [levTwoS3b_e8_bfsMask_K]
  decide +kernel

private theorem levTwoS3b_e8_bfs_506_1 :
    levTwoS3b_bfsMask (levTwoS3b_e8_permsOf 506) 300
      [((levTwoS3b_e8ClassData_506).getD 1 (0, 0)).1]
      (1 <<< ((levTwoS3b_e8ClassData_506).getD 1 (0, 0)).1) =
      ((levTwoS3b_e8ClassData_506).getD 1 (0, 0)).2 := by
  rw [levTwoS3b_e8_bfsMask_K]
  decide +kernel

private theorem levTwoS3b_e8_bfs_506_2 :
    levTwoS3b_bfsMask (levTwoS3b_e8_permsOf 506) 300
      [((levTwoS3b_e8ClassData_506).getD 2 (0, 0)).1]
      (1 <<< ((levTwoS3b_e8ClassData_506).getD 2 (0, 0)).1) =
      ((levTwoS3b_e8ClassData_506).getD 2 (0, 0)).2 := by
  rw [levTwoS3b_e8_bfsMask_K]
  decide +kernel

private theorem levTwoS3b_e8_bfs_501 :
    ∀ a : Fin (levTwoS3b_e8ClassData_501).length,
      levTwoS3b_bfsMask (levTwoS3b_e8_permsOf 501) 300
        [((levTwoS3b_e8ClassData_501).getD a.val (0, 0)).1]
        (1 <<< ((levTwoS3b_e8ClassData_501).getD a.val (0, 0)).1) =
        ((levTwoS3b_e8ClassData_501).getD a.val (0, 0)).2 := by
  intro a
  fin_cases a
  · exact levTwoS3b_e8_bfs_501_0
  · exact levTwoS3b_e8_bfs_501_1
  · exact levTwoS3b_e8_bfs_501_2
  · exact levTwoS3b_e8_bfs_501_3

private theorem levTwoS3b_e8_bfs_505 :
    ∀ a : Fin (levTwoS3b_e8ClassData_505).length,
      levTwoS3b_bfsMask (levTwoS3b_e8_permsOf 505) 300
        [((levTwoS3b_e8ClassData_505).getD a.val (0, 0)).1]
        (1 <<< ((levTwoS3b_e8ClassData_505).getD a.val (0, 0)).1) =
        ((levTwoS3b_e8ClassData_505).getD a.val (0, 0)).2 := by
  intro a
  fin_cases a
  · exact levTwoS3b_e8_bfs_505_0
  · exact levTwoS3b_e8_bfs_505_1
  · exact levTwoS3b_e8_bfs_505_2

private theorem levTwoS3b_e8_bfs_506 :
    ∀ a : Fin (levTwoS3b_e8ClassData_506).length,
      levTwoS3b_bfsMask (levTwoS3b_e8_permsOf 506) 300
        [((levTwoS3b_e8ClassData_506).getD a.val (0, 0)).1]
        (1 <<< ((levTwoS3b_e8ClassData_506).getD a.val (0, 0)).1) =
        ((levTwoS3b_e8ClassData_506).getD a.val (0, 0)).2 := by
  intro a
  fin_cases a
  · exact levTwoS3b_e8_bfs_506_0
  · exact levTwoS3b_e8_bfs_506_1
  · exact levTwoS3b_e8_bfs_506_2

private theorem levTwoS3b_e8_cls_orbit_501 :
    ∀ i : Fin levTwoS3b_e8_rootVecs.length,
      ¬ (levTwoS3b_patMask 501).testBit i.val →
      ((levTwoS3b_e8ClassData_501).getD (levTwoS3u_clsOf levTwoS3b_roots
        levTwoS3b_e8ClassData_501 (by decide +kernel)
        (levTwoS3b_e8_rootVecs.get i)).1 (0, 0)).2.testBit i.val = true :=
  levTwoS3u_clsOrbit_of levTwoS3b_e8_hnodup levTwoS3b_e8_hlen _ _ _ (by decide +kernel)

private theorem levTwoS3b_e8_cls_orbit_505 :
    ∀ i : Fin levTwoS3b_e8_rootVecs.length,
      ¬ (levTwoS3b_patMask 505).testBit i.val →
      ((levTwoS3b_e8ClassData_505).getD (levTwoS3u_clsOf levTwoS3b_roots
        levTwoS3b_e8ClassData_505 (by decide +kernel)
        (levTwoS3b_e8_rootVecs.get i)).1 (0, 0)).2.testBit i.val = true :=
  levTwoS3u_clsOrbit_of levTwoS3b_e8_hnodup levTwoS3b_e8_hlen _ _ _ (by decide +kernel)

private theorem levTwoS3b_e8_cls_orbit_506 :
    ∀ i : Fin levTwoS3b_e8_rootVecs.length,
      ¬ (levTwoS3b_patMask 506).testBit i.val →
      ((levTwoS3b_e8ClassData_506).getD (levTwoS3u_clsOf levTwoS3b_roots
        levTwoS3b_e8ClassData_506 (by decide +kernel)
        (levTwoS3b_e8_rootVecs.get i)).1 (0, 0)).2.testBit i.val = true :=
  levTwoS3u_clsOrbit_of levTwoS3b_e8_hnodup levTwoS3b_e8_hlen _ _ _ (by decide +kernel)

theorem levTwoS3b_e8_tcRoot_of_data_ws
    (m : ℕ)
    (hgen : (List.range 9).all (fun x =>
      !(m.testBit x) || levTwoS3b_inPat m (levTwoS3b_genVec x)) = true)
    (cl : List (ℕ × ℕ)) (hpos : 0 < cl.length)
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
          (cl.getD a.val (0, 0)).2)
    (hrefl : ∀ a : Fin cl.length,
      levTwoS3b_reflectStep (isFiniteType_cartan Tag.E8) levTwoS3b_e8_rootVecs
        (levTwoS3u_repOf (n := Tag.rank Tag.E8) levTwoS3b_roots cl a)
        (levTwoS3b_e8_reflPerm (levTwoS3u_repOf (n := Tag.rank Tag.E8) levTwoS3b_roots cl a)))
    (ws : List (List (Fin cl.length) × List (Fin cl.length)))
    (hws : ws.all (fun w => decide (w.2.length ≤ 2) && w.2.all (fun a => decide (a ∈ w.1)) &&
      levTwoS3t_coversWith levTwoS3b_e8_reflPerm cl
        (levTwoS3u_repOf (n := Tag.rank Tag.E8) levTwoS3b_roots cl)
        (levTwoS3b_e8_permsOf m) [] w.1 w.2) = true)
    (hall : ∀ T : Finset (Fin cl.length), ∃ w ∈ ws, ∀ a, a ∈ w.1 ↔ a ∈ T) :
    TCRoot (isFiniteType_cartan Tag.E8) (levTwoS3b_e8_patSetMask m) := by
  have hrep_mem : ∀ a : Fin cl.length,
      levTwoS3u_repOf (n := Tag.rank Tag.E8) levTwoS3b_roots cl a ∈ levTwoS3b_e8_rootVecs :=
    levTwoS3u_rep_mem (fun a => hcl_rep_lt a)
  have hrep_notMemF : ∀ a : Fin cl.length,
      levTwoS3u_repOf (n := Tag.rank Tag.E8) levTwoS3b_roots cl a ∉ levTwoS3b_e8_patSetMask m :=
    levTwoS3u_notMem_patSet_of_not_bit levTwoS3b_e8_hnodup levTwoS3b_e8_hlen hcl_rep_lt hrep_notpat
  have hrep_notMem_imp : ∀ a : Fin cl.length,
      (∃ r ∈ levTwoS3b_e8_rootVecs, r ∉ levTwoS3b_e8_patSetMask m ∧
        levTwoS3u_clsOf levTwoS3b_roots cl hpos r = a) →
      levTwoS3u_repOf (n := Tag.rank Tag.E8) levTwoS3b_roots cl a ∉ levTwoS3b_e8_patSetMask m :=
    fun a _ => hrep_notMemF a
  have hrep_eq : ∀ a : Fin cl.length,
      levTwoS3u_repOf (n := Tag.rank Tag.E8) levTwoS3b_roots cl a
        = levTwoS3b_e8_rootVecs.getD (cl.getD a.val (0, 0)).1 0 :=
    fun a => (levTwoS3u_getD_map (Tag.rank Tag.E8) levTwoS3b_roots _).symm
  have hcoverW := levTwoS3v_hcoverW_of_table (cl := cl)
    (rep := levTwoS3u_repOf (n := Tag.rank Tag.E8) levTwoS3b_roots cl)
    levTwoS3b_e8_reflPerm (levTwoS3b_e8_permsOf m) [] ws hws hall
  have hΦrt : ∀ β ∈ levTwoS3b_e8_patSetMask m, IsRt (isFiniteType_cartan Tag.E8) β :=
    levTwoS3u_isRt_of_mem_patSet levTwoS3b_e8_hRl (fun _ => Iff.rfl)
  exact levTwoS3v_tcRoot_of_tables_ws
    (roots := levTwoS3b_e8_rootVecs) (hRl := levTwoS3b_e8_hRl)
    (pm := levTwoS3b_patMask m) (Φ := levTwoS3b_e8_patSetMask m)
    (hΦ := fun _ => Iff.rfl) (hΦrt := hΦrt)
    (gens := levTwoS3b_e8_gensOf m) (negP := levTwoS3b_e8NegPerm)
    (perms := levTwoS3b_e8_permsOf m)
    (hperms := by
      simp only [levTwoS3b_e8_permsOf, levTwoS3b_e8_gensOf, List.map_map]
      rfl)
    (reflPerm := levTwoS3b_e8_reflPerm)
    (hgen_mem := levTwoS3b_e8_gens_mem m hgen)
    (hgen_step := levTwoS3b_e8_gens_step m)
    (hneg := levTwoS3b_e8_negStep)
    (hinv := levTwoS3b_e8_inv m) (hrange := levTwoS3b_e8_range m)
    (cl := cl) (cls := levTwoS3u_clsOf levTwoS3b_roots cl hpos)
    (rep := levTwoS3u_repOf (n := Tag.rank Tag.E8) levTwoS3b_roots cl)
    (hrep_mem := hrep_mem) (hrep_cls := hrep_cls) (hrep_notMem := hrep_notMem_imp)
    (hrep_eq := hrep_eq) (hrefl := hrefl)
    (hcls_orbit := hcls_orbit)
    (hcl_bfs := fun a ha => hcl_bfs ⟨a, ha⟩)
    (hcl_rep_lt := fun a ha => hcl_rep_lt ⟨a, ha⟩)
    (seed := []) (hseed := by intro i hi; simp at hi)
    (hcoverW := hcoverW)

theorem levTwoS3b_e8_tcRoot_501 :
    TCRoot (isFiniteType_cartan Tag.E8) (levTwoS3b_e8_patSet 501) := by
  rw [levTwoS3b_e8_patSet_eq]
  have hcl_rep_lt : ∀ a : Fin (levTwoS3b_e8ClassData_501).length,
      (levTwoS3b_e8ClassData_501.getD a.val (0, 0)).1 < levTwoS3b_e8_rootVecs.length := by
    decide +kernel
  refine levTwoS3b_e8_tcRoot_of_data_ws 501 (by decide +kernel) levTwoS3b_e8ClassData_501
    (by decide +kernel) hcl_rep_lt (by decide +kernel) (by decide +kernel)
    levTwoS3b_e8_cls_orbit_501 levTwoS3b_e8_bfs_501 ?_ levTwoS3b_e8Ws_501
    levTwoS3b_e8_hws_501 levTwoS3b_e8_hall_501
  intro a
  have hidx240 : (levTwoS3b_e8ClassData_501.getD a.val (0, 0)).1 < 240 := by
    simpa [levTwoS3b_e8_rootVecs, levTwoS3b_e8_roots_length240] using hcl_rep_lt a
  have hp : levTwoS3b_e8_reflPerm (levTwoS3u_repOf (n := Tag.rank Tag.E8)
      levTwoS3b_roots levTwoS3b_e8ClassData_501 a) =
      levTwoS3b_permOf (levTwoS3b_roots.getD
        ((levTwoS3b_e8ClassData_501.getD a.val (0, 0)).1) []) := by
    simp only [levTwoS3b_e8_reflPerm, levTwoS3u_repOf]
    rw [levTwoS3u_ofFn_vec (Tag.rank Tag.E8) (levTwoS3b_e8_roots_length hidx240)]
  rw [hp]
  refine levTwoS3b_e8_reflStep_of_list_check (g := levTwoS3b_roots.getD
      ((levTwoS3b_e8ClassData_501.getD a.val (0, 0)).1) [])
    (levTwoS3b_e8_roots_length hidx240)
    ((levTwoS3b_e8_hRl _).mpr (levTwoS3u_rep_mem (fun a => hcl_rep_lt a) a)) ?_
  exact levTwoS3b_e8_permOf_step (levTwoS3b_e8_roots_length hidx240)
    ((levTwoS3b_e8_hRl _).mpr (levTwoS3u_rep_mem (fun a => hcl_rep_lt a) a))

theorem levTwoS3b_e8_tcRoot_505 :
    TCRoot (isFiniteType_cartan Tag.E8) (levTwoS3b_e8_patSet 505) := by
  rw [levTwoS3b_e8_patSet_eq]
  have hcl_rep_lt : ∀ a : Fin (levTwoS3b_e8ClassData_505).length,
      (levTwoS3b_e8ClassData_505.getD a.val (0, 0)).1 < levTwoS3b_e8_rootVecs.length := by
    decide +kernel
  refine levTwoS3b_e8_tcRoot_of_data_ws 505 (by decide +kernel) levTwoS3b_e8ClassData_505
    (by decide +kernel) hcl_rep_lt (by decide +kernel) (by decide +kernel)
    levTwoS3b_e8_cls_orbit_505 levTwoS3b_e8_bfs_505 ?_ levTwoS3b_e8Ws_505
    levTwoS3b_e8_hws_505 levTwoS3b_e8_hall_505
  intro a
  have hidx240 : (levTwoS3b_e8ClassData_505.getD a.val (0, 0)).1 < 240 := by
    simpa [levTwoS3b_e8_rootVecs, levTwoS3b_e8_roots_length240] using hcl_rep_lt a
  have hp : levTwoS3b_e8_reflPerm (levTwoS3u_repOf (n := Tag.rank Tag.E8)
      levTwoS3b_roots levTwoS3b_e8ClassData_505 a) =
      levTwoS3b_permOf (levTwoS3b_roots.getD
        ((levTwoS3b_e8ClassData_505.getD a.val (0, 0)).1) []) := by
    simp only [levTwoS3b_e8_reflPerm, levTwoS3u_repOf]
    rw [levTwoS3u_ofFn_vec (Tag.rank Tag.E8) (levTwoS3b_e8_roots_length hidx240)]
  rw [hp]
  refine levTwoS3b_e8_reflStep_of_list_check (g := levTwoS3b_roots.getD
      ((levTwoS3b_e8ClassData_505.getD a.val (0, 0)).1) [])
    (levTwoS3b_e8_roots_length hidx240)
    ((levTwoS3b_e8_hRl _).mpr (levTwoS3u_rep_mem (fun a => hcl_rep_lt a) a)) ?_
  exact levTwoS3b_e8_permOf_step (levTwoS3b_e8_roots_length hidx240)
    ((levTwoS3b_e8_hRl _).mpr (levTwoS3u_rep_mem (fun a => hcl_rep_lt a) a))

theorem levTwoS3b_e8_tcRoot_506 :
    TCRoot (isFiniteType_cartan Tag.E8) (levTwoS3b_e8_patSet 506) := by
  rw [levTwoS3b_e8_patSet_eq]
  have hcl_rep_lt : ∀ a : Fin (levTwoS3b_e8ClassData_506).length,
      (levTwoS3b_e8ClassData_506.getD a.val (0, 0)).1 < levTwoS3b_e8_rootVecs.length := by
    decide +kernel
  refine levTwoS3b_e8_tcRoot_of_data_ws 506 (by decide +kernel) levTwoS3b_e8ClassData_506
    (by decide +kernel) hcl_rep_lt (by decide +kernel) (by decide +kernel)
    levTwoS3b_e8_cls_orbit_506 levTwoS3b_e8_bfs_506 ?_ levTwoS3b_e8Ws_506
    levTwoS3b_e8_hws_506 levTwoS3b_e8_hall_506
  intro a
  have hidx240 : (levTwoS3b_e8ClassData_506.getD a.val (0, 0)).1 < 240 := by
    simpa [levTwoS3b_e8_rootVecs, levTwoS3b_e8_roots_length240] using hcl_rep_lt a
  have hp : levTwoS3b_e8_reflPerm (levTwoS3u_repOf (n := Tag.rank Tag.E8)
      levTwoS3b_roots levTwoS3b_e8ClassData_506 a) =
      levTwoS3b_permOf (levTwoS3b_roots.getD
        ((levTwoS3b_e8ClassData_506.getD a.val (0, 0)).1) []) := by
    simp only [levTwoS3b_e8_reflPerm, levTwoS3u_repOf]
    rw [levTwoS3u_ofFn_vec (Tag.rank Tag.E8) (levTwoS3b_e8_roots_length hidx240)]
  rw [hp]
  refine levTwoS3b_e8_reflStep_of_list_check (g := levTwoS3b_roots.getD
      ((levTwoS3b_e8ClassData_506.getD a.val (0, 0)).1) [])
    (levTwoS3b_e8_roots_length hidx240)
    ((levTwoS3b_e8_hRl _).mpr (levTwoS3u_rep_mem (fun a => hcl_rep_lt a) a)) ?_
  exact levTwoS3b_e8_permOf_step (levTwoS3b_e8_roots_length hidx240)
    ((levTwoS3b_e8_hRl _).mpr (levTwoS3u_rep_mem (fun a => hcl_rep_lt a) a))

end CFSG.StandardType.LevTwo
