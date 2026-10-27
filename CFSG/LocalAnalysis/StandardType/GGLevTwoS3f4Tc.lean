module

public import CFSG.LocalAnalysis.StandardType.GGLevTwoS3f4Link
public import CFSG.LocalAnalysis.StandardType.GGLevTwoS3bTables3
public import CFSG.LocalAnalysis.StandardType.GGLevTwoS3bTables4
import CFSG.LocalAnalysis.StandardType.GGLevTwoS3aDict

public section

namespace CFSG.StandardType.LevTwo

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsL33d
open CFSG.LieType.RootSystem
open scoped Matrix

@[expose] def levTwoS3f4_rootVecs : List (Fin (Tag.rank Tag.F4) → ℤ) :=
  levTwoS3f4_roots.map (levTwoS3u_vec (Tag.rank Tag.F4))

theorem levTwoS3f4_rootVecs_len : levTwoS3f4_rootVecs.length = 48 := by
  rw [levTwoS3f4_rootVecs, List.length_map, levTwoS3f4_roots, Tag.length_artifactRoots]
  decide +kernel

theorem levTwoS3f4_roots_len : levTwoS3f4_roots.length = 48 := by
  rw [levTwoS3f4_roots, Tag.length_artifactRoots]
  decide +kernel

theorem levTwoS3f4_hlen : ∀ l ∈ levTwoS3f4_roots, l.length = Tag.rank Tag.F4 := by
  intro l hl
  exact length_of_mem_artifactRoots hl

theorem levTwoS3f4_hnodup : levTwoS3f4_roots.Nodup := by
  simpa only [levTwoS3f4_roots] using nodup_artifactRoots (τ := Tag.F4)

theorem levTwoS3f4_hRl :
    ∀ β : Fin (Tag.rank Tag.F4) → ℤ,
      IsRt (isFiniteType_cartan Tag.F4) β ↔ β ∈ levTwoS3f4_rootVecs := by
  have hRl0 : ∀ β : Fin (Tag.rank Tag.F4) → ℤ,
      IsRt (isFiniteType_cartan Tag.F4) β ↔ List.ofFn β ∈ levTwoS3f4_roots := by
    intro β
    rw [levTwoS3a_isRt_iff]
    change IsRoot Tag.F4 β ↔ List.ofFn β ∈ Tag.artifactRoots Tag.F4
    exact isRoot_iff_mem_artifactRoots
  exact levTwoS3u_isRt_iff_mem_ofFn levTwoS3f4_hlen hRl0

theorem levTwoS3f4_rootVecs_getElem (i : Fin levTwoS3f4_rootVecs.length) :
    levTwoS3f4_rootVecs.get i =
      levTwoS3f4_vec (Tag.rank Tag.F4) (levTwoS3f4_roots.getD i.val []) := by
  have h1 : levTwoS3f4_rootVecs.get i = levTwoS3f4_rootVecs.getD i.val 0 := by
    rw [List.get_eq_getElem, List.getD_eq_getElem]
  rw [h1]
  show (levTwoS3f4_roots.map (levTwoS3u_vec (Tag.rank Tag.F4))).getD i.val 0 =
    levTwoS3f4_vec (Tag.rank Tag.F4) (levTwoS3f4_roots.getD i.val [])
  exact levTwoS3u_getD_map (Tag.rank Tag.F4) levTwoS3f4_roots i.val

theorem levTwoS3f4_rootVecs_getElem_vec (i : Fin levTwoS3f4_rootVecs.length) :
    levTwoS3f4_rootVecs.get i =
      levTwoS3u_vec (Tag.rank Tag.F4) (levTwoS3f4_roots.getD i.val []) := by
  have h1 : levTwoS3f4_rootVecs.get i = levTwoS3f4_rootVecs.getD i.val 0 := by
    rw [List.get_eq_getElem, List.getD_eq_getElem]
  rw [h1]
  show (levTwoS3f4_roots.map (levTwoS3u_vec (Tag.rank Tag.F4))).getD i.val 0 =
    levTwoS3u_vec (Tag.rank Tag.F4) (levTwoS3f4_roots.getD i.val [])
  exact levTwoS3u_getD_map (Tag.rank Tag.F4) levTwoS3f4_roots i.val

@[expose] def levTwoS3f4_patSetF (m l : ℕ) : Set (Fin (Tag.rank Tag.F4) → ℤ) :=
  {β | ∃ i : Fin levTwoS3f4_rootVecs.length,
    levTwoS3f4_rootVecs.get i = β ∧ (levTwoS3f4_patMask m l).testBit i.val}

theorem levTwoS3f4_patSetF_eq (m l : ℕ) :
    levTwoS3f4_patSetF m l = ↑(levTwoS3f4_patSet m l) := by
  ext β
  constructor
  · rintro ⟨i, hβ, hbit⟩
    rw [Finset.mem_coe, levTwoS3f4_patSet, List.mem_toFinset, List.mem_map]
    refine ⟨i.val, ?_, ?_⟩
    · rw [List.mem_filter, List.mem_range]
      exact ⟨by rw [← levTwoS3f4_rootVecs_len]; exact i.isLt, hbit⟩
    · rw [levTwoS3f4_rootVecs_getElem i] at hβ
      exact hβ
  · intro h
    change β ∈ (levTwoS3f4_patSet m l : Set (Fin (Tag.rank Tag.F4) → ℤ)) at h
    rw [Finset.mem_coe, levTwoS3f4_patSet, List.mem_toFinset, List.mem_map] at h
    obtain ⟨j, hj, hβ⟩ := h
    rw [List.mem_filter, List.mem_range] at hj
    refine ⟨⟨j, by rw [levTwoS3f4_rootVecs_len]; exact hj.1⟩, ?_, hj.2⟩
    rw [levTwoS3f4_rootVecs_getElem]
    exact hβ

@[expose] def levTwoS3f4_gensOf (m l : ℕ) : List ((Fin (Tag.rank Tag.F4) → ℤ) × List ℕ) :=
  ((List.range 48).filter (fun i => (levTwoS3f4_patMask m l).testBit i)).map
    (fun i => (levTwoS3u_vec (Tag.rank Tag.F4) (levTwoS3f4_roots.getD i []),
      levTwoS3f4_permOf (levTwoS3f4_roots.getD i [])))

@[expose] def levTwoS3f4_reflPerm (β : Fin (Tag.rank Tag.F4) → ℤ) : List ℕ :=
  levTwoS3f4_reflPerms.getD (levTwoS3u_idx levTwoS3f4_roots β) []

@[expose] def levTwoS3f4_seed (m l : ℕ) : List ℕ :=
  (List.range 48).filter (fun i => (levTwoS3f4_patMask m l).testBit i)

theorem levTwoS3f4_reflPerms_len : levTwoS3f4_reflPerms.length = 48 := by
  rw [levTwoS3f4_reflPerms_eq, List.length_map, List.length_range]

theorem levTwoS3f4_reflPerms_getD {i : ℕ} (hi : i < 48) :
    levTwoS3f4_reflPerms.getD i [] = levTwoS3f4_permOf (levTwoS3f4_roots.getD i []) := by
  rw [levTwoS3f4_reflPerms_eq,
    List.getD_eq_getElem _ _ (by rw [List.length_map, List.length_range]; exact hi),
    List.getElem_map, List.getElem_range]

theorem levTwoS3f4_gens_mem (m l : ℕ) :
    ∀ gp ∈ levTwoS3f4_gensOf m l, gp.1 ∈ levTwoS3f4_patSetF m l := by
  intro gp hgp
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hgp
  rw [List.mem_filter] at hx
  have hx48 : x < 48 := List.mem_range.mp hx.1
  refine ⟨⟨x, by rw [levTwoS3f4_rootVecs_len]; exact hx48⟩, ?_, hx.2⟩
  rw [levTwoS3f4_rootVecs_getElem_vec]

theorem levTwoS3f4_gens_mem_patSet (m l : ℕ) :
    ∀ gp ∈ levTwoS3f4_gensOf m l, gp.1 ∈ ↑(levTwoS3f4_patSet m l) := by
  intro gp hgp
  change gp.1 ∈ (levTwoS3f4_patSet m l : Set (Fin (Tag.rank Tag.F4) → ℤ))
  rw [← levTwoS3f4_patSetF_eq]
  exact levTwoS3f4_gens_mem m l gp hgp

theorem levTwoS3f4_gens_step
    (m l : ℕ) :
    ∀ gp ∈ levTwoS3f4_gensOf m l,
      levTwoS3b_reflectStep (isFiniteType_cartan Tag.F4) levTwoS3f4_rootVecs gp.1 gp.2 := by
  intro gp hgp
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hgp
  rw [List.mem_filter] at hx
  have hx48 : x < 48 := List.mem_range.mp hx.1
  have hgget : levTwoS3f4_roots.getD x [] ∈ levTwoS3f4_roots := by
    rw [List.getD_eq_getElem _ _ (by rw [levTwoS3f4_roots_len]; exact hx48)]
    exact List.getElem_mem _
  have hglen : (levTwoS3f4_roots.getD x []).length = Tag.rank Tag.F4 :=
    levTwoS3f4_hlen _ hgget
  have hgrt : IsRt (isFiniteType_cartan Tag.F4)
      (levTwoS3u_vec (Tag.rank Tag.F4) (levTwoS3f4_roots.getD x [])) :=
    (levTwoS3f4_hRl _).mpr (List.mem_map.mpr ⟨_, hgget, rfl⟩)
  refine levTwoS3u_reflectStep_of_list (n := Tag.rank Tag.F4) (roots := levTwoS3f4_roots)
    levTwoS3f4_hlen (fun β => levTwoS3f4_hRl β) (reflv := levTwoS3f4_reflv)
    (fun g v hgv hvv hig hiv =>
      levTwoS3f4_weylAction_reflv (levTwoS3a_isRt_iff.mp hig) (levTwoS3a_isRt_iff.mp hiv)
        hgv hvv) hglen hgrt ?_
  intro i hi
  rw [← levTwoS3f4_reflPerms_getD hx48]
  exact levTwoS3f4_reflPerm_valid ⟨x, hx48⟩ ⟨i, by rwa [levTwoS3f4_roots_len] at hi⟩

theorem levTwoS3f4_negStep :
    levTwoS3b_negStep levTwoS3f4_rootVecs levTwoS3f4_negPermLit :=
  levTwoS3u_negStep_of_list (n := Tag.rank Tag.F4) (roots := levTwoS3f4_roots)
    (fun i hi => levTwoS3f4_negPermLit_valid
      ⟨i, by rwa [levTwoS3f4_roots_len] at hi⟩)

theorem levTwoS3f4_perms_sub (m l : ℕ) :
    ∀ p ∈ levTwoS3f4_patPerms m l, p ∈ levTwoS3f4_negPermLit :: levTwoS3f4_reflPerms := by
  intro p hp
  rw [levTwoS3f4_patPerms] at hp
  rcases List.mem_cons.mp hp with rfl | hp
  · rw [levTwoS3f4_negPermLit_eq]
    exact List.mem_cons_self ..
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hp
    rw [List.mem_filter] at hx
    have hx48 : x < 48 := List.mem_range.mp hx.1
    rw [← levTwoS3f4_reflPerms_getD hx48]
    have hx' : x < levTwoS3f4_reflPerms.length := by
      rw [levTwoS3f4_reflPerms_len]; exact hx48
    rw [List.getD_eq_get _ _ ⟨x, hx'⟩]
    exact List.mem_cons_of_mem _ (List.get_mem _ _)

theorem levTwoS3f4_base_inv :
    (levTwoS3f4_negPermLit :: levTwoS3f4_reflPerms).all (fun p =>
      (List.range levTwoS3f4_rootVecs.length).all
        (fun i => p.getD (p.getD i 0) 0 == i)) = true := by
  rw [levTwoS3f4_rootVecs_len]
  decide +kernel

theorem levTwoS3f4_base_range :
    (levTwoS3f4_negPermLit :: levTwoS3f4_reflPerms).all (fun p =>
      (List.range levTwoS3f4_rootVecs.length).all
        (fun i => decide (p.getD i 0 < levTwoS3f4_rootVecs.length))) = true := by
  rw [levTwoS3f4_rootVecs_len]
  decide +kernel

theorem levTwoS3f4_inv (m l : ℕ) :
    ∀ p ∈ levTwoS3f4_patPerms m l, ∀ i, i < levTwoS3f4_rootVecs.length →
      p.getD (p.getD i 0) 0 = i :=
  levTwoS3u_inv_of_all levTwoS3f4_base_inv (levTwoS3f4_perms_sub m l)

theorem levTwoS3f4_range (m l : ℕ) :
    ∀ p ∈ levTwoS3f4_patPerms m l, ∀ i, i < levTwoS3f4_rootVecs.length →
      p.getD i 0 < levTwoS3f4_rootVecs.length :=
  levTwoS3u_range_of_all levTwoS3f4_base_range (levTwoS3f4_perms_sub m l)

theorem levTwoS3f4_reflStep_of_list_check
    {g : List ℤ} (hglen : g.length = Tag.rank Tag.F4)
    (hgrt : IsRt (isFiniteType_cartan Tag.F4) (levTwoS3u_vec (Tag.rank Tag.F4) g))
    (hcheck : ∀ i : Fin 48,
      levTwoS3f4_roots.getD ((levTwoS3f4_permOf g).getD i.val 0) [] =
        levTwoS3f4_reflv g (levTwoS3f4_roots.getD i.val [])) :
    levTwoS3b_reflectStep (isFiniteType_cartan Tag.F4) levTwoS3f4_rootVecs
      (levTwoS3u_vec (Tag.rank Tag.F4) g) (levTwoS3f4_permOf g) := by
  refine levTwoS3u_reflectStep_of_list (n := Tag.rank Tag.F4) (roots := levTwoS3f4_roots)
    levTwoS3f4_hlen (fun β => levTwoS3f4_hRl β) (reflv := levTwoS3f4_reflv)
    (fun g v hgv hvv hig hiv =>
      levTwoS3f4_weylAction_reflv (levTwoS3a_isRt_iff.mp hig) (levTwoS3a_isRt_iff.mp hiv)
        hgv hvv) hglen hgrt
    (fun i hi => hcheck ⟨i, by rwa [levTwoS3f4_roots_len] at hi⟩)

theorem levTwoS3f4_idx_repOf {cl : List (ℕ × ℕ)} (a : Fin cl.length)
    (hrlt : (cl.getD a.val (0, 0)).1 < levTwoS3f4_roots.length) :
    levTwoS3u_idx levTwoS3f4_roots
      (levTwoS3u_repOf (n := Tag.rank Tag.F4) levTwoS3f4_roots cl a) =
        (cl.getD a.val (0, 0)).1 := by
  simp only [levTwoS3u_repOf]
  rw [List.getD_eq_get _ _ ⟨_, hrlt⟩]
  exact levTwoS3u_idx_vec_get levTwoS3f4_hnodup levTwoS3f4_hlen ⟨_, hrlt⟩

theorem levTwoS3f4_reflPerm_repOf {cl : List (ℕ × ℕ)} (a : Fin cl.length)
    (hrlt : (cl.getD a.val (0, 0)).1 < levTwoS3f4_roots.length) :
    levTwoS3f4_reflPerm
      (levTwoS3u_repOf (n := Tag.rank Tag.F4) levTwoS3f4_roots cl a) =
        levTwoS3f4_permOf (levTwoS3f4_roots.getD (cl.getD a.val (0, 0)).1 []) := by
  rw [levTwoS3f4_reflPerm, levTwoS3f4_idx_repOf a hrlt,
    levTwoS3f4_reflPerms_getD (by
      have h48 : levTwoS3f4_roots.length = 48 := levTwoS3f4_roots_len
      rwa [h48] at hrlt)]

theorem levTwoS3f4_mem_patSet_vec_iff (m l : ℕ) (β : Fin (Tag.rank Tag.F4) → ℤ) :
    β ∈ (levTwoS3f4_patSet m l : Set (Fin (Tag.rank Tag.F4) → ℤ)) ↔
      ∃ i : Fin levTwoS3f4_rootVecs.length,
        levTwoS3f4_rootVecs.get i = β ∧ (levTwoS3f4_patMask m l).testBit i.val := by
  rw [← levTwoS3f4_patSetF_eq]
  rfl

theorem levTwoS3f4_tcRoot_of_data_ws
    (m l : ℕ)
    (cl : List (ℕ × ℕ)) (hpos : 0 < cl.length)
    (hcl_rep_lt : ∀ a : Fin cl.length,
      (cl.getD a.val (0, 0)).1 < levTwoS3f4_rootVecs.length)
    (hrep_notpat : ∀ a : Fin cl.length,
      ¬ (levTwoS3f4_patMask m l).testBit (cl.getD a.val (0, 0)).1)
    (hrep_cls : ∀ a : Fin cl.length,
      levTwoS3u_clsOf levTwoS3f4_roots cl hpos
        (levTwoS3u_repOf (n := Tag.rank Tag.F4) levTwoS3f4_roots cl a) = a)
    (hcls_orbit : ∀ i : Fin levTwoS3f4_rootVecs.length,
      ¬ (levTwoS3f4_patMask m l).testBit i.val →
      (cl.getD (levTwoS3u_clsOf levTwoS3f4_roots cl hpos
        (levTwoS3f4_rootVecs.get i)).1 (0, 0)).2.testBit i.val = true)
    (hcl_bfs : ∀ a : Fin cl.length,
      levTwoS3b_bfsMask (levTwoS3f4_patPerms m l) 300
        [(cl.getD a.val (0, 0)).1] (1 <<< (cl.getD a.val (0, 0)).1) =
          (cl.getD a.val (0, 0)).2)
    (hrefl : ∀ a : Fin cl.length,
      levTwoS3b_reflectStep (isFiniteType_cartan Tag.F4) levTwoS3f4_rootVecs
        (levTwoS3u_repOf (n := Tag.rank Tag.F4) levTwoS3f4_roots cl a)
        (levTwoS3f4_reflPerm (levTwoS3u_repOf (n := Tag.rank Tag.F4) levTwoS3f4_roots cl a)))
    (ws : List (List (Fin cl.length) × List (Fin cl.length)))
    (hws : ws.all (fun w => decide (w.2.length ≤ 2) && w.2.all (fun a => decide (a ∈ w.1)) &&
      levTwoS3t_coversWith levTwoS3f4_reflPerm cl
        (levTwoS3u_repOf (n := Tag.rank Tag.F4) levTwoS3f4_roots cl)
        (levTwoS3f4_patPerms m l) (levTwoS3f4_seed m l) w.1 w.2) = true)
    (hall : ∀ T : Finset (Fin cl.length), ∃ w ∈ ws, ∀ a, a ∈ w.1 ↔ a ∈ T) :
    TCRoot (isFiniteType_cartan Tag.F4) ↑(levTwoS3f4_patSet m l) := by
  have hrep_mem : ∀ a : Fin cl.length,
      levTwoS3u_repOf (n := Tag.rank Tag.F4) levTwoS3f4_roots cl a ∈ levTwoS3f4_rootVecs :=
    levTwoS3u_rep_mem (n := Tag.rank Tag.F4) (roots := levTwoS3f4_roots) (cl := cl)
      (fun a => hcl_rep_lt a)
  have hrep_notMemF : ∀ a : Fin cl.length,
      levTwoS3u_repOf (n := Tag.rank Tag.F4) levTwoS3f4_roots cl a ∉
        levTwoS3f4_patSetF m l :=
    levTwoS3u_notMem_patSet_of_not_bit (n := Tag.rank Tag.F4) levTwoS3f4_hnodup
      levTwoS3f4_hlen (fun a => hcl_rep_lt a) hrep_notpat
  have hrep_notMem : ∀ a : Fin cl.length,
      levTwoS3u_repOf (n := Tag.rank Tag.F4) levTwoS3f4_roots cl a ∉
        ↑(levTwoS3f4_patSet m l) := by
    intro a
    change levTwoS3u_repOf (n := Tag.rank Tag.F4) levTwoS3f4_roots cl a ∉
      (levTwoS3f4_patSet m l : Set (Fin (Tag.rank Tag.F4) → ℤ))
    rw [← levTwoS3f4_patSetF_eq]
    exact hrep_notMemF a
  have hrep_notMem_imp : ∀ a : Fin cl.length,
      (∃ r ∈ levTwoS3f4_rootVecs, r ∉ ↑(levTwoS3f4_patSet m l) ∧
        levTwoS3u_clsOf levTwoS3f4_roots cl hpos r = a) →
      levTwoS3u_repOf (n := Tag.rank Tag.F4) levTwoS3f4_roots cl a ∉
        ↑(levTwoS3f4_patSet m l) :=
    fun a _ => hrep_notMem a
  have hrep_eq : ∀ a : Fin cl.length,
      levTwoS3u_repOf (n := Tag.rank Tag.F4) levTwoS3f4_roots cl a
        = levTwoS3f4_rootVecs.getD (cl.getD a.val (0, 0)).1 0 :=
    fun a => (levTwoS3u_getD_map (Tag.rank Tag.F4) levTwoS3f4_roots _).symm
  have hcoverW := levTwoS3v_hcoverW_of_table (cl := cl)
    (rep := levTwoS3u_repOf (n := Tag.rank Tag.F4) levTwoS3f4_roots cl)
    levTwoS3f4_reflPerm (levTwoS3f4_patPerms m l) (levTwoS3f4_seed m l) ws hws hall
  have hΦrt : ∀ β ∈ (↑(levTwoS3f4_patSet m l) : Set (Fin (Tag.rank Tag.F4) → ℤ)),
      IsRt (isFiniteType_cartan Tag.F4) β := by
    intro β hβ
    rw [← levTwoS3f4_patSetF_eq] at hβ
    exact levTwoS3u_isRt_of_mem_patSet levTwoS3f4_hRl (fun _ => Iff.rfl) β hβ
  refine levTwoS3v_tcRoot_of_tables_ws
    (roots := levTwoS3f4_rootVecs) (hRl := levTwoS3f4_hRl)
    (pm := levTwoS3f4_patMask m l) (Φ := ↑(levTwoS3f4_patSet m l))
    (hΦ := fun β => levTwoS3f4_mem_patSet_vec_iff m l β) (hΦrt := hΦrt)
    (gens := levTwoS3f4_gensOf m l) (negP := levTwoS3f4_negPermLit)
    (perms := levTwoS3f4_patPerms m l)
    (hperms := ?_)
    (reflPerm := levTwoS3f4_reflPerm)
    (hgen_mem := levTwoS3f4_gens_mem_patSet m l)
    (hgen_step := levTwoS3f4_gens_step m l)
    (hneg := levTwoS3f4_negStep)
    (hinv := levTwoS3f4_inv m l) (hrange := levTwoS3f4_range m l)
    (cl := cl) (cls := levTwoS3u_clsOf levTwoS3f4_roots cl hpos)
    (rep := levTwoS3u_repOf (n := Tag.rank Tag.F4) levTwoS3f4_roots cl)
    (hrep_mem := hrep_mem) (hrep_cls := hrep_cls) (hrep_notMem := hrep_notMem_imp)
    (hrep_eq := hrep_eq) (hrefl := hrefl)
    (hcls_orbit := hcls_orbit)
    (hcl_bfs := fun a ha => hcl_bfs ⟨a, ha⟩)
    (hcl_rep_lt := fun a ha => hcl_rep_lt ⟨a, ha⟩)
    (seed := levTwoS3f4_seed m l) (hseed := ?_)
    (hcoverW := hcoverW)
  · rw [levTwoS3f4_patPerms, levTwoS3f4_gensOf, List.map_map]
    rw [levTwoS3f4_negPermLit_eq]
    rfl
  · intro i hi
    rw [levTwoS3f4_seed] at hi
    rw [List.mem_filter] at hi
    refine ⟨by rw [levTwoS3f4_rootVecs_len]; exact List.mem_range.mp hi.1, hi.2⟩

end CFSG.StandardType.LevTwo
