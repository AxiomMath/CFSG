module

public import CFSG.LocalAnalysis.StandardType.GGLevTwoS3f4Tc
public import CFSG.LocalAnalysis.StandardType.GGLevTwoS3bPackK
import CFSG.LocalAnalysis.StandardType.GGLevTwoS3aDict

public section

namespace CFSG.StandardType.LevTwo

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsL33d
open CFSG.LieType.RootSystem

@[expose] def levTwoS3f4_patPermsK (m l : ℕ) : List (List ℕ) :=
  levTwoS3f4_negPermLit :: (levTwoS3f4_seed m l).map (fun i => levTwoS3f4_reflPerms.getD i [])

@[expose] def levTwoS3f4_covK (cl : List (ℕ × ℕ)) (perms : List (List ℕ)) (seed T T' : List ℕ) :
    Bool :=
  let reps := T'.map (fun a => (cl.getD a (0, 0)).1)
  let q0 := seed ++ reps
  let vis0 := q0.foldl (fun acc b => acc ||| (1 <<< b)) 0
  let orb := E8K.bfsG (fun b => (perms ++ reps.map (fun r => levTwoS3f4_reflPerms.getD r [])).map
    (fun p => p.getD b 0)) E8K.bitB 300 q0 vis0
  T.all (fun a => E8K.bitB orb ((cl.getD a (0, 0)).1))

private theorem f4_bfsMask_eq (perms : List (List ℕ)) : ∀ (f : ℕ) (q : List ℕ) (v : ℕ),
    levTwoS3b_bfsMask perms f q v =
      E8K.bfsG (fun b => perms.map (fun p => p.getD b 0)) Nat.testBit f q v := by
  intro f
  induction f with
  | zero => intro q v; simp [levTwoS3b_bfsMask, E8K.bfsG]
  | succ f ih =>
    intro q v
    cases q with
    | nil => simp [levTwoS3b_bfsMask, E8K.bfsG]
    | cons b rest =>
      simp only [levTwoS3b_bfsMask, E8K.bfsG]
      exact ih _ _

theorem levTwoS3f4_patPerms_K (m l : ℕ) : levTwoS3f4_patPerms m l = levTwoS3f4_patPermsK m l := by
  simp only [levTwoS3f4_patPerms, levTwoS3f4_patPermsK, levTwoS3f4_seed, levTwoS3f4_negPermLit_eq]
  congr 1
  apply List.map_congr_left
  intro i hi
  have hi48 : i < 48 := by
    simp only [List.mem_filter, List.mem_range] at hi
    exact hi.1
  exact (levTwoS3f4_reflPerms_getD hi48).symm

theorem levTwoS3f4_bfsMask_K (m l f : ℕ) (q : List ℕ) (v : ℕ) :
    levTwoS3b_bfsMask (levTwoS3f4_patPerms m l) f q v =
      E8K.bfsG (fun b => (levTwoS3f4_patPermsK m l).map (fun p => p.getD b 0)) E8K.bitB f q v := by
  rw [levTwoS3f4_patPerms_K, f4_bfsMask_eq, E8K.bitB_eq]

theorem levTwoS3f4_coversWith_K (m l : ℕ) (cl : List (ℕ × ℕ))
    (hlt : ∀ a : Fin cl.length, (cl.getD a.val (0, 0)).1 < levTwoS3f4_rootVecs.length)
    (T T' : List (Fin cl.length)) :
    levTwoS3t_coversWith levTwoS3f4_reflPerm cl
        (levTwoS3u_repOf (n := Tag.rank Tag.F4) levTwoS3f4_roots cl)
        (levTwoS3f4_patPerms m l) (levTwoS3f4_seed m l) T T' =
      levTwoS3f4_covK cl (levTwoS3f4_patPermsK m l) (levTwoS3f4_seed m l)
        (T.map Fin.val) (T'.map Fin.val) := by
  have hf : (fun b => (levTwoS3f4_patPerms m l ++ T'.map (fun a => levTwoS3f4_reflPerm
      (levTwoS3u_repOf (n := Tag.rank Tag.F4) levTwoS3f4_roots cl a))).map (fun p => p.getD b 0)) =
      (fun b => (levTwoS3f4_patPermsK m l ++ ((T'.map Fin.val).map
        (fun a => (cl.getD a (0, 0)).1)).map (fun r => levTwoS3f4_reflPerms.getD r [])).map
        (fun p => p.getD b 0)) := by
    funext b
    rw [levTwoS3f4_patPerms_K, List.map_map]
    congr 2
    rw [List.map_map]
    apply List.map_congr_left
    intro a _
    have h1 := hlt a
    rw [levTwoS3f4_rootVecs_len] at h1
    have h2 : (cl.getD a.val (0, 0)).1 < levTwoS3f4_roots.length := by
      rw [levTwoS3f4_roots_len]
      exact h1
    simp only [Function.comp_apply]
    rw [levTwoS3f4_reflPerm_repOf a h2, levTwoS3f4_reflPerms_getD h1]
  have hr : (T'.map Fin.val).map (fun a => (cl.getD a (0, 0)).1) =
      T'.map (fun a => (cl.getD a.1 (0, 0)).1) := by
    rw [List.map_map]
    rfl
  simp only [levTwoS3t_coversWith, levTwoS3f4_covK, f4_bfsMask_eq, E8K.bitB_eq, List.all_map]
  rw [hf, hr]
  rfl

theorem levTwoS3f4_hws_of_K (m l : ℕ) (cl : List (ℕ × ℕ))
    (hlt : ∀ a : Fin cl.length, (cl.getD a.val (0, 0)).1 < levTwoS3f4_rootVecs.length)
    (ws : List (List (Fin cl.length) × List (Fin cl.length)))
    (h : ws.all (fun w => decide (w.2.length ≤ 2) && w.2.all (fun a => decide (a ∈ w.1)) &&
      levTwoS3f4_covK cl (levTwoS3f4_patPermsK m l) (levTwoS3f4_seed m l)
        (w.1.map Fin.val) (w.2.map Fin.val)) = true) :
    ws.all (fun w => decide (w.2.length ≤ 2) && w.2.all (fun a => decide (a ∈ w.1)) &&
      levTwoS3t_coversWith levTwoS3f4_reflPerm cl
        (levTwoS3u_repOf (n := Tag.rank Tag.F4) levTwoS3f4_roots cl)
        (levTwoS3f4_patPerms m l) (levTwoS3f4_seed m l) w.1 w.2) = true := by
  rw [← h]
  congr 1
  funext w
  rw [levTwoS3f4_coversWith_K m l cl hlt]

theorem levTwoS3f4_permOf_step {g : List ℤ} (hglen : g.length = Tag.rank Tag.F4)
    (hgrt : IsRt (isFiniteType_cartan Tag.F4) (levTwoS3u_vec (Tag.rank Tag.F4) g))
    (i : Fin 48) :
    levTwoS3f4_roots.getD ((levTwoS3f4_permOf g).getD i.val 0) [] =
      levTwoS3f4_reflv g (levTwoS3f4_roots.getD i.val []) := by
  have hi : i.val < levTwoS3f4_roots.length := by
    rw [levTwoS3f4_roots_len]
    exact i.isLt
  have hv : levTwoS3f4_roots.getD i.val [] ∈ levTwoS3f4_roots := by
    rw [List.getD_eq_getElem _ _ hi]
    exact List.getElem_mem hi
  have hvlen := levTwoS3f4_hlen _ hv
  have hvrt : IsRt (isFiniteType_cartan Tag.F4)
      (levTwoS3u_vec (Tag.rank Tag.F4) (levTwoS3f4_roots.getD i.val [])) :=
    (levTwoS3f4_hRl _).mpr (List.mem_map.mpr ⟨_, hv, rfl⟩)
  have e : weylAction (isFiniteType_cartan Tag.F4)
      (rRefl (isFiniteType_cartan Tag.F4) (levTwoS3u_vec (Tag.rank Tag.F4) g))
      (levTwoS3u_vec (Tag.rank Tag.F4) (levTwoS3f4_roots.getD i.val [])) =
      levTwoS3u_vec (Tag.rank Tag.F4) (levTwoS3f4_reflv g (levTwoS3f4_roots.getD i.val [])) :=
    levTwoS3f4_weylAction_reflv (levTwoS3a_isRt_iff.mp hgrt) (levTwoS3a_isRt_iff.mp hvrt)
      hglen hvlen
  have hw : IsRt (isFiniteType_cartan Tag.F4)
      (levTwoS3u_vec (Tag.rank Tag.F4) (levTwoS3f4_reflv g (levTwoS3f4_roots.getD i.val []))) := by
    rw [← e]
    exact isRt_smul (isFiniteType_cartan Tag.F4) hvrt _
  have hwlen : (levTwoS3f4_reflv g (levTwoS3f4_roots.getD i.val [])).length = Tag.rank Tag.F4 := by
    simp only [levTwoS3f4_reflv, List.length_zipWith, hvlen, hglen, Nat.min_self]
  obtain ⟨u, hu, huw⟩ := List.mem_map.mp ((levTwoS3f4_hRl _).mp hw)
  have hwmem : levTwoS3f4_reflv g (levTwoS3f4_roots.getD i.val []) ∈ levTwoS3f4_roots := by
    have h1 := congrArg List.ofFn huw
    rw [levTwoS3u_ofFn_vec _ (levTwoS3f4_hlen u hu), levTwoS3u_ofFn_vec _ hwlen] at h1
    rw [← h1]
    exact hu
  obtain ⟨k, hk, hkw⟩ := List.getElem_of_mem hwmem
  have hkk : k < levTwoS3f4_keys.length := by
    rw [levTwoS3f4_keys, List.length_map]
    exact hk
  have hp : (levTwoS3f4_permOf g).getD i.val 0 = k := by
    rw [levTwoS3f4_permOf, List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hi),
      List.getElem_map, ← List.getD_eq_getElem _ [] hi]
    change levTwoS3f4_keys.idxOf _ = k
    have hkey : levTwoS3f4_key (levTwoS3f4_reflv g (levTwoS3f4_roots.getD i.val [])) =
        levTwoS3f4_keys[k] := by
      rw [← hkw]
      change _ = (levTwoS3f4_roots.map levTwoS3f4_key)[k]'(by rw [List.length_map]; exact hk)
      rw [List.getElem_map]
    rw [hkey]
    exact List.Nodup.idxOf_getElem levTwoS3f4_keys_nodup k hkk
  rw [hp, List.getD_eq_getElem _ _ hk, hkw]

end CFSG.StandardType.LevTwo
