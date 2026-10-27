module

public import CFSG.LocalAnalysis.StandardType.GGLevTwoS3bE8Tc
public import CFSG.LocalAnalysis.StandardType.GGLevTwoS3bTables4
public import CFSG.LocalAnalysis.StandardType.GGLevTwoS3bPackK
import CFSG.LocalAnalysis.StandardType.GGLevTwoS3aDict

public section

namespace CFSG.StandardType.LevTwo

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsL33d
open CFSG.LieType.RootSystem

theorem levTwoS3b_bfsMask_eq_bfsG (perms : List (List ℕ)) : ∀ (f : ℕ) (q : List ℕ) (v : ℕ),
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

private theorem e8NK_lt' : E8K.e8NK >>> 1920 = 0 := by decide +kernel

theorem levTwoS3b_e8_permsOf_img (m b : ℕ) :
    (levTwoS3b_e8_permsOf m).map (fun p => p.getD b 0) =
      E8K.imgK (E8K.e8NK :: (levTwoS3b_nodesOf m).map (fun x => E8K.e8PK.getD x 0)) b := by
  simp only [levTwoS3b_e8_permsOf, E8K.imgK, List.map_cons, List.map_map]
  congr 1
  · have hn : levTwoS3b_e8NegPerm = E8K.unpack8 E8K.e8NK 240 := by decide +kernel
    rw [hn]
    exact E8K.unpack8_getD 240 _ b e8NK_lt'
  · apply List.map_congr_left
    intro x hx
    have hx9 : x < 9 := by
      simp only [levTwoS3b_nodesOf, List.mem_filter, List.mem_range] at hx
      exact hx.1
    have hp : ∀ x : Fin 9,
        levTwoS3b_e8Perms.getD x.val [] = E8K.unpack8 (E8K.e8PK.getD x.val 0) 240 ∧
          E8K.e8PK.getD x.val 0 >>> 1920 = 0 := by decide +kernel
    simp only [Function.comp_apply]
    rw [(hp ⟨x, hx9⟩).1]
    exact E8K.unpack8_getD 240 _ b (hp ⟨x, hx9⟩).2

theorem levTwoS3b_e8_bfsMask_K (m f : ℕ) (q : List ℕ) (v : ℕ) :
    levTwoS3b_bfsMask (levTwoS3b_e8_permsOf m) f q v =
      E8K.bfsG (E8K.imgK (E8K.e8NK :: (levTwoS3b_nodesOf m).map (fun x => E8K.e8PK.getD x 0)))
        E8K.bitB f q v := by
  rw [levTwoS3b_bfsMask_eq_bfsG, E8K.bitB_eq, funext (levTwoS3b_e8_permsOf_img m)]

theorem levTwoS3t_coversWith_K {ι : Type} (reflPerm : (ι → ℤ) → List ℕ) (cl : List (ℕ × ℕ))
    (rep : Fin cl.length → ι → ℤ) (perms : List (List ℕ)) (img : ℕ → List ℕ)
    (ext : ℕ → ℕ → ℕ) (himg : ∀ b, perms.map (fun p => p.getD b 0) = img b)
    (hext : ∀ a b, (reflPerm (rep a)).getD b 0 = ext (cl.getD a.1 (0, 0)).1 b)
    (T T' : List (Fin cl.length)) :
    levTwoS3t_coversWith reflPerm cl rep perms [] T T' =
      E8K.covG img ext cl (T.map Fin.val) (T'.map Fin.val) := by
  have hf : (fun b => (perms ++ T'.map (fun a => reflPerm (rep a))).map (fun p => p.getD b 0)) =
      (fun b => img b ++ ((T'.map Fin.val).map (fun a => (cl.getD a (0, 0)).1)).map
        (fun r => ext r b)) := by
    funext b
    rw [List.map_append, himg, List.map_map, List.map_map, List.map_map]
    congr 1
    apply List.map_congr_left
    intro a _
    exact hext a b
  have hr : (T'.map Fin.val).map (fun a => (cl.getD a (0, 0)).1) =
      T'.map (fun a => (cl.getD a.1 (0, 0)).1) := by
    rw [List.map_map]
    rfl
  simp only [levTwoS3t_coversWith, E8K.covG, List.nil_append, levTwoS3b_bfsMask_eq_bfsG,
    E8K.bitB_eq, List.all_map]
  rw [hf, hr]
  rfl

theorem levTwoS3b_e8_reflImg_K (cl : List (ℕ × ℕ))
    (hR : cl.all (fun p => (List.map Prod.fst E8K.e8RK).contains p.1) = true)
    (a : Fin cl.length) (b : ℕ) :
    (levTwoS3b_permOf (List.ofFn (levTwoS3u_repOf (n := Tag.rank Tag.E8) levTwoS3b_roots cl a))).getD
      b 0 = E8K.lk8 (E8K.rkOf E8K.e8RK (cl.getD a.1 (0, 0)).1) b := by
  have hmem := E8K.rep_mem cl _ (by decide) hR a.1
  have hlt : ((List.map Prod.fst E8K.e8RK).all fun r => decide (r < 240)) = true := by
    decide +kernel
  have hr240 : (cl.getD a.1 (0, 0)).1 < 240 := of_decide_eq_true (List.all_eq_true.1 hlt _ hmem)
  have hchecks : E8K.e8RK.all (fun p =>
      E8K.permChkG E8K.e8KP levTwoS3b_key
        (levTwoS3b_roots.map (levTwoS3b_reflv (levTwoS3b_roots.getD p.1 [])))
        (E8K.unpack8 p.2 240) && decide (p.2 >>> 1920 = 0)) = true := by
    decide +kernel
  have hc := List.all_eq_true.1 hchecks _ (E8K.rkOf_mem _ _ hmem)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  have he : levTwoS3b_permOf (levTwoS3b_roots.getD (cl.getD a.1 (0, 0)).1 []) =
      E8K.unpack8 (E8K.rkOf E8K.e8RK (cl.getD a.1 (0, 0)).1) 240 := by
    simpa only [levTwoS3b_permOf, List.map_map, Function.comp_def] using
      E8K.permChkG_sound E8K.e8KP levTwoS3b_key levTwoS3b_keys levTwoS3b_idxK
        (fun _ => rfl) (by decide +kernel) (by decide +kernel)
        (E8K.nodup_of_incB _ (by decide +kernel)) _ _ hc.1
  simp only [levTwoS3u_repOf]
  rw [levTwoS3u_ofFn_vec (Tag.rank Tag.E8) (levTwoS3b_e8_roots_length hr240), he]
  exact E8K.unpack8_getD 240 _ b hc.2

theorem levTwoS3b_e8_hws_of_K (m : ℕ) (cl : List (ℕ × ℕ))
    (reflPerm : (Fin (Tag.rank Tag.E8) → ℤ) → List ℕ)
    (hrp : ∀ β, reflPerm β = levTwoS3b_permOf (List.ofFn β))
    (hR : cl.all (fun p => (List.map Prod.fst E8K.e8RK).contains p.1) = true)
    (ws : List (List (Fin cl.length) × List (Fin cl.length)))
    (h : ws.all (fun w => decide (w.2.length ≤ 2) && w.2.all (fun a => decide (a ∈ w.1)) &&
      E8K.covG (E8K.imgK (E8K.e8NK :: (levTwoS3b_nodesOf m).map (fun x => E8K.e8PK.getD x 0)))
        (fun r b => E8K.lk8 (E8K.rkOf E8K.e8RK r) b) cl (w.1.map Fin.val) (w.2.map Fin.val)) =
        true) :
    ws.all (fun w => decide (w.2.length ≤ 2) && w.2.all (fun a => decide (a ∈ w.1)) &&
      levTwoS3t_coversWith reflPerm cl
        (levTwoS3u_repOf (n := Tag.rank Tag.E8) levTwoS3b_roots cl)
        (levTwoS3b_e8_permsOf m) [] w.1 w.2) = true := by
  have hext : ∀ (a : Fin cl.length) (b : ℕ),
      (reflPerm (levTwoS3u_repOf (n := Tag.rank Tag.E8) levTwoS3b_roots cl a)).getD b 0 =
        E8K.lk8 (E8K.rkOf E8K.e8RK (cl.getD a.1 (0, 0)).1) b := by
    intro a b
    rw [hrp]
    exact levTwoS3b_e8_reflImg_K cl hR a b
  simpa only [levTwoS3t_coversWith_K reflPerm cl _ _ _
    (fun r b => E8K.lk8 (E8K.rkOf E8K.e8RK r) b)
    (levTwoS3b_e8_permsOf_img m) hext] using h

private theorem levTwoS3b_keys_nodup' : levTwoS3b_keys.Nodup :=
  E8K.nodup_of_incB _ (by decide +kernel)

theorem levTwoS3b_e8_permOf_step {g : List ℤ} (hglen : g.length = Tag.rank Tag.E8)
    (hgrt : IsRt (isFiniteType_cartan Tag.E8) (levTwoS3u_vec (Tag.rank Tag.E8) g))
    (i : Fin 240) :
    levTwoS3b_roots.getD ((levTwoS3b_permOf g).getD i.val 0) [] =
      levTwoS3b_reflv g (levTwoS3b_roots.getD i.val []) := by
  have hi : i.val < levTwoS3b_roots.length := by
    rw [levTwoS3b_e8_roots_length240]
    exact i.isLt
  have hv : levTwoS3b_roots.getD i.val [] ∈ levTwoS3b_roots := by
    rw [List.getD_eq_getElem _ _ hi]
    exact List.getElem_mem hi
  have hvlen := levTwoS3b_e8_hlen _ hv
  have hvrt : IsRt (isFiniteType_cartan Tag.E8)
      (levTwoS3u_vec (Tag.rank Tag.E8) (levTwoS3b_roots.getD i.val [])) :=
    (levTwoS3b_e8_hRl _).mpr (List.mem_map.mpr ⟨_, hv, rfl⟩)
  have e : weylAction (isFiniteType_cartan Tag.E8)
      (rRefl (isFiniteType_cartan Tag.E8) (levTwoS3u_vec (Tag.rank Tag.E8) g))
      (levTwoS3u_vec (Tag.rank Tag.E8) (levTwoS3b_roots.getD i.val [])) =
      levTwoS3u_vec (Tag.rank Tag.E8) (levTwoS3b_reflv g (levTwoS3b_roots.getD i.val [])) :=
    levTwoS3b_e8_weylAction_reflv (levTwoS3a_isRt_iff.mp hgrt) (levTwoS3a_isRt_iff.mp hvrt)
      hglen hvlen
  have hw : IsRt (isFiniteType_cartan Tag.E8)
      (levTwoS3u_vec (Tag.rank Tag.E8) (levTwoS3b_reflv g (levTwoS3b_roots.getD i.val []))) := by
    rw [← e]
    exact isRt_smul (isFiniteType_cartan Tag.E8) hvrt _
  have hwlen : (levTwoS3b_reflv g (levTwoS3b_roots.getD i.val [])).length = Tag.rank Tag.E8 := by
    simp only [levTwoS3b_reflv, List.length_zipWith, hvlen, hglen, Nat.min_self]
  obtain ⟨u, hu, huw⟩ := List.mem_map.mp ((levTwoS3b_e8_hRl _).mp hw)
  have hwmem : levTwoS3b_reflv g (levTwoS3b_roots.getD i.val []) ∈ levTwoS3b_roots := by
    have h1 := congrArg List.ofFn huw
    rw [levTwoS3u_ofFn_vec _ (levTwoS3b_e8_hlen u hu), levTwoS3u_ofFn_vec _ hwlen] at h1
    rw [← h1]
    exact hu
  obtain ⟨k, hk, hkw⟩ := List.getElem_of_mem hwmem
  have hkk : k < levTwoS3b_keys.length := by
    rw [levTwoS3b_keys, List.length_map]
    exact hk
  have hp : (levTwoS3b_permOf g).getD i.val 0 = k := by
    rw [levTwoS3b_permOf, List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hi),
      List.getElem_map, ← List.getD_eq_getElem _ [] hi]
    change levTwoS3b_keys.idxOf _ = k
    have hkey : levTwoS3b_key (levTwoS3b_reflv g (levTwoS3b_roots.getD i.val [])) =
        levTwoS3b_keys[k] := by
      rw [← hkw]
      change _ = (levTwoS3b_roots.map levTwoS3b_key)[k]'(by rw [List.length_map]; exact hk)
      rw [List.getElem_map]
    rw [hkey]
    exact levTwoS3b_keys_nodup'.idxOf_getElem k hkk
  rw [hp, List.getD_eq_getElem _ _ hk, hkw]

end CFSG.StandardType.LevTwo
