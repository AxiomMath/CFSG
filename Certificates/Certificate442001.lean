module

public import Certificates.Data.OmegaT0
import CFSG.Certificates.Kernel.PermCent.CVSound
import Certificates.Kernel.PermCent.K442001S
import Certificates.Kernel.PermCent.K442001N
public import Certificates.Data.Kernel.PermCent.CV

public section

open CFSG.GH74.KGroups CFSG.ComponentClassification.CatFactsSmall.PSp43
  CFSG.Certificates.Kernel.PkCV CFSG.Certificates.Kernel.PkCV.P45T Certificates.OmegaT0

namespace Certificates

private theorem sylow_eq : sylowChk () = sylowC := by
  unfold sylowChk sylowC
  rw [elemsT_eq_elemsC, elemsT_eq_elemsC]
  simp only [List.filter_map, List.length_map, List.all_map, Function.comp_def, ev_mul',
    decide_ev_eq, decide_mem_map_ev, comm_fast]

private theorem wordW_ev (gs : List (CV 45)) (w : List ℕ) :
    wordW (gs.map ev) w = ev (wordW gs w) := by
  induction w with
  | nil => exact ev_one.symm
  | cons i w ih =>
    simp only [wordW, List.foldr_cons] at ih ⊢
    rw [ev_mul, ← ih, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
    cases gs[i]? with
    | none => rw [Option.map_none, Option.getD_none, Option.getD_none, ev_one]
    | some g => rw [Option.map_some, Option.getD_some, Option.getD_some]

private theorem coverW_ev (gs reps L : List (CV 45)) (ws : List (List ℕ)) :
    coverW (gs.map ev) (reps.map ev) (L.map ev) ws = coverW gs reps L ws := by
  induction L generalizing ws with
  | nil => rfl
  | cons t L ih =>
    have e1 : decide (ev t * ev t = 1 ∧ ev t ≠ 1) = decide (t * t = 1 ∧ t ≠ 1) :=
      decide_eq_decide.2 (by rw [ev_mul', one_eq_ev, ne_eq, ev_eq_iff, ev_eq_iff])
    cases ws with
    | nil => simp only [List.map_cons, coverW, e1, ih]
    | cons w ws =>
      simp only [List.map_cons, coverW]
      rw [e1]
      simp only [ih, List.any_map, Function.comp_def, wordW_ev, ev_inv', ev_mul', decide_ev_eq]

private theorem treeL_ev (f : CV 45 → CV 45 → CV 45)
    (f' : Equiv.Perm (Fin 45) → Equiv.Perm (Fin 45) → Equiv.Perm (Fin 45))
    (hf : ∀ s x, f' (ev s) (ev x) = ev (f s x)) (a : CV 45) (gs : List (CV 45))
    (ps : List (ℕ × ℕ)) : treeL f' (ev a) (gs.map ev) ps = (treeL f a gs ps).map ev := by
  have key : ∀ (L : List (CV 45)) (ps : List (ℕ × ℕ)),
      ps.foldl (fun L kp => L ++ [f' ((gs.map ev).getD kp.1 1) (L.getD kp.2 (ev a))]) (L.map ev) =
        (ps.foldl (fun L kp => L ++ [f (gs.getD kp.1 1) (L.getD kp.2 a)]) L).map ev := by
    intro L ps
    induction ps generalizing L with
    | nil => rfl
    | cons kp ps ih =>
      rw [List.foldl_cons, List.foldl_cons, ← ih]
      congr 1
      rw [List.map_append, List.map_singleton, ← hf, ← ev_one, List.getD_map, List.getD_map]
  unfold treeL
  exact key [a] ps

private theorem treeL_mul_ev (gs : List (CV 45)) (ps : List (ℕ × ℕ)) :
    treeL (· * ·) 1 (gs.map ev) ps = (treeL (· * ·) 1 gs ps).map ev := by
  have e := treeL_ev (· * ·) (· * ·) (fun s x => (ev_mul s x).symm) 1 gs ps
  rw [ev_one] at e
  exact e

private theorem orbTr_ev (cd : Equiv.Perm (Fin 45) → ℕ) (gs : List (CV 45)) (r : CV 45)
    (ps : List (ℕ × ℕ)) (ts : List (List ℕ)) (k : ℕ) :
    orbTr cd (gs.map ev) (ev r) ps ts k = orbTr (fun c => cd (ev c)) gs r ps ts k := by
  have hO := treeL_ev (fun s o => s * o * s⁻¹) (fun s o => s * o * s⁻¹)
    (fun s x => by rw [ev_mul, ev_mul, ev_inv]) r gs ps
  unfold orbTr
  simp only [hO, List.length_map, List.map_map, List.zip_map_left,
    List.all_map, Function.comp_def, Prod.map_fst, Prod.map_snd, id_eq, List.getD_map, ev_inv',
    ev_mul', decide_ev_eq]

private theorem coverW_ev2 (a b c d : CV 45) (L : List (CV 45)) (ws : List (List ℕ)) :
    coverW [ev a, ev b] [ev c, ev d] (L.map ev) ws = coverW [a, b] [c, d] L ws :=
  coverW_ev [a, b] [c, d] L ws

private theorem orbTr_ev2 (cd : Equiv.Perm (Fin 45) → ℕ) (a b r : CV 45) (ps : List (ℕ × ℕ))
    (ts : List (List ℕ)) (k : ℕ) :
    orbTr cd [ev a, ev b] (ev r) ps ts k = orbTr (fun c => cd (ev c)) [a, b] r ps ts k :=
  orbTr_ev cd [a, b] r ps ts k

private theorem sylW_ev (a b : CV 45) :
    sylW.map (wordW [ev a, ev b]) = (sylW.map (wordW [a, b])).map ev := by
  rw [List.map_map]
  exact List.map_congr_left fun w _ => wordW_ev [a, b] w

private theorem mulTab_ev (gs L : List (CV 45)) (ts : List (List ℕ)) (k : ℕ) :
    mulTab (gs.map ev) (L.map ev) ts k = mulTab gs L ts k := by
  have h1 : (1 : Equiv.Perm (Fin 45)) = ev 1 := ev_one.symm
  unfold mulTab
  rw [h1]
  simp only [List.length_map, List.zip_map_left, List.all_map, Function.comp_def, Prod.map_fst,
    Prod.map_snd, id_eq, List.getD_map, ev_mul', decide_ev_eq]

private theorem n7_eq : n7Chk () = n7C := by
  unfold n7Chk n7C cntCent cntCentC t0L
  conv_lhs => rw [eq_ev_cOf x45, eq_ev_cOf y45, eq_ev_cOf (z0 ()), eq_ev_cOf (yB ()),
    eq_ev_cOf (za ()), eq_ev_cOf (zb ()), eq_ev_cOf (ya ()), eq_ev_cOf (yb ())]
  simp only [sylW_ev, treeL_mul_ev, mulTab_ev, coverW_ev2, orbTr_ev2, List.filter_map,
    List.length_map, Function.comp_def, ev_mul', ev_inv', decide_ev_eq, decide_mem_map_ev,
    comm_fast]

theorem certificate442001 : OmegaT0.check () = true := by
  rw [check.eq_1, sylow_eq, n7_eq, k442001S, k442001N]
  rfl

end Certificates
