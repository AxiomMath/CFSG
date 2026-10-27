
module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312M24Lat
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312M24Enum

public section

namespace CFSG.Quasithin.A312M24

open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.QuasithinUnique.Ch1.SporLat
open CFSG.QuasithinUnique.Ch1.SporLat.M24

@[expose] def slpL (ta tb : List ℕ) (prog : List (ℕ × ℕ)) : List (List ℕ) :=
  prog.foldl (fun l p => l ++ [compTab (l.getD p.1 []) (l.getD p.2 [])]) [ta, tb]

theorem getElem!_toList_aux (acc : Array (Array ℕ)) (i : ℕ) :
    (acc[i]!).toList = (acc.toList.map Array.toList).getD i [] := by
  by_cases h : i < acc.size
  · simp [List.getD_eq_getElem?_getD, h]
  · simp [List.getD_eq_getElem?_getD, h]
    rfl

theorem slpFold_eq (prog : List (ℕ × ℕ)) (acc : Array (Array ℕ)) :
    (prog.foldl slpStepA acc).toList.map Array.toList =
      prog.foldl (fun l p => l ++ [compTab (l.getD p.1 []) (l.getD p.2 [])])
        (acc.toList.map Array.toList) := by
  induction prog generalizing acc with
  | nil => rfl
  | cons p prog ih =>
    simp only [List.foldl_cons]
    rw [ih]
    congr 1
    unfold slpStepA
    rw [Array.toList_push, List.map_append, List.map_cons, List.map_nil, compArr_toList,
      getElem!_toList_aux, getElem!_toList_aux]

theorem slpTabsA_eq (ta tb : List ℕ) (prog : List (ℕ × ℕ)) :
    (slpTabsA ta.toArray tb.toArray prog).toList.map Array.toList = slpL ta tb prog :=
  slpFold_eq prog #[ta.toArray, tb.toArray]

@[expose] def sTL : List (List ℕ) := [
  [16, 18, 11, 14, 8, 1, 4, 20, 12, 5, 23, 21, 6, 2, 17, 22, 10, 19, 9, 3, 15, 13, 7, 0],
  [7, 1, 3, 2, 5, 4, 6, 0, 8, 9, 21, 20, 18, 13, 16, 17, 14, 15, 12, 19, 11, 10, 22, 23],
  [7, 1, 2, 3, 12, 5, 8, 0, 6, 9, 10, 23, 4, 20, 22, 15, 19, 21, 18, 16, 13, 17, 14, 11],
  [23, 1, 13, 19, 4, 5, 6, 22, 8, 9, 20, 17, 12, 2, 21, 16, 15, 11, 18, 3, 10, 14, 7, 0]]

theorem sTL_eq : m24Qp.map (fun p => (slpL m24ta m24tb m24Prog).getD p.1 []) = sTL := by
  decide +kernel

theorem m24Sg_tab : m24Sg.map (tab 24) = sTL := by
  have h := congrArg (List.map Array.toList) m24_sGens.1
  simp only [genTabs, List.map_map, Function.comp_def] at h
  rw [h]
  rw [← sTL_eq]
  simp only [m24STabs, List.map_map, Function.comp_def]
  apply List.map_congr_left
  intro p _
  rw [getElem!_toList_aux]
  show (List.map Array.toList (slpTabsA m24ta.toArray m24tb.toArray m24Prog).toList).getD p.1 [] = _
  rw [slpTabsA_eq]

theorem m24Sg_length : m24Sg.length = 4 := by
  have h := congrArg List.length m24Sg_tab
  simpa [sTL] using h

end CFSG.Quasithin.A312M24
