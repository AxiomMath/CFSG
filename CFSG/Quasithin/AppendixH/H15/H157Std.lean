module

public import CFSG.Quasithin.AppendixH.H15.H157Basic

public section

namespace CFSG.ASVolI.AppH.H157

open CFSG.Quasithin CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H153 CFSG.ASVolI.ChH
  CFSG.Monster.Code

@[expose] def fixListT : List ℕ :=
  [0, 31, 175, 176, 323, 348, 492, 499, 621, 626, 706, 733, 814, 817, 897, 926, 1064, 1079, 1159,
    1176, 1387, 1396, 1476, 1499, 1605, 1626, 1770, 1781, 1798, 1817, 1961, 1974]

theorem fixListT_eq :
    (List.range 2048).filter (fun m => act11 tArr m == m) = fixListT := by
  unfold fixListT
  decide +kernel

theorem msk_decide_eq {n : ℕ} (a b : Msk n) :
    (decide (a = b) : Bool) = decide (a.val = b.val) := by
  by_cases h : a = b
  · rw [decide_eq_true h, decide_eq_true (congrArg Msk.val h)]
  · have h' : a.val ≠ b.val := fun hv => h (Msk.ext' hv)
    rw [decide_eq_false h, decide_eq_false h']

theorem msk_decide_mem {n : ℕ} (x : Msk n) (l : List (Msk n)) :
    (decide (x ∈ l) : Bool) = decide (x.val ∈ l.map Msk.val) := by
  by_cases h : x ∈ l
  · rw [decide_eq_true h, decide_eq_true (List.mem_map.mpr ⟨x, h, rfl⟩)]
  · rw [decide_eq_false h, decide_eq_false (fun hv => ?_)]
    obtain ⟨y, hy, hyv⟩ := List.mem_map.mp hv
    exact h (Msk.ext' hyv ▸ hy)

theorem msk_findIdx {n : ℕ} (x : Msk n) (l : List (Msk n)) :
    List.findIdx (fun y => y == x) l = List.findIdx (fun y => y == x.val) (l.map Msk.val) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
      rw [List.map_cons, List.findIdx_cons, List.findIdx_cons]
      have h : (a == x) = (a.val == x.val) := by
        show decide (a = x) = decide (a.val = x.val)
        exact msk_decide_eq a x
      rw [h, ih]

theorem msk_idxOf {n : ℕ} (x : Msk n) (l : List (Msk n)) :
    List.idxOf x l = List.idxOf x.val (l.map Msk.val) :=
  msk_findIdx x l

theorem avoidOK_fixListT : avoidOK 11 2 o2Masks24 fixListT = true := by
  simp only [avoidOK, forallGreedy, greedyExt, startPos, pos]
  simp only [msk_decide_eq, msk_decide_mem, msk_idxOf]
  decide +kernel

theorem rhoM24_tA_toW (m : ℕ) : rhoM24 tA (toW 11 m) = toW 11 (act11 tArr m) := by
  exact rho11_toW AutPerm le_rfl tA hasArr_tP m

theorem mem_fixListT_iff {m : ℕ} (hm : m < 2 ^ 11) :
    rhoM24 tA (toW 11 m) = toW 11 m ↔ m ∈ fixListT := by
  rw [rhoM24_tA_toW, ← fixListT_eq, List.mem_filter, List.mem_range]
  constructor
  · intro h
    exact ⟨hm, beq_iff_eq.mpr (toW_inj (act11_lt tArr m) hm h)⟩
  · rintro ⟨-, h⟩
    exact congrArg (toW 11) (beq_iff_eq.mp h)

theorem card_fixW_tA : Nat.card ↥(fixW tA) = 32 := by
  have hP : ∀ m < 2 ^ 11,
      (MaskCoords.std 11).vm m ∈ fixW tA ↔ (act11 tArr m == m) = true := by
    intro m hm
    rw [mem_fixW]
    change rhoM24 tA (toW 11 m) = toW 11 m ↔ (act11 tArr m == m) = true
    rw [mem_fixListT_iff hm]
    rw [← fixListT_eq, List.mem_filter, List.mem_range, beq_iff_eq]
    exact ⟨fun h => h.2, fun h => ⟨hm, h⟩⟩
  have h := (MaskCoords.std 11).card_eq (fixW tA) (fun m => act11 tArr m == m) hP
  rw [h]
  rw [show (2 : ℕ) ^ 11 = 2048 by norm_num]
  rw [fixListT_eq]
  rfl

end CFSG.ASVolI.AppH.H157
