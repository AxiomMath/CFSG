module

public import CFSG.Quasithin.AppendixH.H14.H142StdDefs
public import CFSG.Quasithin.AppendixH.H14.H142Arr
public import CFSG.Certificates.Kernel.MathieuAut.InAutKSound

public section

namespace CFSG.Quasithin.AppendixH.H14.QDataK

open CFSG.Quasithin.H.Mathieu CFSG.KS.MathieuAut

@[expose] def masksOKL (cs : List ℕ) : Bool := qMasks.all fun m => qMasks.contains (actM cs m)

@[expose] def repOKL (l : List ℕ) : Bool :=
  inAutKL l && l.getD 8 0 == 8 && masksOKL (l.map (2 ^ ·))

theorem getElem!_eq_getD_toList {α : Type} [Inhabited α] (a : Array α) (x : ℕ) :
    a[x]! = a.toList.getD x default := by
  by_cases hx : x < a.size
  · rw [getElem!_pos a x hx, List.getD_eq_getElem _ _ (by simpa using hx), Array.getElem_toList]
  · rw [getElem!_neg a x hx, List.getD_eq_default _ _ (by simpa using hx)]

theorem list_getElem!_eq_getD {α : Type} [Inhabited α] (l : List α) (x : ℕ) :
    l[x]! = l.getD x default := by
  by_cases hx : x < l.length
  · rw [getElem!_pos l x hx, List.getD_eq_getElem _ _ hx]
  · rw [getElem!_neg l x hx, List.getD_eq_default _ _ (by omega)]

theorem repOK_sound {a : Array ℕ} (h : (a.size == 24 && repOKL a.toList) = true) :
    inAutOK a = true ∧ a[8]! = 8 ∧ ∀ m ∈ qMasks, permM a m ∈ qMasks := by
  simp only [repOKL, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨ha, ⟨hK, h8⟩, hM⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · rw [inAutOK_eq_K, inAutK, if_pos ha]
    exact hK
  · rw [getElem!_eq_getD_toList]
    exact h8
  · intro m hm
    rw [permM, permCols_eq ha]
    simp only [masksOKL, List.all_eq_true, List.contains_iff_mem] at hM
    exact hM m hm

@[expose] def compL (g r : List ℕ) : List ℕ := r.map fun x => g.getD x 0

theorem compL_eq {g r c : Array ℕ} (hr : r.size = 24) (h : c.toList = compL g.toList r.toList) :
    c = comp24 g r := by
  apply Array.toList_inj.1
  rw [h, comp24, Array.toList_ofFn]
  apply List.ext_getElem
  · rw [compL, List.length_map, Array.length_toList, hr, List.length_ofFn]
  · intro i h1 _
    have hi : i < r.size := by
      rw [compL, List.length_map, Array.length_toList] at h1
      exact h1
    rw [List.getElem_ofFn]
    simp only [compL, List.getElem_map, Array.getElem_toList, Fin.val_mk]
    rw [getElem!_pos r i hi, getElem!_eq_getD_toList g]
    try rfl

theorem size_of_all {L : List (Array ℕ)}
    (h : (L.all fun a => a.size == 24 && repOKL a.toList) = true) : ∀ a ∈ L, a.size = 24 := by
  intro a ha
  have := List.all_eq_true.1 h a ha
  simp only [Bool.and_eq_true, beq_iff_eq] at this
  exact this.1

@[expose] def bfsL (n : ℕ) (B : List (ℕ × ℕ)) (R G : List (Array ℕ)) : Bool :=
  ((List.range n).zip (B.zip R)).all fun e => e.1 == 0 || (decide (e.2.1.2 < e.1) &&
    decide (e.2.1.1 < 2) && e.2.2.toList == compL (G.getD e.2.1.1 #[]).toList (R.getD e.2.1.2 #[]).toList)

theorem bfs_sound {n : ℕ} {B : List (ℕ × ℕ)} {R : Array (Array ℕ)} {G : List (Array ℕ)}
    (hB : B.length = n) (hR : R.size = n) (hsz : ∀ a ∈ R.toList, a.size = 24)
    (h : bfsL n B R.toList G = true) :
    ∀ k < n, 0 < k → (B.getD k (0, 0)).2 < k ∧ (B.getD k (0, 0)).1 < 2 ∧
      R[k]! = comp24 G[(B.getD k (0, 0)).1]! R[(B.getD k (0, 0)).2]! := by
  intro k hk hk0
  have hRl : R.toList.length = n := by rw [Array.length_toList, hR]
  have hz : k < ((List.range n).zip (B.zip R.toList)).length := by
    simp only [List.length_zip, List.length_range, hB, hRl, Nat.min_self]
    exact hk
  have he := List.all_eq_true.1 h _ (List.getElem_mem hz)
  simp only [List.getElem_zip, List.getElem_range] at he
  have hBk : B.getD k (0, 0) = B[k]'(by omega) := List.getD_eq_getElem _ _ _
  have hRk : R[k]! = R.toList[k]'(by omega) := by
    rw [getElem!_eq_getD_toList, List.getD_eq_getElem _ _ (by omega)]
  have hk0' : (k == 0) = false := by simp; omega
  rw [hk0', Bool.false_or] at he
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at he
  obtain ⟨⟨h1, h2⟩, h3⟩ := he
  rw [hBk]
  refine ⟨h1, h2, ?_⟩
  have hp : (R.toList.getD (B[k]'(by omega)).2 #[]).size = 24 := by
    have hpl : (B[k]'(by omega)).2 < R.toList.length := by omega
    rw [List.getD_eq_getElem _ _ hpl]
    exact hsz _ (List.getElem_mem hpl)
  rw [hRk, list_getElem!_eq_getD, getElem!_eq_getD_toList R]
  exact compL_eq hp h3

theorem any_of_mem {T : List (ℕ × ℕ × ℕ)} {n : ℕ} (hT : T.length = n) {f0 f1 f2 : ℕ → ℕ}
    (h0 : ∀ k, f0 k = (T.getD k (0, 0, 0)).1) (h1 : ∀ k, f1 k = (T.getD k (0, 0, 0)).2.1)
    (h2 : ∀ k, f2 k = (T.getD k (0, 0, 0)).2.2) {s v0 v1 : ℕ} (h : (s, v0, v1) ∈ T) :
    ((List.range n).any fun k => f0 k == s && f1 k == v0 && f2 k == v1) = true := by
  obtain ⟨k, hk, he⟩ := List.mem_iff_getElem.1 h
  rw [List.any_eq_true]
  refine ⟨k, List.mem_range.2 (hT ▸ hk), ?_⟩
  rw [h0, h1, h2, List.getD_eq_getElem _ _ hk, he]
  simp

theorem all3_mono {P Q : ℕ → ℕ → ℕ → Bool} (h : ∀ s v0 v1, P s v0 v1 = true → Q s v0 v1 = true)
    (hP : ((List.range 2).all fun s => (List.range 16).all fun v0 => (List.range 16).all fun v1 =>
      P s v0 v1) = true) :
    ((List.range 2).all fun s => (List.range 16).all fun v0 => (List.range 16).all fun v1 =>
      Q s v0 v1) = true := by
  simp only [List.all_eq_true] at hP ⊢
  exact fun s hs v0 hv0 v1 hv1 => h s v0 v1 (hP s hs v0 hv0 v1 hv1)

end CFSG.Quasithin.AppendixH.H14.QDataK

end
