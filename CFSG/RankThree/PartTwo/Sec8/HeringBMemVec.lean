module

public import CFSG.RankThree.PartTwo.Sec8.Item8KFacts3ProofSp62

public section

namespace CFSG.RankThree.PartTwo.Sec8.HeringBMem

open CFSG.RankThree.PartTwo.Sec8.Item8KFacts3 CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two

theorem vAct_injective : Function.Injective vAct := by
  intro g h hgh
  apply mat6_injective
  ext i j
  have := congrArg (fun p : Equiv.Perm (Fin 6 → ZMod 2) => p (Pi.single j 1) i) hgh
  simpa [vAct_apply, Matrix.mulVec_single_one] using this

theorem vAct_add (g : H6) (x y : Fin 6 → ZMod 2) : vAct g (x + y) = vAct g x + vAct g y := by
  simp only [vAct_apply, Matrix.mulVec_add]

theorem vAct_zero (g : H6) : vAct g 0 = 0 := by
  simp only [vAct_apply, Matrix.mulVec_zero]

theorem bF_symm (x y : Fin 6 → ZMod 2) : bF x y = bF y x := by
  revert x y
  decide +kernel

theorem bF_self (x : Fin 6 → ZMod 2) : bF x x = 0 := by
  revert x
  decide +kernel

theorem bF_add_left (x x' y : Fin 6 → ZMod 2) : bF (x + x') y = bF x y + bF x' y := by
  simp [bF, add_dotProduct]

theorem bF_add_right (x y y' : Fin 6 → ZMod 2) : bF x (y + y') = bF x y + bF x y' := by
  simp [bF, Matrix.mulVec_add, dotProduct_add]

theorem bF_nondeg (a : Fin 6 → ZMod 2) (ha : a ≠ 0) : ∃ w, bF w a = 1 := by
  revert a
  decide +kernel

@[expose] def Pl (l : Fin 3) : Finset (Fin 6 → ZMod 2) :=
  Finset.univ.filter fun y => ∀ r : Fin 6, r ≠ pos l → r ≠ pos3 l → y r = 0

@[expose] def Pp (l : Fin 3) : Finset (Fin 6 → ZMod 2) :=
  Finset.univ.filter fun y => y (pos l) = 0 ∧ y (pos3 l) = 0

theorem card_Pl (l : Fin 3) : (Pl l).card = 4 :=
  card_planeSet l

theorem card_Pp : ∀ l : Fin 3, (Pp l).card = 16 := by
  decide +kernel

theorem mem_Pp {l : Fin 3} {y : Fin 6 → ZMod 2} : y ∈ Pp l ↔ y (pos l) = 0 ∧ y (pos3 l) = 0 := by
  simp [Pp]

theorem mem_Pl {l : Fin 3} {y : Fin 6 → ZMod 2} :
    y ∈ Pl l ↔ ∀ r : Fin 6, r ≠ pos l → r ≠ pos3 l → y r = 0 := by
  simp [Pl]

theorem zero_mem_Pp (l : Fin 3) : (0 : Fin 6 → ZMod 2) ∈ Pp l := by
  rw [mem_Pp]
  simp

theorem Pp_add {l : Fin 3} {b b' : Fin 6 → ZMod 2} (hb : b ∈ Pp l) (hb' : b' ∈ Pp l) :
    b + b' ∈ Pp l := by
  rw [mem_Pp] at hb hb' ⊢
  simp [hb.1, hb.2, hb'.1, hb'.2]

theorem decomp_plane (l : Fin 3) (y : Fin 6 → ZMod 2) :
    ∃ s ∈ Pl l, ∃ b ∈ Pp l, y = s + b := by
  refine ⟨fun r => if r = pos l ∨ r = pos3 l then y r else 0, ?_,
    fun r => if r = pos l ∨ r = pos3 l then 0 else y r, ?_, ?_⟩
  · rw [mem_Pl]
    intro r h1 h2
    simp [h1, h2]
  · rw [mem_Pp]
    have h3 : pos l ≠ pos3 l := by
      fin_cases l <;> decide
    simp [h3]
  · funext r
    by_cases h : r = pos l ∨ r = pos3 l <;> simp [h]

set_option maxRecDepth 100000 in
set_option synthInstance.maxSize 4096 in
theorem wt1_check : ∀ x : Fin 3 → ZMod 3, ∀ k : Fin 3, x k ≠ 0 → (∀ i, i ≠ k → x i = 0) →
    Pl k = Finset.univ.image (fun y => wAct x y - y) ∧
      Pp k = Finset.univ.filter (fun y => wAct x y = y) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option synthInstance.maxSize 4096 in
theorem wt2_check : ∀ x : Fin 3 → ZMod 3, ∀ l : Fin 3, x l = 0 → (∀ i, i ≠ l → x i ≠ 0) →
    Pl l = Finset.univ.filter (fun y => wAct x y = y) ∧
      Pp l = Finset.univ.image (fun y => wAct x y - y) := by
  decide +kernel

end CFSG.RankThree.PartTwo.Sec8.HeringBMem
