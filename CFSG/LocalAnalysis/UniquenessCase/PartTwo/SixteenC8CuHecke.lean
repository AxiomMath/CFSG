module

public import CFSG.Quasithin.Background.SmithCurtisBasic
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8CuCoord
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8CuWord
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.SpCurtis

open Matrix CFSG.Quasithin.SmithCurtis

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] (ρ : Representation (ZMod 2) G6 V)

abbrev fixU : Submodule (ZMod 2) V := fixSub ρ Ugrp

theorem mem_fixU {x : V} : x ∈ fixU ρ ↔ ∀ u ∈ Ugrp, ρ u x = x := Iff.rfl

theorem add_self_zmod2 (x : V) : x + x = 0 := by
  rw [← two_smul (ZMod 2) x, show (2 : ZMod 2) = 0 from rfl, zero_smul]

theorem act_eq_of_words {l₁ l₂ : List (Bool × Fin 3)}
    (h : IsUpU (toMat (rootBM (l₂.reverse ++ l₁)))) {x : V} (hx : x ∈ fixU ρ) :
    ρ (rootProd l₁) x = ρ (rootProd l₂) x := by
  refine act_eq_of_mem ρ ?_ hx
  rw [rootProd_inv, ← rootProd_append]
  exact rootProd_mem_Ugrp h

@[expose] def Th (s : Fin 3) : V →ₗ[ZMod 2] V := ρ (yE s) + ρ (xE s * yE s)

theorem Th_apply (s : Fin 3) (x : V) : Th ρ s x = ρ (yE s) x + ρ (xE s * yE s) x := rfl

theorem Th_rootProd (s : Fin 3) (l : List (Bool × Fin 3)) (x : V) :
    Th ρ s (ρ (rootProd l) x) =
      ρ (rootProd ((false, s) :: l)) x + ρ (rootProd ((true, s) :: (false, s) :: l)) x := by
  rw [Th_apply, act_mul, act_mul]
  simp only [rootProd, List.foldr_cons, rootE, mul_assoc]

theorem fix_of_Qs {s : Fin 3} {x : V} (hx : x ∈ fixU ρ) {q : G6} (hq : IsQs s (gM q)) :
    ρ q (Th ρ s x) = Th ρ s x := by
  change ρ q (ρ (yE s) x + ρ (xE s * yE s) x) = ρ (yE s) x + ρ (xE s * yE s) x
  rw [map_add, act_mul, act_mul]
  congr 1
  · refine act_eq_of_mem ρ ?_ hx
    rw [yE_inv, mem_Ugrp]
    simpa only [mul_assoc] using (Qs_conj_y hq).1
  · refine act_eq_of_mem ρ ?_ hx
    rw [_root_.mul_inv_rev, yE_inv, xE_inv, mem_Ugrp]
    simpa only [mul_assoc] using (Qs_conj_y (Qs_conj_x hq)).1

theorem Th_mem_fixU (s : Fin 3) {x : V} (hx : x ∈ fixU ρ) : Th ρ s x ∈ fixU ρ := by
  rw [mem_fixU]
  intro u hu
  rcases decomp_up (s := s) (show IsUpU (gM u) from hu) with h | h
  · exact fix_of_Qs ρ hx h
  · have hq := fix_of_Qs ρ hx (q := xE s * u) h
    have e : u = xE s * (xE s * u) := by rw [← mul_assoc, xE_mul_self, one_mul]
    rw [e, ← act_mul, hq]
    change ρ (xE s) (ρ (yE s) x + ρ (xE s * yE s) x) = ρ (yE s) x + ρ (xE s * yE s) x
    rw [map_add, act_mul, act_mul, ← mul_assoc, xE_mul_self, one_mul, add_comm]

@[expose] def evT (l : List (Fin 3)) : V →ₗ[ZMod 2] V :=
  l.foldr (fun s f => Th ρ s ∘ₗ f) LinearMap.id

theorem evT_cons (s : Fin 3) (l : List (Fin 3)) (x : V) :
    evT ρ (s :: l) x = Th ρ s (evT ρ l x) := rfl

theorem evT_append (l l' : List (Fin 3)) (x : V) :
    evT ρ (l ++ l') x = evT ρ l (evT ρ l' x) := by
  induction l with
  | nil => rfl
  | cons s l ih => rw [List.cons_append, evT_cons, evT_cons, ih]

theorem evT_mem_fixU (l : List (Fin 3)) {x : V} (hx : x ∈ fixU ρ) : evT ρ l x ∈ fixU ρ := by
  induction l with
  | nil => exact hx
  | cons s l ih => rw [evT_cons]; exact Th_mem_fixU ρ s ih

@[expose] def tWords : List (Fin 3) → List (List (Bool × Fin 3))
  | [] => [[]]
  | s :: l => (tWords l).flatMap fun w => [(false, s) :: w, (true, s) :: (false, s) :: w]

theorem evT_eq_sum (l : List (Fin 3)) (x : V) :
    evT ρ l x = ((tWords l).map fun w => ρ (rootProd w) x).sum := by
  induction l with
  | nil => simp [evT, tWords, rootProd]
  | cons s l ih =>
    rw [evT_cons, ih, map_list_sum, List.map_map]
    simp only [tWords, List.map_flatMap]
    rw [List.flatMap, List.sum_flatten, List.map_map]
    congr 1
    refine List.map_congr_left fun w _ => ?_
    simp only [Function.comp, Th_rootProd, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, add_zero]

theorem list_sum_eq_range_sum {α W : Type*} [AddCommMonoid W] (F : α → W) (d : α) :
    ∀ M : List α, (M.map F).sum = ∑ i ∈ Finset.range M.length, F (M.getD i d)
  | [] => by simp
  | a :: M => by
    rw [List.map_cons, List.sum_cons, List.length_cons, Finset.sum_range_succ',
      list_sum_eq_range_sum F d M]
    simp [add_comm]

@[expose] def PairingOK (M : List (List (Bool × Fin 3))) (σ : List ℕ) : Prop :=
  ∀ i < M.length, σ.getD i 0 < M.length ∧ σ.getD (σ.getD i 0) 0 = i ∧ σ.getD i 0 ≠ i ∧
    IsUpU (toMat (rootBM ((M.getD (σ.getD i 0) []).reverse ++ M.getD i [])))

instance (M : List (List (Bool × Fin 3))) (σ : List ℕ) : Decidable (PairingOK M σ) := by
  unfold PairingOK
  infer_instance

theorem sum_words_eq_zero {x : V} (hx : x ∈ fixU ρ) {M : List (List (Bool × Fin 3))}
    {σ : List ℕ} (h : PairingOK M σ) : (M.map fun w => ρ (rootProd w) x).sum = 0 := by
  rw [list_sum_eq_range_sum _ [] M]
  refine Finset.sum_involution (fun i _ => σ.getD i 0) ?_ ?_ ?_ ?_
  · intro i hi
    obtain ⟨h1, h2, h3, h4⟩ := h i (Finset.mem_range.mp hi)
    rw [act_eq_of_words ρ h4 hx]
    exact add_self_zmod2 _
  · intro i hi _
    exact (h i (Finset.mem_range.mp hi)).2.2.1
  · intro i hi
    exact Finset.mem_range.mpr (h i (Finset.mem_range.mp hi)).1
  · intro i hi
    exact (h i (Finset.mem_range.mp hi)).2.1

theorem evT_eq_of_pairing {l₁ l₂ : List (Fin 3)} {σ : List ℕ}
    (h : PairingOK (tWords l₁ ++ tWords l₂) σ) {x : V} (hx : x ∈ fixU ρ) :
    evT ρ l₁ x = evT ρ l₂ x := by
  have h0 := sum_words_eq_zero ρ hx h
  rw [List.map_append, List.sum_append] at h0
  rw [evT_eq_sum, evT_eq_sum]
  exact add_right_cancel (h0.trans (add_self_zmod2 _).symm)

theorem pair_idem : ∀ s : Fin 3,
    PairingOK (tWords [s, s] ++ tWords [s]) [1, 0, 5, 4, 3, 2] := by
  decide +kernel

theorem pair_comm :
    PairingOK (tWords [0, 2] ++ tWords [2, 0]) [4, 6, 5, 7, 0, 2, 1, 3] := by
  decide +kernel

theorem pair_braid3 :
    PairingOK (tWords [0, 1, 0] ++ tWords [1, 0, 1])
      [13, 9, 12, 14, 10, 8, 11, 15, 5, 1, 4, 6, 2, 0, 3, 7] := by
  decide +kernel

theorem pair_braid4 :
    PairingOK (tWords [1, 2, 1, 2] ++ tWords [2, 1, 2, 1])
      [16, 18, 17, 25, 29, 21, 28, 30, 27, 19, 26, 24, 22, 20, 23, 31, 0, 2, 1, 9, 13, 5, 12, 14,
       11, 3, 10, 8, 6, 4, 7, 15] := by
  decide +kernel

theorem Th_Th (s : Fin 3) {x : V} (hx : x ∈ fixU ρ) : Th ρ s (Th ρ s x) = Th ρ s x := by
  have h := evT_eq_of_pairing ρ (pair_idem s) hx
  simpa [evT] using h

theorem Th_comm {s t : Fin 3} (hst : s.val + 2 ≤ t.val ∨ t.val + 2 ≤ s.val) {x : V}
    (hx : x ∈ fixU ρ) : Th ρ s (Th ρ t x) = Th ρ t (Th ρ s x) := by
  fin_cases s <;> fin_cases t <;> simp at hst
  · simpa [evT] using evT_eq_of_pairing ρ pair_comm hx
  · simpa [evT] using (evT_eq_of_pairing ρ pair_comm hx).symm

theorem Th_braid3 {x : V} (hx : x ∈ fixU ρ) :
    Th ρ 0 (Th ρ 1 (Th ρ 0 x)) = Th ρ 1 (Th ρ 0 (Th ρ 1 x)) := by
  have h := evT_eq_of_pairing ρ pair_braid3 hx
  simpa [evT] using h

theorem Th_braid4 {x : V} (hx : x ∈ fixU ρ) :
    Th ρ 1 (Th ρ 2 (Th ρ 1 (Th ρ 2 x))) = Th ρ 2 (Th ρ 1 (Th ρ 2 (Th ρ 1 x))) := by
  have h := evT_eq_of_pairing ρ pair_braid4 hx
  simpa [evT] using h

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.SpCurtis
