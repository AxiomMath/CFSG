module

public import CFSG.Sporadic.Co1.Module.Pairs
public import CFSG.Sporadic.Co1.Module.CoTwoDataInputs
public import CFSG.Sporadic.Co1.Module.OddProg

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Sporadic.Co1.Module.CoTwo

open CFSG.Blueprint CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1.OddNative
  CFSG.Sporadic.Co1.CoTwoNative Matrix

section Abstract

variable {G X : Type*} [Group G] (act : G → X → X)

@[expose] def orbitSet (H : Subgroup G) (x : X) : Set X := {y | ∃ h ∈ H, act h x = y}

variable {act}

theorem card_step [Finite G] (hmul : ∀ g h x, act (g * h) x = act g (act h x))
    (hone : ∀ x, act 1 x = x) {H K : Subgroup G} (hKH : K ≤ H) {x : X}
    (hK : ∀ g ∈ K, act g x = x) {s : ℕ} (hs : s ≤ (orbitSet act H x).ncard) :
    s * Nat.card K ≤ Nat.card H := by
  let _ : MulAction G X :=
    { smul := act
      one_smul := hone
      mul_smul := hmul }
  have h1 := Pairs.ncard_orbit_mul_card_inf_stabilizer H x
  have h2 : MulAction.orbit H x = orbitSet act H x := by
    ext y
    constructor
    · rintro ⟨⟨h, hh⟩, rfl⟩
      exact ⟨h, hh, rfl⟩
    · rintro ⟨h, hh, rfl⟩
      exact ⟨⟨h, hh⟩, rfl⟩
  rw [h2] at h1
  have h3 : Nat.card K ≤ Nat.card ↥(H ⊓ MulAction.stabilizer G x) :=
    Subgroup.card_le_of_le fun g hg => ⟨hKH hg, (MulAction.mem_stabilizer_iff).2 (hK g hg)⟩
  calc s * Nat.card K ≤ (orbitSet act H x).ncard * Nat.card K := Nat.mul_le_mul_right _ hs
    _ ≤ (orbitSet act H x).ncard * Nat.card ↥(H ⊓ MulAction.stabilizer G x) :=
        Nat.mul_le_mul_left _ h3
    _ = Nat.card H := h1

end Abstract

noncomputable def regsGA :
    List NativeSporadic.Co1 := Odd.runEval [Odd.eA, Odd.eB] progA

noncomputable def regA
    (i : ℕ) : NativeSporadic.Co1 := regsGA.getD i 1

theorem regs_relA : Odd.RegsRel Odd.mat regsGA regsRowsA := by
  refine Odd.runRows_spec Odd.mat progA ?_
  refine ⟨rfl, fun i => ?_⟩
  match i with
  | 0 => exact Odd.mat_eA
  | 1 => exact Odd.mat_eB
  | i + 2 => simp [rowsMatrix_idRows, initRowsA]

section

attribute [local irreducible] regsGA regsRowsA

theorem mat_regA
    (i : ℕ) : Odd.mat (regA i) = rowsMatrix 24 (rrA i) := by
  have h : ∀ j : ℕ, Odd.mat (regsGA.getD j 1) =
      rowsMatrix 24 (regsRowsA[j]?.getD (idRows 24)) :=
    And.right regs_relA
  simpa only [regA, rrA] using h i

noncomputable def regsGS :
    List NativeSporadic.Co1 := Odd.runEval [regA 13, regA 18] progS

noncomputable def regS
    (i : ℕ) : NativeSporadic.Co1 := regsGS.getD i 1

theorem getD_pair_zero {M : Type*} [One M] (a b : M) : [a, b].getD 0 1 = a := rfl

theorem getD_pair_one {M : Type*} [One M] (a b : M) : [a, b].getD 1 1 = b := rfl

theorem getD_pair_add_two {M : Type*} [One M] (a b : M) (i : ℕ) : [a, b].getD (i + 2) 1 = 1 := by
  simp

theorem arr_pair_zero (x y : Array ℕ) : #[x, y][0]?.getD (idRows 24) = x := rfl

theorem arr_pair_one (x y : Array ℕ) : #[x, y][1]?.getD (idRows 24) = y := rfl

theorem arr_pair_add_two (x y : Array ℕ) (i : ℕ) :
    #[x, y][i + 2]?.getD (idRows 24) = idRows 24 := by
  simp

theorem regs_relS : Odd.RegsRel Odd.mat regsGS regsRowsS := by
  refine Odd.runRows_spec Odd.mat progS ?_
  refine ⟨rfl, fun i => ?_⟩
  match i with
  | 0 =>
    rw [getD_pair_zero]
    show Odd.mat (regA 13) = rowsMatrix 24 (#[rrA 13, rrA 18][0]?.getD (idRows 24))
    rw [arr_pair_zero]
    exact mat_regA 13
  | 1 =>
    rw [getD_pair_one]
    show Odd.mat (regA 18) = rowsMatrix 24 (#[rrA 13, rrA 18][1]?.getD (idRows 24))
    rw [arr_pair_one]
    exact mat_regA 18
  | i + 2 =>
    rw [getD_pair_add_two]
    show Odd.mat 1 = rowsMatrix 24 (#[rrA 13, rrA 18][i + 2]?.getD (idRows 24))
    rw [arr_pair_add_two, map_one, rowsMatrix_idRows]

theorem mat_regS
    (i : ℕ) : Odd.mat (regS i) = rowsMatrix 24 (rrS i) := regs_relS.2 i

end

attribute [local irreducible] regsGA regsGS regsRowsA regsRowsS

theorem getD_mem_of_forall_mem {M : Type*} [Group M] {H : Subgroup M} {l : List M}
    (h : ∀ x ∈ l, x ∈ H) (i : ℕ) : l.getD i 1 ∈ H := by
  by_cases hi : i < l.length
  · rw [List.getD_eq_getElem _ _ hi]
    exact h _ (List.getElem_mem hi)
  · rw [List.getD_eq_default _ _ (by omega)]
    exact H.one_mem

theorem runEval_mem {M : Type*} [Group M] (H : Subgroup M) (prog : List (List (ℕ × ℕ))) :
    ∀ init : List M, (∀ x ∈ init, x ∈ H) → ∀ i, (Odd.runEval init prog).getD i 1 ∈ H := by
  induction prog with
  | nil => intro init h i; exact getD_mem_of_forall_mem h i
  | cons fac prog ih =>
    intro init h i
    refine ih (init ++ [Odd.lineEval init fac]) (fun x hx => ?_) i
    rcases List.mem_append.1 hx with hx | hx
    · exact h x hx
    · rw [List.mem_singleton.1 hx]
      unfold Odd.lineEval
      exact Subgroup.list_prod_mem _ fun y hy => by
        obtain ⟨p, -, rfl⟩ := List.mem_map.1 hy
        exact H.pow_mem (getD_mem_of_forall_mem h p.1) _

theorem regS_mem_closure (i : ℕ) :
    regS i ∈ Subgroup.closure ({regA 13, regA 18} : Set NativeSporadic.Co1) := by
  unfold regS regsGS
  refine runEval_mem _ progS [regA 13, regA 18] (fun x hx => ?_) i
  rcases List.mem_cons.1 hx with rfl | hx
  · exact Subgroup.subset_closure (Set.mem_insert _ _)
  · rw [List.mem_singleton.1 hx]
    exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

end CFSG.Sporadic.Co1.Module.CoTwo
