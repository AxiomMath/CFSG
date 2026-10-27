module

public import CFSG.Sporadic.Co1Block.TwoACent
public import Certificates.Certificate10507

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F10.Co1K

open CFSG.Sporadic.Co1Schreier CFSG.Sporadic.Co1Block
open CFSG.KD.Co1K105 (qElt wordRows qTableOK letterOK co1KLettersCheck t24Codes wordOf)
open CFSG.Sporadic.Co1Schreier.Native (Rows)
open CFSG.Sporadic.SmallF2 (rowsMatrix)

abbrev cA : Subgroup GL24 := GA ⊓ Subgroup.centralizer {aG}

@[expose] def zRows : Rows :=
  CFSG.Sporadic.Co1.CoverNative.eprodRows CFSG.Sporadic.Co1.Cover.epsRows 3

@[expose] def cRows : Rows :=
  Native.mul (Native.pow (Native.mul (Native.mul (Native.mul (CFSG.Sporadic.Co1.Cover.rrCov 0)
    zRows) (Native.inv (CFSG.Sporadic.Co1.Cover.rrCov 0))) iotaARows) 2)
    (CFSG.Sporadic.Co1.Cover.rrCov 0)

@[expose] def qArr : Array Rows := (Array.range 512).map (qElt Native.one iotaARows twoAQRows)

@[expose] def brayL : List Rows := Native.brayElts (Native.brayRows iotaARows twoAD1) twoABray

@[expose] def wsT : List (List Bool) := t24Codes.map fun c => wordOf c.1 c.2

theorem letters_parts :
    Native.mul (CFSG.Sporadic.Co1.Cover.rrCov 0) (Native.inv (CFSG.Sporadic.Co1.Cover.rrCov 0)) =
      Native.one ∧
    Native.mul cRows (Native.inv cRows) = Native.one ∧
    Native.mul (Native.mul cRows zRows) (Native.inv cRows) = iotaARows ∧
    qTableOK Native.one qArr twoAQRows = true ∧
    (∀ i < 11, letterOK Native.one qArr CFSG.KD.Co1K105.L i (Native.mul (Native.mul cRows
      CFSG.Sporadic.Co1.Cover.epsRows[i]!) (Native.inv cRows)) = true) ∧
    (∀ j < 4, letterOK Native.one qArr CFSG.KD.Co1K105.L (11 + j) (Native.mul (Native.mul cRows
      (wordRows Native.one (CFSG.Sporadic.Co1.Cover.rrCov 4) (CFSG.Sporadic.Co1.Cover.rrCov 5)
        (wsT.getD j []))) (Native.inv cRows)) = true) ∧
    letterOK Native.one qArr CFSG.KD.Co1K105.L 15 (Native.mul (Native.mul
      (brayL.getD 0 Native.one) (brayL.getD 7 Native.one)) (brayL.getD 4 Native.one)) = true ∧
    letterOK Native.one qArr CFSG.KD.Co1K105.L 16 (brayL.getD 0 Native.one) = true := by
  have h := (Certificates.certificate10507).1
  simp only [co1KLettersCheck, Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
    List.mem_range] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

theorem qTable_parts (h : qTableOK Native.one qArr twoAQRows = true) :
    (∀ i < 512, CFSG.Sporadic.Co1.InvNative.validRows qArr[i]! = true ∧
      ∀ j < i, qArr[i]! ≠ qArr[j]!) ∧
    ∀ j < 8, qArr[2 ^ j]! = twoAQRows.getD j Native.one := by
  simp only [qTableOK, Bool.and_eq_true, List.all_eq_true, List.mem_range, bne_iff_ne, ne_eq,
    beq_iff_eq] at h
  exact h

theorem qArr_get {i : ℕ} (hi : i < 512) : qArr[i]! = qElt Native.one iotaARows twoAQRows i := by
  have hs : i < qArr.size := by simp [qArr, hi]
  rw [getElem!_pos qArr i hs]
  simp [qArr]

@[expose] def qG (i : ℕ) : GL24 :=
  let x := (List.range 8).foldl (fun x j => if i.testBit j then x * twoAQg j else x) 1
  if i.testBit 8 then x * aG else x

theorem twoAQg_mem {j : ℕ} (hj : j < 8) : twoAQg j ∈ twoAQ := by
  show twoAQg j ∈ Subgroup.closure (twoAQg '' {l | l < twoAQRows.length})
  exact Subgroup.subset_closure ⟨j, by rw [Set.mem_setOf_eq, twoAQRows_length]; exact hj, rfl⟩

theorem rep_qG (i : ℕ) : MRep (qElt Native.one iotaARows twoAQRows i) (qG i) := by
  have key : ∀ l : List ℕ, (∀ j ∈ l, j < 8) → ∀ (R : Rows) (x : GL24), MRep R x →
      MRep (l.foldl (fun x j => if i.testBit j then Native.mul x (twoAQRows.getD j Native.one)
        else x) R) (l.foldl (fun x j => if i.testBit j then x * twoAQg j else x) x) := by
    intro l
    induction l with
    | nil => exact fun _ _ _ h => h
    | cons j l ih =>
      intro hl R x h
      have hstep : MRep (if i.testBit j then Native.mul R (twoAQRows.getD j Native.one) else R)
          (if i.testBit j then x * twoAQg j else x) := by
        split_ifs
        · exact h.mul (qRep_twoA j (by rw [twoAQRows_length]; exact hl j List.mem_cons_self))
        · exact h
      exact ih (fun k hk => hl k (List.mem_cons_of_mem _ hk)) _ _ hstep
  have h0 := key (List.range 8) (fun j hj => List.mem_range.1 hj) _ _ MRep.one
  unfold qElt qG
  dsimp only
  split_ifs
  · exact h0.mul rep_iotaA
  · exact h0

theorem qG_mem (i : ℕ) : qG i ∈ twoAQ := by
  have key : ∀ l : List ℕ, (∀ j ∈ l, j < 8) → ∀ x ∈ twoAQ,
      l.foldl (fun x j => if i.testBit j then x * twoAQg j else x) x ∈ twoAQ := by
    intro l
    induction l with
    | nil => exact fun _ _ h => h
    | cons j l ih =>
      intro hl x hx
      refine ih (fun k hk => hl k (List.mem_cons_of_mem _ hk)) _ ?_
      dsimp only
      split_ifs
      · exact twoAQ.mul_mem hx (twoAQg_mem (hl j List.mem_cons_self))
      · exact hx
  have h0 := key (List.range 8) (fun j hj => List.mem_range.1 hj) 1 twoAQ.one_mem
  unfold qG
  dsimp only
  split_ifs
  · exact twoAQ.mul_mem h0 aG_mem_twoAQ
  · exact h0

theorem qG_inj {i j : ℕ} (hi : i < 512) (hj : j < 512) (h : qG i = qG j) : i = j := by
  obtain ⟨hv, -⟩ := qTable_parts letters_parts.2.2.2.1
  have h1 : rowsMatrix 24 qArr[i]! = ((qG i : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) := by
    rw [qArr_get hi]
    exact rep_qG i
  have h2 : rowsMatrix 24 qArr[j]! = ((qG j : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) := by
    rw [qArr_get hj]
    exact rep_qG j
  have e : qArr[i]! = qArr[j]! :=
    CFSG.Sporadic.Co1.Module.rowsMatrix_injective_of_valid (hv i hi).1 (hv j hj).1
      (by rw [h1, h2, h])
  rcases lt_trichotomy i j with hij | hij | hij
  · exact absurd e.symm ((hv j hj).2 i hij)
  · exact hij
  · exact absurd e ((hv i hi).2 j hij)

theorem qG_two_pow {j : ℕ} (hj : j < 8) : qG (2 ^ j) = twoAQg j := by
  have hlt : 2 ^ j < 512 := lt_of_lt_of_le (Nat.pow_lt_pow_right (by norm_num) hj) (by norm_num)
  have h := (qTable_parts letters_parts.2.2.2.1).2 j hj
  have h1 := rep_qG (2 ^ j)
  rw [← qArr_get hlt, h] at h1
  exact h1.eq (qRep_twoA j (by rw [twoAQRows_length]; exact hj))

@[expose] def eQ : Fin 512 ≃ twoAQ :=
  Equiv.ofBijective (fun i => ⟨qG i, qG_mem i⟩) <| by
    refine Function.Injective.bijective_of_nat_card_le
      (fun i j h => Fin.ext (qG_inj i.2 j.2 (congrArg Subtype.val h))) ?_
    simp [card_twoAQ]

end CFSG.LocalAnalysis.UniquenessCase.UC22.F10.Co1K
