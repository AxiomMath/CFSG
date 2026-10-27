module

public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.ComponentPrimary.L3SevenModelInputs
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.ComponentPrimary.L3SevenRels

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.ComponentPrimary.L3Seven

open CFSG.RankThree.Native.ONTriple

theorem rowAt_lt : ∀ j < 2, ∀ k < 9, ∀ l < 4, rowAt j k l < 3 := by decide +kernel

@[expose] def progOK : ℕ → List (List (ℕ × Bool)) → Bool
  | _, [] => true
  | n, w :: p => w.all (fun l => decide (l.1 < n)) && progOK (n + 1) p

@[expose] noncomputable def σS (j s a : ℕ) : ℕ := piAt j s (2 * a) / 3

@[expose] noncomputable def σW (j : ℕ) (w : List ℕ) (a : ℕ) : ℕ := w.foldl (fun a s => σS j s a) a

@[expose] def decWordF : ℕ → ℕ → List ℕ
  | 0, _ => []
  | f + 1, n => if n ≤ 1 then [] else n % 2 :: decWordF f (n / 2)

@[expose] def decWord (n : ℕ) : List ℕ := decWordF 16 n

theorem decWordF_lt : ∀ (f n : ℕ), ∀ s ∈ decWordF f n, s < 2
  | 0, _, s, hs => by simp [decWordF] at hs
  | f + 1, n, s, hs => by
    unfold decWordF at hs
    split at hs
    · simp at hs
    · rcases List.mem_cons.1 hs with rfl | hs
      · exact Nat.mod_lt _ (by norm_num)
      · exact decWordF_lt f _ s hs

theorem decWord_lt (n : ℕ) : ∀ s ∈ decWord n, s < 2 := decWordF_lt 16 n

theorem symWd_lt : ∀ j < 2, ∀ s < 2, ∀ l ∈ symWd j s, l.1 < 200 := by decide +kernel

theorem piAt_facts : ∀ j < 2, ∀ s < 2, ∀ a < 12, piAt j s (2 * a) < 36 ∧
    piAt j s (2 * a + 1) < 36 ∧ piAt j s (2 * a) / 3 = piAt j s (2 * a + 1) / 3 ∧
    piAt j s (2 * a) % 3 ≠ piAt j s (2 * a + 1) % 3 := by decide +kernel

theorem relRep_lt : ∀ j < 2, ∀ q < 2, relRepF j q 0 < 12 ∧ relRepF j q 1 < 12 := by
  decide +kernel

theorem rel_facts : relCodes = (List.range 20).map
      (fun r => (List.replicate (relEx r) ((rootW r).map Prod.fst)).flatten) ∧
    ∀ r < 20, ∀ l ∈ rootW r, l.1 < 4 ∧ l.2 = true := by decide +kernel

@[expose] noncomputable def pairCode (j l₁ l₂ m₁ m₂ : ℕ) : ℕ :=
  nthN dPairW (144 * j + 36 * l₁ + 9 * l₂ + 3 * m₁ + m₂)

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
theorem pairW_facts : ∀ j < 2, ∀ l₁ < 4, ∀ l₂ < 4, ∀ m₁ < 3, ∀ m₂ < 3, l₂ ≤ l₁ ∨
    (σW j (decWord (pairCode j l₁ l₂ m₁ m₂ / 2)) (relRepF j (pairCode j l₁ l₂ m₁ m₂ % 2) 0) =
        3 * l₁ + m₁ ∧
      σW j (decWord (pairCode j l₁ l₂ m₁ m₂ / 2)) (relRepF j (pairCode j l₁ l₂ m₁ m₂ % 2) 1) =
        3 * l₂ + m₂) ∨
    (σW j (decWord (pairCode j l₁ l₂ m₁ m₂ / 2)) (relRepF j (pairCode j l₁ l₂ m₁ m₂ % 2) 0) =
        3 * l₂ + m₂ ∧
      σW j (decWord (pairCode j l₁ l₂ m₁ m₂ / 2)) (relRepF j (pairCode j l₁ l₂ m₁ m₂ % 2) 1) =
        3 * l₁ + m₁) := by
  decide +kernel

theorem prog_facts : ∀ j < 2, progOK 4 (inProg j) = true ∧
    (∀ i < 4, inTg j i < 4 + (inProg j).length) ∧ progOK 6 (topProg j) = true ∧
    (∀ i < 8, topTg j i < 6 + (topProg j).length) ∧ topBL j < 4 ∧ topBM j < 3 := by
  decide +kernel

@[expose] noncomputable def inWd (j k : ℕ) : List ℕ := decWord (nthN dInW (9 * j + k))

theorem inW_facts : ∀ j < 2, ∀ k < 9,
    ((σW j (inWd j k) (3 * 0 + rowAt j 0 0) = 3 * 0 + rowAt j k 0 ∧
        σW j (inWd j k) (3 * 1 + rowAt j 0 1) = 3 * 1 + rowAt j k 1) ∨
      (σW j (inWd j k) (3 * 0 + rowAt j 0 0) = 3 * 1 + rowAt j k 1 ∧
        σW j (inWd j k) (3 * 1 + rowAt j 0 1) = 3 * 0 + rowAt j k 0)) ∧
    ((σW j (inWd j k) (3 * 2 + rowAt j 0 2) = 3 * 2 + rowAt j k 2 ∧
        σW j (inWd j k) (3 * 3 + rowAt j 0 3) = 3 * 3 + rowAt j k 3) ∨
      (σW j (inWd j k) (3 * 2 + rowAt j 0 2) = 3 * 3 + rowAt j k 3 ∧
        σW j (inWd j k) (3 * 3 + rowAt j 0 3) = 3 * 2 + rowAt j k 2)) := by decide +kernel

@[expose] noncomputable def topWd (j k l m : ℕ) : List ℕ :=
  decWord (nthN dTopW (108 * j + 12 * k + 3 * l + m))

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
theorem topW_facts : ∀ j < 2, ∀ k < 9, ∀ l < 4, ∀ m < 3, m = rowAt j k l ∨
    (σW j (topWd j k l m) (3 * topBL j + topBM j) = 3 * l + m ∧
    (∃ l' < 4, σW j (topWd j k l m) (3 * 0 + rowAt j 0 0) = 3 * l' + rowAt j k l') ∧
    (∃ l' < 4, σW j (topWd j k l m) (3 * 1 + rowAt j 0 1) = 3 * l' + rowAt j k l')) := by
  decide +kernel

end CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.ComponentPrimary.L3Seven
