module

public import CFSG.LocalAnalysis.StandardType.GGHalfCentFrame
public import CFSG.Sporadic.Schreier.J4SProfileNode

public section

namespace CFSG.StandardType.GGHalf

open CFSG.StandardType CFSG.StandardType.CoordSL CFSG.RankThree.CALinearPlane Matrix

@[expose] def ones {s : ℕ} (k : Fin s → ℕ) : ℕ :=
  (Finset.univ.filter fun i : Fin s => k i = 1).card

@[expose] noncomputable def zeroBlk {n s r : ℕ}
    (ε : Fin (n + 1) ≃ (Fin (rootPB phi3).dim × Fin s) ⊕ Fin r) (k : Fin s → ℕ) :
    Subgroup (SpecialLinearGroup (Fin (n + 1)) F2) :=
  coordBlockSL F2 (zeroCoords ε fun i => (k i : ZMod 3))

@[expose] noncomputable def classBlk {n s r : ℕ}
    (ε : Fin (n + 1) ≃ (Fin (rootPB phi3).dim × Fin s) ⊕ Fin r) (k : Fin s → ℕ) :
    Subgroup (SpecialLinearGroup (Fin (n + 1)) F2) :=
  (coordBlockSL (AdjoinRoot phi3) (classSet (fun i => (k i : ZMod 3)) 1)).map (theta phi3 ε)

theorem frame_card {n s r : ℕ} (ε : Fin (n + 1) ≃ (Fin (rootPB phi3).dim × Fin s) ⊕ Fin r) :
    n + 1 = 2 * s + r := by
  have h := Fintype.card_congr ε
  simp only [Fintype.card_fin, Fintype.card_sum, Fintype.card_prod] at h
  rw [rootPB_phi3_dim] at h
  omega

theorem ones_le {s : ℕ} (k : Fin s → ℕ) : ones k ≤ s := by
  unfold ones
  calc (Finset.univ.filter fun i : Fin s => k i = 1).card ≤ (Finset.univ : Finset (Fin s)).card :=
        Finset.card_filter_le _ _
    _ = s := by simp

theorem card_classSet {s : ℕ} (k : Fin s → ℕ) (hk : ∀ i, k i = 0 ∨ k i = 1) :
    (classSet (fun i => (k i : ZMod 3)) 1).card = ones k := by
  unfold ones classSet
  congr 1
  refine Finset.filter_congr fun i _ => ?_
  rcases hk i with h | h <;> simp [h]

theorem card_zeroCoords {n s r : ℕ}
    (ε : Fin (n + 1) ≃ (Fin (rootPB phi3).dim × Fin s) ⊕ Fin r) (k : Fin s → ℕ)
    (hk : ∀ i, k i = 0 ∨ k i = 1) :
    (zeroCoords ε fun i => (k i : ZMod 3)).card = n + 1 - 2 * ones k := by
  let β : Fin s → ZMod 3 := fun i => (k i : ZMod 3)
  change (zeroCoords ε β).card = n + 1 - 2 * ones k
  have hcount : (zeroCoords ε β).card =
      (rootPB phi3).dim * (Finset.univ.filter fun i : Fin s => β i = 0).card + r := by
    classical
    let A : Finset (Fin (rootPB phi3).dim × Fin s) :=
      Finset.univ.filter fun ai => β ai.2 = 0
    let t : Finset ((Fin (rootPB phi3).dim × Fin s) ⊕ Fin r) :=
      A.disjSum (Finset.univ : Finset (Fin r))
    have hA : A = (Finset.univ : Finset (Fin (rootPB phi3).dim)) ×ˢ
        (Finset.univ.filter fun i : Fin s => β i = 0) := by
      ext ⟨a, i⟩
      simp [A]
    have hst : ∀ i, i ∈ zeroCoords ε β ↔ ε i ∈ t := by
      intro i
      rcases hi : ε i with ⟨a, j⟩ | k'
      · rw [mem_zeroCoords_inl hi]
        show β j = 0 ↔ Sum.inl (a, j) ∈ t
        simp only [t, Finset.mem_disjSum]
        constructor
        · intro hβ
          exact Or.inl ⟨(a, j), by simpa [A] using hβ, rfl⟩
        · rintro (⟨⟨a', j'⟩, hmem, heq⟩ | ⟨k', _, hk⟩)
          · simp only [Sum.inl.injEq] at heq
            have hj : β j' = 0 := by simpa [A] using hmem
            rw [show j' = j from congrArg Prod.snd heq] at hj
            exact hj
          · exact absurd hk (by simp)
      · rw [iff_true_intro (mem_zeroCoords_inr hi)]
        show True ↔ Sum.inr k' ∈ t
        simp only [t, Finset.mem_disjSum]
        exact ⟨fun _ => Or.inr ⟨k', Finset.mem_univ k', rfl⟩, fun _ => trivial⟩
    have h1 : (zeroCoords ε β).card = t.card := Finset.card_equiv ε hst
    rw [h1]
    dsimp only [t]
    rw [Finset.card_disjSum, hA, Finset.card_product,
      Finset.card_univ, Fintype.card_fin, Finset.card_univ, Fintype.card_fin]
  have hZ : (Finset.univ.filter fun i : Fin s => β i = 0).card = s - ones k := by
    have heq : (Finset.univ.filter fun i : Fin s => ¬ k i = 1) =
        (Finset.univ.filter fun i : Fin s => β i = 0) := by
      refine Finset.filter_congr fun i _ => ?_
      have hβi : β i = (k i : ZMod 3) := rfl
      rw [hβi]
      rcases hk i with h | h <;> rw [h] <;> decide
    have hsum := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin s)))
      (p := fun i => k i = 1)
    rw [show (Finset.univ.filter fun i : Fin s => k i = 1).card = ones k from rfl,
      heq, Finset.card_univ, Fintype.card_fin] at hsum
    have hle := ones_le k
    omega
  have hD1 := frame_card ε
  have hle := ones_le k
  rw [hcount, hZ, rootPB_phi3_dim]
  omega

end CFSG.StandardType.GGHalf

end
