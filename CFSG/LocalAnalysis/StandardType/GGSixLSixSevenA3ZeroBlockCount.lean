module

public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordModelSLCompParts
public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordModelSL

public section

open Polynomial Module Matrix

namespace CFSG.StandardType

namespace CoordSL

open Multiplicative

section Count

variable {K : Type} [Field K] {g : K[X]} [Fact (Irreducible g)] {n s r p : ℕ}

theorem card_zeroCoords (ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r) (β : Fin s → ZMod p) :
    (zeroCoords ε β).card =
      (rootPB g).dim * (Finset.univ.filter fun i => β i = 0).card + r := by
  classical
  let A : Finset (Fin (rootPB g).dim × Fin s) :=
    Finset.univ.filter fun ai => β ai.2 = 0
  let t : Finset ((Fin (rootPB g).dim × Fin s) ⊕ Fin r) :=
    A.disjSum (Finset.univ : Finset (Fin r))
  have hA : A = (Finset.univ : Finset (Fin (rootPB g).dim)) ×ˢ
      (Finset.univ.filter fun i : Fin s => β i = 0) := by
    ext ⟨a, i⟩
    simp [A]
  have hst : ∀ i, i ∈ zeroCoords ε β ↔ ε i ∈ t := by
    intro i
    rcases hi : ε i with ⟨a, j⟩ | k
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
      show True ↔ Sum.inr k ∈ t
      simp only [t, Finset.mem_disjSum]
      exact ⟨fun _ => Or.inr ⟨k, Finset.mem_univ k, rfl⟩, fun _ => trivial⟩
  have h1 : (zeroCoords ε β).card = t.card := Finset.card_equiv ε hst
  rw [h1]
  dsimp only [t]
  rw [Finset.card_disjSum, hA, Finset.card_product,
    Finset.card_univ, Fintype.card_fin, Finset.card_univ, Fintype.card_fin]

end Count

section Elementary

variable {G : Type} [Group G] {s p : ℕ}

theorem card_eq_add_two_of_eq_vanishing [Fact p.Prime]
    (ι : Multiplicative (Fin s → ZMod p) →* G) (hι : Function.Injective ι) {D : Subgroup G}
    (hD : D ≤ ι.range) (hcard : Nat.card D = p ^ 2) (Z : Finset (Fin s))
    (hZ : ∀ t : Fin s → ZMod p, ι (ofAdd t) ∈ D → ∀ i ∈ Z, t i = 0)
    (hcent : ∀ t : Fin s → ZMod p, (∀ i ∈ Z, t i = 0) → ι (ofAdd t) ∈ D) :
    s = Z.card + 2 := by
  classical
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  let P : (Fin s → ZMod p) → Prop := fun t => ∀ i ∈ Z, t i = 0
  have hPeq : ∀ t, ι (ofAdd t) ∈ D ↔ P t := fun t => ⟨hZ t, hcent t⟩
  have hf : Function.Bijective
      (fun t : {t : Fin s → ZMod p // ι (ofAdd t) ∈ D} =>
        (⟨ι (ofAdd t.1), t.2⟩ : D)) := by
    constructor
    · rintro ⟨t1, ht1⟩ ⟨t2, ht2⟩ h
      apply Subtype.ext
      have h' : ι (ofAdd t1) = ι (ofAdd t2) := congrArg Subtype.val h
      simpa using congrArg Multiplicative.toAdd (hι h')
    · intro d
      obtain ⟨x, hx⟩ := hD d.2
      refine ⟨⟨x.toAdd, ?_⟩, ?_⟩
      · show ι (ofAdd x.toAdd) ∈ D
        rw [ofAdd_toAdd, hx]; exact d.2
      · apply Subtype.ext
        show ι (ofAdd x.toAdd) = d.1
        rw [ofAdd_toAdd]; exact hx
  have hDcard : Nat.card {t : Fin s → ZMod p // ι (ofAdd t) ∈ D} = p ^ 2 := by
    rw [Nat.card_congr (Equiv.ofBijective _ hf), hcard]
  have eS : {t : Fin s → ZMod p // P t} ≃ ({i : Fin s // i ∉ Z} → ZMod p) :=
    { toFun := fun t i => t.1 i.1
      invFun := fun f => ⟨fun i => if h : i ∈ Z then 0 else f ⟨i, h⟩, by
        intro i hi
        simp [dif_pos hi]⟩
      left_inv := by
        intro t
        ext i
        by_cases h : i ∈ Z
        · simp [dif_pos h, t.2 i h]
        · simp [dif_neg h]
      right_inv := by
        intro f
        ext ⟨i, hi⟩
        simp [dif_neg hi] }
  have hPcard : Nat.card {t : Fin s → ZMod p // P t} = p ^ (s - Z.card) := by
    have hZc : Fintype.card {i : Fin s // i ∈ Z} = Z.card := Fintype.card_coe Z
    rw [Nat.card_eq_fintype_card, Fintype.card_congr eS, Fintype.card_fun, ZMod.card,
      Fintype.card_subtype_compl, Fintype.card_fin, hZc]
  have hp : p ^ (s - Z.card) = p ^ 2 := by
    rw [← hPcard, ← Nat.card_congr (Equiv.subtypeEquivRight hPeq), hDcard]
  have hsub : s - Z.card = 2 := Nat.pow_right_injective (Fact.out : p.Prime).two_le hp
  have hle : Z.card ≤ s := by simpa using Z.card_le_univ
  omega

theorem mem_closure_pair_of_forall_eq_zero [NeZero p]
    (ι : Multiplicative (Fin s → ZMod p) →* G) {i j : Fin s} (hij : i ≠ j)
    (t : Fin s → ZMod p) (ht : ∀ k, k ≠ i → k ≠ j → t k = 0) :
    ι (ofAdd t) ∈ Subgroup.closure
      {ι (ofAdd (Pi.single i 1)), ι (ofAdd (Pi.single j 1))} := by
  have ht' : t = (t i).val • Pi.single i (1 : ZMod p) + (t j).val • Pi.single j (1 : ZMod p) := by
    funext k
    rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply]
    by_cases hki : k = i
    · rw [hki, Pi.single_eq_same, Pi.single_eq_of_ne' (Ne.symm hij), smul_zero, add_zero,
        nsmul_one, ZMod.natCast_zmod_val]
    · by_cases hkj : k = j
      · rw [hkj, Pi.single_eq_of_ne' hij, Pi.single_eq_same, smul_zero, zero_add, nsmul_one,
          ZMod.natCast_zmod_val]
      · rw [Pi.single_eq_of_ne' (fun h => hki h.symm), Pi.single_eq_of_ne' (fun h => hkj h.symm),
          smul_zero, smul_zero, add_zero, ht k hki hkj]
  rw [ht']
  rw [ofAdd_add, ofAdd_nsmul, ofAdd_nsmul, map_mul, map_pow, map_pow]
  have hmi : ι (ofAdd (Pi.single i 1)) ∈ Subgroup.closure
      ({ι (ofAdd (Pi.single i 1)), ι (ofAdd (Pi.single j 1))} : Set G) :=
    Subgroup.subset_closure (by simp)
  have hmj : ι (ofAdd (Pi.single j 1)) ∈ Subgroup.closure
      ({ι (ofAdd (Pi.single i 1)), ι (ofAdd (Pi.single j 1))} : Set G) :=
    Subgroup.subset_closure (by simp)
  exact Subgroup.mul_mem _ (Subgroup.pow_mem _ hmi _) (Subgroup.pow_mem _ hmj _)

end Elementary

end CoordSL

end CFSG.StandardType
