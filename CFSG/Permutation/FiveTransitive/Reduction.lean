module

public import Mathlib.Data.Fintype.CardEmbedding
public import Mathlib.GroupTheory.GroupAction.MultipleTransitivity

public section

namespace CFSG

namespace FiveTransitive

theorem isMultiplyPretransitive_of_explicit
    (G X : Type*) [Group G] [MulAction G X] (k : ℕ)
    (h : ∀ a b : Fin k → X, Function.Injective a → Function.Injective b →
      ∃ g : G, ∀ i, g • a i = b i) :
    MulAction.IsMultiplyPretransitive G X k := by
  rw [MulAction.isMultiplyPretransitive_iff]
  intro a b
  obtain ⟨g, hg⟩ := h a b a.injective b.injective
  refine ⟨g, Function.Embedding.ext ?_⟩
  exact hg

theorem isMultiplyPretransitive_range_toPermHom
    (G X : Type*) [Group G] [MulAction G X] (k : ℕ)
    (h : MulAction.IsMultiplyPretransitive G X k) :
    MulAction.IsMultiplyPretransitive (MulAction.toPermHom G X).range X k := by
  rw [MulAction.isMultiplyPretransitive_iff] at h ⊢
  intro a b
  obtain ⟨g, hg⟩ := h a b
  refine ⟨⟨MulAction.toPermHom G X g, ⟨g, rfl⟩⟩, ?_⟩
  apply Function.Embedding.ext
  intro i
  have hgi := DFunLike.congr_fun hg i
  simpa [Function.Embedding.smul_apply, Subgroup.smul_def,
    Equiv.Perm.smul_def, MulAction.toPermHom_apply, MulAction.toPerm_apply] using hgi

theorem card_range_toPermHom
    (G X : Type*) [Group G] [Fintype G] [MulAction G X] [FaithfulSMul G X] :
    Nat.card (MulAction.toPermHom G X).range = Fintype.card G := by
  let f := (MulAction.toPermHom G X).rangeRestrict
  have hf : Function.Bijective f :=
    ⟨fun _ _ hab ↦ MulAction.toPerm_injective (β := X) (congr_arg Subtype.val hab),
      (MulAction.toPermHom G X).rangeRestrict_surjective⟩
  simpa [Nat.card_eq_fintype_card] using (Nat.card_eq_of_bijective f hf).symm

theorem descFactorial_dvd_card_of_isMultiplyPretransitive
    (G X : Type*) [Group G] [Finite G] [Fintype X] [MulAction G X] (k : ℕ)
    (hk : k ≤ Fintype.card X)
    (h : MulAction.IsMultiplyPretransitive G X k) :
    (Fintype.card X).descFactorial k ∣ Nat.card G := by
  classical
  let _ : MulAction.IsMultiplyPretransitive G X k := h
  have hecard : 0 < Fintype.card (Fin k ↪ X) := by
    rw [Fintype.card_embedding_eq, Fintype.card_fin]
    exact Nat.descFactorial_pos.mpr hk
  let e : Fin k ↪ X := Classical.choice (Fintype.card_pos_iff.mp hecard)
  have hindex := MulAction.index_stabilizer_of_transitive G e
  have hemb : Nat.card (Fin k ↪ X) = (Fintype.card X).descFactorial k := by
    rw [Nat.card_eq_fintype_card, Fintype.card_embedding_eq, Fintype.card_fin]
  have hcard := (MulAction.stabilizer G e).card_mul_index
  rw [hindex, hemb] at hcard
  refine ⟨Nat.card (MulAction.stabilizer G e), ?_⟩
  simpa [Nat.mul_comm] using hcard.symm

theorem alt_le_perm_card_dichotomy
    (X : Type*) [Fintype X] [DecidableEq X]
    (H : Subgroup (Equiv.Perm X))
    (hcard : 2 ≤ Fintype.card X)
    (hAlt : alternatingGroup X ≤ H) :
    Nat.card H = (Fintype.card X).factorial ∨
      Nat.card H = (Fintype.card X).factorial / 2 := by
  let _ : Nontrivial X :=
    Fintype.one_lt_card_iff_nontrivial.mp (lt_of_lt_of_le one_lt_two hcard)
  have hindex : H.index ∣ 2 := by
    simpa using Subgroup.index_dvd_of_le hAlt
  rcases (Nat.dvd_prime Nat.prime_two).mp hindex with hindex | hindex
  · left
    have htop : H = ⊤ := Subgroup.index_eq_one.mp hindex
    calc
      Nat.card H = Nat.card (Equiv.Perm X) := by simp [htop]
      _ = (Fintype.card X).factorial := by
        simpa [Nat.card_eq_fintype_card] using (Nat.card_perm (α := X))
  · right
    have hperm : Nat.card (Equiv.Perm X) = (Fintype.card X).factorial := by
      simpa [Nat.card_eq_fintype_card] using (Nat.card_perm (α := X))
    have hmul := H.card_mul_index
    rw [hindex, hperm] at hmul
    exact Nat.eq_div_of_mul_eq_right two_ne_zero (by simpa [Nat.mul_comm] using hmul)

end FiveTransitive

end CFSG
