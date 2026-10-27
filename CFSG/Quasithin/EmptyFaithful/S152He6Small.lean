module

public import CFSG.Quasithin.EmptyFaithful.S152He6CaseB
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGeneralLinearSmall

public section

namespace CFSG.Quasithin.He6

open Polynomial
open scoped MatrixGroups

theorem card_splittingField_zero (p : (ZMod 2)[X]) (hp : p = 0) :
    Nat.card (SplittingField p) ≤ 2 := by
  subst hp
  have hadj := SplittingField.adjoin_rootSet (0 : (ZMod 2)[X])
  rw [rootSet_zero, Algebra.adjoin_empty] at hadj
  have hsurj : Function.Surjective (algebraMap (ZMod 2) (SplittingField (0 : (ZMod 2)[X]))) := by
    intro y
    have hy := (SetLike.ext_iff.1 hadj y).2 Algebra.mem_top
    obtain ⟨x, hx⟩ := Algebra.mem_bot.1 hy
    exact ⟨x, hx⟩
  calc Nat.card (SplittingField (0 : (ZMod 2)[X])) ≤ Nat.card (ZMod 2) :=
        Nat.card_le_card_of_surjective _ hsurj
    _ = 2 := Nat.card_zmod 2

theorem card_galoisField_zero_le : Nat.card (GaloisField 2 0) ≤ 2 :=
  card_splittingField_zero (X ^ 2 ^ 0 - X) (by simp)

theorem psl2_isSolvable_of_card_le_three {F : Type*} [Field F] [Finite F] (hF : Nat.card F ≤ 3) :
    Group.IsSolvable (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) := by
  have h1 : 1 < Nat.card F := Finite.one_lt_card
  have : Group.IsSolvable (Matrix.GeneralLinearGroup (Fin 2) F) :=
    CFSG.ComponentClassification.CatalogueBGeneralLinear.generalLinear_two_small_solvable F
      (by omega)
  have : Group.IsSolvable (Matrix.SpecialLinearGroup (Fin 2) F) :=
    Group.isSolvable_of_isSolvable_injective Matrix.SpecialLinearGroup.toGL_injective
  infer_instance

theorem famPSL_iso {G H : Type} [Group G] [Group H] (e : G ≃* H) (h : FamPSL G) : FamPSL H := by
  rcases h with ⟨f, hf, hf2, ⟨e'⟩⟩ | ⟨p, hp, hp5, ⟨e'⟩⟩
  · exact Or.inl ⟨f, hf, hf2, ⟨e.symm.trans e'⟩⟩
  · exact Or.inr ⟨p, hp, hp5, ⟨e.symm.trans e'⟩⟩

theorem famPSLne7_iso {G H : Type} [Group G] [Group H] (e : G ≃* H) (h : FamPSLne7 G) :
    FamPSLne7 H := by
  rcases h with ⟨f, hf, hf2, ⟨e'⟩⟩ | ⟨p, hp, hp5, hp7, ⟨e'⟩⟩
  · exact Or.inl ⟨f, hf, hf2, ⟨e.symm.trans e'⟩⟩
  · exact Or.inr ⟨p, hp, hp5, hp7, ⟨e.symm.trans e'⟩⟩

theorem famPSL_simple {G : Type} [Group G] (h : FamPSL G) : IsSimpleGroup G := by
  rcases h with ⟨f, -, hf2, ⟨e⟩⟩ | ⟨p, hp, hp5, ⟨e⟩⟩
  · have h4 : 3 < Nat.card (GaloisField 2 f) := by
      rw [GaloisField.card 2 f (by omega)]
      calc 3 < 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
    have : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 f)) :=
      Matrix.ProjectiveSpecialLinearGroup.rank_two_simple h4
    exact e.isSimpleGroup
  · have : Fact p.Prime := ⟨hp⟩
    have h4 : 3 < Nat.card (ZMod p) := by
      rw [Nat.card_zmod]
      omega
    have : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p)) :=
      Matrix.ProjectiveSpecialLinearGroup.rank_two_simple h4
    exact e.isSimpleGroup

theorem famPSLne7_simple {G : Type} [Group G] (h : FamPSLne7 G) : IsSimpleGroup G := by
  rcases h with h | ⟨p, hp, hp5, -, e⟩
  · exact famPSL_simple (Or.inl h)
  · exact famPSL_simple (Or.inr ⟨p, hp, hp5, e⟩)

theorem famPSL_of_perfect {G : Type} [Group G] [Group.IsPerfect G]
    (h : (∃ f : ℕ, Even f ∧ Nonempty (G ≃* PSL(2, GaloisField 2 f))) ∨
      (∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ Nonempty (G ≃* PSL(2, ZMod p)))) : FamPSL G := by
  have hsmall : ∀ (F : Type) [Field F] [Finite F], Nat.card F ≤ 3 → Nonempty (G ≃* PSL(2, F)) →
      False := by
    intro F _ _ hF ⟨e⟩
    have hs : Group.IsSolvable (PSL(2, F)) := psl2_isSolvable_of_card_le_three hF
    have hGs : Group.IsSolvable G :=
      Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
    obtain ⟨x, -, hx1⟩ := exists_involution_psl2 F
    have : Nontrivial G := ⟨⟨e.symm x, 1, fun h => hx1 (e.symm.injective (by simpa using h))⟩⟩
    exact Group.IsPerfect.not_isSolvable G hGs
  rcases h with ⟨f, hfe, ⟨e⟩⟩ | ⟨p, hp, hp2, ⟨e⟩⟩
  · refine Or.inl ⟨f, hfe, ?_, ⟨e⟩⟩
    by_contra hf
    have : f = 0 := by
      obtain ⟨k, hk⟩ := hfe
      omega
    subst this
    exact hsmall (GaloisField 2 0) (by have := card_galoisField_zero_le; omega) ⟨e⟩
  · refine Or.inr ⟨p, hp, ?_, ⟨e⟩⟩
    by_contra hp5
    have : Fact p.Prime := ⟨hp⟩
    have hp4 : p ≠ 4 := by
      rintro rfl
      exact absurd hp (by decide)
    have hp3 : p = 3 := by
      have := hp.two_le
      omega
    subst hp3
    exact hsmall (ZMod 3) (by rw [Nat.card_zmod]) ⟨e⟩

end CFSG.Quasithin.He6
