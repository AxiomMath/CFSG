module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

public section

namespace CFSG.Monster.B.TwoA

open Module

section Trans

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem exists_linearEquiv_map_eq {S T : Submodule K V} (h : finrank K S = finrank K T) :
    ∃ e : V ≃ₗ[K] V, S.map (e : V →ₗ[K] V) = T := by
  obtain ⟨S', hS'⟩ := Submodule.exists_isCompl S
  obtain ⟨T', hT'⟩ := Submodule.exists_isCompl T
  have h' : finrank K S' = finrank K T' := by
    have h1 := Submodule.finrank_add_eq_of_isCompl hS'
    have h2 := Submodule.finrank_add_eq_of_isCompl hT'
    omega
  let eS : S ≃ₗ[K] T := LinearEquiv.ofFinrankEq S T h
  let eS' : S' ≃ₗ[K] T' := LinearEquiv.ofFinrankEq S' T' h'
  let e : V ≃ₗ[K] V := (Submodule.prodEquivOfIsCompl S S' hS').symm.trans
    ((eS.prodCongr eS').trans (Submodule.prodEquivOfIsCompl T T' hT'))
  have he : ∀ x : S, e x = eS x := by
    intro x
    change Submodule.prodEquivOfIsCompl T T' hT'
      ((eS.prodCongr eS') ((Submodule.prodEquivOfIsCompl S S' hS').symm x)) = _
    rw [Submodule.prodEquivOfIsCompl_symm_apply_left, LinearEquiv.prodCongr_apply,
      Submodule.coe_prodEquivOfIsCompl', map_zero, Submodule.coe_zero, add_zero]
  refine ⟨e, le_antisymm ?_ ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    change e (⟨x, hx⟩ : S) ∈ T
    rw [he]
    exact (eS ⟨x, hx⟩).2
  · intro y hy
    refine ⟨eS.symm ⟨y, hy⟩, (eS.symm ⟨y, hy⟩).2, ?_⟩
    change e (eS.symm ⟨y, hy⟩) = y
    rw [he, LinearEquiv.apply_symm_apply]

end Trans

section Count

variable {K V : Type*} [Field K] [Fintype K] [AddCommGroup V] [Module K V] [Finite V]

abbrev IndepTuple (K V : Type*) [Field K] [AddCommGroup V] [Module K V] (j : ℕ) : Type _ :=
  {s : Fin j → V // LinearIndependent K s}

abbrev SubspaceDim (K V : Type*) [Field K] [AddCommGroup V] [Module K V] (j : ℕ) : Type _ :=
  {S : Submodule K V // finrank K S = j}

omit [Fintype K] [Finite V] in
theorem finrank_span_indep {j : ℕ} (s : IndepTuple K V j) :
    finrank K (Submodule.span K (Set.range s.1)) = j := by
  rw [finrank_span_eq_card s.2, Fintype.card_fin]

@[expose] def spanTuple {j : ℕ} (s : IndepTuple K V j) : SubspaceDim K V j :=
  ⟨Submodule.span K (Set.range s.1), finrank_span_indep s⟩

@[expose] noncomputable def fibreEquiv {j : ℕ} (S : SubspaceDim K V j) :
    {s : IndepTuple K V j // spanTuple s = S} ≃ IndepTuple K S.1 j where
  toFun s := ⟨fun i => ⟨s.1.1 i,
      (congrArg Subtype.val s.2) ▸ (Submodule.subset_span ⟨i, rfl⟩ :
        s.1.1 i ∈ Submodule.span K (Set.range s.1.1))⟩, by
    have h := s.1.2
    exact LinearIndependent.of_comp S.1.subtype h⟩
  invFun t := ⟨⟨S.1.subtype ∘ t.1, t.2.map' S.1.subtype (Submodule.ker_subtype _)⟩, by
    apply Subtype.ext
    change Submodule.span K (Set.range (S.1.subtype ∘ t.1)) = S.1
    refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact (t.1 i).2
    · rw [finrank_span_eq_card (t.2.map' S.1.subtype (Submodule.ker_subtype _)),
        Fintype.card_fin, S.2]⟩
  left_inv s := rfl
  right_inv t := rfl

instance finite_subspaceDim (j : ℕ) : Finite (SubspaceDim K V j) := by
  have : Finite (Submodule K V) :=
    Finite.of_injective (fun S : Submodule K V => (S : Set V)) SetLike.coe_injective
  infer_instance

theorem card_subspaces_mul {j : ℕ} (hj : j ≤ finrank K V) :
    Nat.card (SubspaceDim K V j) * ∏ i : Fin j, (Fintype.card K ^ j - Fintype.card K ^ (i : ℕ)) =
      ∏ i : Fin j, (Fintype.card K ^ finrank K V - Fintype.card K ^ (i : ℕ)) := by
  classical
  have hfib : ∀ S : SubspaceDim K V j, Nat.card {s : IndepTuple K V j // spanTuple s = S} =
      ∏ i : Fin j, (Fintype.card K ^ j - Fintype.card K ^ (i : ℕ)) := by
    intro S
    rw [Nat.card_congr (fibreEquiv S), card_linearIndependent (by rw [S.2]), S.2]
  have : Fintype (SubspaceDim K V j) := Fintype.ofFinite _
  rw [← card_linearIndependent hj,
    ← Nat.card_congr (Equiv.sigmaFiberEquiv (spanTuple (K := K) (V := V) (j := j))),
    Nat.card_sigma]
  simp only [hfib]
  rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.card_eq_fintype_card]

@[expose] def qBinom (q n j : ℕ) : ℕ :=
  (∏ i : Fin j, (q ^ n - q ^ (i : ℕ))) / ∏ i : Fin j, (q ^ j - q ^ (i : ℕ))

theorem prod_pos_of_le {q j : ℕ} (hq : 1 < q) {n : ℕ} (hjn : j ≤ n) :
    0 < ∏ i : Fin j, (q ^ n - q ^ (i : ℕ)) := by
  refine Finset.prod_pos fun i _ => ?_
  have : q ^ (i : ℕ) < q ^ n := Nat.pow_lt_pow_right hq (by omega)
  omega

theorem card_subspaces {j : ℕ} (hj : j ≤ finrank K V) :
    Nat.card (SubspaceDim K V j) = qBinom (Fintype.card K) (finrank K V) j := by
  have h := card_subspaces_mul (K := K) (V := V) hj
  have hpos := prod_pos_of_le (Fintype.one_lt_card (α := K)) (le_refl j)
  rw [qBinom, ← h, Nat.mul_div_cancel _ hpos]

end Count

end CFSG.Monster.B.TwoA
