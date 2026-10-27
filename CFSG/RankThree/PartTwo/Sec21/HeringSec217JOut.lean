module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.Sec217ALe

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Blueprint

theorem j217_not_inducesOuterTheta_of_hInn {G : Type} [Group G] [Finite G] {J : Subgroup G} {x : G}
    (hx3 : x ^ 3 = 1)
    (hInn : ∀ σ : MulAut (lBar J), σ ^ 3 = 1 → ∃ k : lBar J, σ = MulAut.conj k) :
    ¬ Sec4.InducesOuterTheta x J := by
  rintro ⟨hx, hnot⟩
  apply hnot
  have hσ3 : (Sec4.thetaQuotMulAut J (Sec4.compAction J ⟨x, hx⟩)) ^ 3 = 1 := by
    rw [← map_pow, ← map_pow]
    have : (⟨x, hx⟩ : Subgroup.normalizer (J : Set G)) ^ 3 = 1 := Subtype.ext (by simpa using hx3)
    rw [this, map_one, map_one]
  obtain ⟨k, hk⟩ := hInn _ hσ3
  exact ⟨k, hk.symm⟩

theorem j217_center_eq_bot_of_perfect_simple {X : Type} [Group X] [IsSimpleGroup X]
    (hX : Group.IsPerfect X) : Subgroup.center X = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h | h
  · exact h
  · exfalso
    have hcomm : ∀ a b : X, a * b = b * a := fun a b =>
      Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b) a
    exact not_subsingleton X
      (subsingleton_of_isPerfect_of_isSolvable hX (Group.isSolvable_of_comm hcomm))

theorem j217_center_eq_bot_of_equiv_simple {X M : Type} [Group X] [Group M] [hM : IsSimpleGroup M]
    (hX : Group.IsPerfect X) (e : X ≃* M) : Subgroup.center X = ⊥ := by
  have : IsSimpleGroup X := @MulEquiv.isSimpleGroup _ _ _ _ hM e
  exact j217_center_eq_bot_of_perfect_simple hX

section Cases

set_option maxRecDepth 20000 in
theorem j217_hInn_J3
    {X : Type} [Group X]
    (hX : Group.IsPerfect X) (e : X ≃* NativeSporadic.J3) :
    ∀ σ : MulAut X, σ ^ 3 = 1 → ∃ k : X, σ = MulAut.conj k := by
  intro σ hσ
  haveI hs : IsSimpleGroup NativeSporadic.J3 := CFSG.Sporadic.J3.isSimpleGroup_J3
  haveI : IsSimpleGroup X := @MulEquiv.isSimpleGroup _ _ _ _ hs e
  have hZ := j217_center_eq_bot_of_perfect_simple hX
  obtain ⟨e'⟩ : Nonempty (X ⧸ Subgroup.center X ≃* NativeSporadic.J3) :=
    ⟨((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).trans e⟩
  have h := CFSG.AGLEmbeddingD2.Wilson.NormalizerAction.inner_of_pow_three_J3 hX e' σ hσ
  exact h

theorem j217_sign_eq_one_of_pow_three {n : ℕ} {π : Equiv.Perm (Fin n)} (hπ : π ^ 3 = 1) :
    Equiv.Perm.sign π = 1 := by
  have h : Equiv.Perm.sign π ^ 3 = 1 := by rw [← map_pow, hπ, map_one]
  rcases Int.units_eq_one_or (Equiv.Perm.sign π) with h1 | h1
  · exact h1
  · rw [h1] at h
    exact absurd h (by decide)

theorem j217_hInn_A9 {X : Type} [Group X] (e : X ≃* alternatingGroup (Fin 9)) :
    ∀ σ : MulAut X, σ ^ 3 = 1 → ∃ k : X, σ = MulAut.conj k := by
  intro σ hσ
  have hσ' : (MulAut.congr e σ) ^ 3 = 1 := by rw [← map_pow, hσ, map_one]
  obtain ⟨π, hπ⟩ := (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 9
    (by norm_num) (by norm_num)).2 (MulAut.congr e σ)
  have hπ3 : π ^ 3 = 1 := by
    apply CFSG.GroupTheory.AutAlternating.conjNormal_injective_alternatingGroup 9 (by norm_num)
    rw [map_pow, hπ, hσ', map_one]
  have hπA : π ∈ alternatingGroup (Fin 9) :=
    Equiv.Perm.mem_alternatingGroup.mpr (j217_sign_eq_one_of_pow_three hπ3)
  refine ⟨e.symm ⟨π, hπA⟩, ?_⟩
  ext x
  apply e.injective
  have h1 : (MulAut.conjNormal π) (e x) = (MulAut.congr e σ) (e x) := by rw [hπ]
  have h2 : (MulAut.congr e σ) (e x) = e (σ x) := by simp [MulAut.congr_apply]
  rw [h2] at h1
  rw [MulAut.conj_apply, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, ← h1]
  apply Subtype.ext
  simp [MulAut.conjNormal_apply]

end Cases

end CFSG.RankThree.PartTwo.Sec21
