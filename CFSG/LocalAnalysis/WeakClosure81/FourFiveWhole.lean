module

public import CFSG.LocalAnalysis.WeakClosure81.FourFiveComponent
public import CFSG.LocalAnalysis.WeakClosure81.FourFiveAbel
public import CFSG.LocalAnalysis.WeakClosure81.FourFiveNmn
public import CFSG.LocalAnalysis.WeakClosure81.FourFiveHypQuot

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup
open scoped Pointwise

theorem fourFive_minimal_normal_subset {Q : Type} [Group Q] [Finite Q] {j : ℕ} (hj : 1 ≤ j)
    {T R : Subgroup Q} (hT : IsSylowIn 2 T ⊤) (hQ : fourFiveCompFAS j Q T)
    {Ω : Set (Subgroup Q)} (hΩ : E1.IsInvColl ⊤ Ω) [R.Normal]
    (hmin : ∀ M : Subgroup Q, M.Normal → M ≤ R → M = ⊥ ∨ M = R) :
    (R : Set Q) ⊆ (E1.eGen j ⊤ T Ω : Set Q) *
      (Subgroup.normalizer (E1.weakClosure T Ω : Set Q) : Set Q) := by
  by_cases hab : IsMulCommutative R
  · exact fourFive_abelian_subset hj hT hΩ hmin hab
  · have hRbot : R ≠ ⊥ := fun h => hab (h ▸ inferInstance)
    have hN : FourFiveNMN R := ⟨inferInstance, hRbot, hmin, hab⟩
    refine fourFive_nmn_subset hΩ hN fun J hJ => ?_
    obtain ⟨hnorm, hF⟩ := hQ R inferInstance hRbot hmin hab J hJ
    exact fourFive_component_dichotomy hj hT hN hJ hF hΩ

private theorem fourFive_whole_aux {j : ℕ} (hj : 1 ≤ j) :
    ∀ n : ℕ, ∀ (Q : Type) [Group Q] [Finite Q], Nat.card Q = n → ∀ {T : Subgroup Q},
      IsSylowIn 2 T ⊤ → fourFiveQuotCompFAS j Q T → ∀ {Ω : Set (Subgroup Q)},
        E1.IsInvColl ⊤ Ω →
          (E1.eGen j ⊤ T Ω : Set Q) *
            (Subgroup.normalizer (E1.weakClosure T Ω : Set Q) : Set Q) = Set.univ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro Q _ _ hn T hT hQ Ω hΩ
    by_cases hsub : Subsingleton Q
    · refine Set.eq_univ_of_forall fun g => ?_
      refine Set.mem_mul.mpr ⟨1, (E1.eGen j ⊤ T Ω).one_mem, 1,
        (Subgroup.normalizer (E1.weakClosure T Ω : Set Q)).one_mem, ?_⟩
      exact (Subsingleton.elim _ _)
    · haveI : Nontrivial Q := not_subsingleton_iff_nontrivial.mp hsub
      obtain ⟨R, hRn, -, hRbot, hRmin⟩ :=
        CFSG.exists_minimal_normal_le (⊤ : Subgroup Q) inferInstance top_ne_bot
      haveI := hRn
      have hmin : ∀ M : Subgroup Q, M.Normal → M ≤ R → M = ⊥ ∨ M = R := fun M hM hMR => by
        by_cases hMbot : M = ⊥
        · exact Or.inl hMbot
        · exact Or.inr (hRmin M hM hMR hMbot)
      have hRsub := fourFive_minimal_normal_subset hj hT
        (fourFive_compFAS_of_quotCompFAS hQ) hΩ hmin
      have hlt : Nat.card (Q ⧸ R) < n := by
        rw [← hn, Subgroup.card_eq_card_quotient_mul_card_subgroup R]
        have h1 : 1 < Nat.card R := R.one_lt_card_iff_ne_bot.mpr hRbot
        have h2 : 0 < Nat.card (Q ⧸ R) := Nat.card_pos
        nlinarith
      have hbar := ih _ hlt (Q ⧸ R) rfl
        (E1.isSylowIn_two_map_top (QuotientGroup.mk'_surjective R) hT)
        (fourFive_quotCompFAS_quotient R hQ)
        (E1.isInvColl_map_of_surjective (QuotientGroup.mk' R) (QuotientGroup.mk'_surjective R) hΩ)
      exact fourFive_step hT hΩ j hRsub hbar

theorem fourFive_whole {Q : Type} [Group Q] [Finite Q] {j : ℕ} (hj : 1 ≤ j) {T : Subgroup Q}
    (hT : IsSylowIn 2 T ⊤) (hQ : fourFiveQuotCompFAS j Q T) {Ω : Set (Subgroup Q)}
    (hΩ : E1.IsInvColl ⊤ Ω) :
    (E1.eGen j ⊤ T Ω : Set Q) *
      (Subgroup.normalizer (E1.weakClosure T Ω : Set Q) : Set Q) = Set.univ :=
  fourFive_whole_aux hj _ Q rfl hT hQ hΩ

end CFSG.LocalAnalysis.WeakClosure81
