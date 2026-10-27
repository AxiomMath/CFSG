module

public import CFSG.LocalAnalysis.WeakClosure81.FiveTenEnd
public import CFSG.LocalAnalysis.WeakClosure81.FiveTenFinal
public import CFSG.LocalAnalysis.WeakClosure81.FiveTenQuotHyp

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup

theorem fiveTenAt_of_card (n : ℕ) :
    ∀ {G : Type} [Group G] [Finite G] (H M : Subgroup G), Nat.card H = n → FiveTenAt H M := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro G _ _ H M hn T Ω h
    by_cases hJ : kerMOf M H = ⊥
    · rcases fiveTen_step hJ h with hc | ⟨N, T', Ω', hNH, hNh, hΩ'⟩
      · exact hc
      · have hlt : Nat.card N < n := hn ▸ Subgroup.card_lt_of_lt hNH
        exact FiveTenConc.of_le hNH.le hΩ' hJ (ih (Nat.card N) hlt N M rfl T' Ω' hNh)
    · have hlt : Nat.card (⊤ : Subgroup (KerQuot M H)) < n := hn ▸ card_kerQuot_lt hJ
      exact fiveTenConc_of_kerQuot h.invColl
        (ih _ hlt (⊤ : Subgroup (KerQuot M H)) (kerQuotImg M H M) rfl _ _ (fiveTenHyp_kerQuot h))

theorem fiveTenAt_all {G : Type} [Group G] [Finite G] (H M : Subgroup G) : FiveTenAt H M :=
  fiveTenAt_of_card _ H M rfl

variable {G : Type} [Group G] [Finite G]

theorem five_ten {H M T : Subgroup G} {Ω : Set (Subgroup G)} (hΩ : E1.IsInvColl H Ω)
    (hT : IsSylowIn 2 T H) (hN : H ⊓ normalizer (E1.weakClosure T Ω : Set G) ≤ M)
    (hHM : ¬ H ≤ M) :
    ∃ A ∈ Ω, A ≤ T ∧ ∃ H' : Subgroup G, H' ≤ H ∧ A ≤ H' ∧ kerMOf M H ≤ kerMOf M H' ∧
      ¬ A ≤ kerMOf M H' ∧ maxOver ⊤ (kerQuotImg M H' A) = {kerQuotImg M H' M} := by
  have hyp : FiveTenHyp H M T Ω := ⟨hΩ, hT, hN, hHM⟩
  obtain ⟨A, hA, hAT, H', hH'H, hAH', hker, hnot, hmax⟩ :=
    FiveTenConc.exists_le_sylow hΩ hT hyp.le_M (fiveTenAt_all H M T Ω hyp)
  exact ⟨A, hA, hAT, H', hH'H, hAH', hker, hnot, maxOver_kerQuotImg_of_inf hAH' hmax⟩

end CFSG.LocalAnalysis.WeakClosure81
