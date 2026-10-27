module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarUnique
public import CFSG.LocalAnalysis.StandardType.GGSixBstarUniqueToralA

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

section Tags

@[expose] def GGSixBstarNoOffenderAt (t : StatedLieTag) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (n f : ℕ) (ψ : (ggU t n f).K →* G),
    GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ →
    Subgroup.centralizer (ggG0 p B x L D J : Set G) = ⊥ → GGNoOffender p (ggM p B x L D J) Bs

theorem ggSixBstarNoOffenderInput_of_tags (h : ∀ t, GGSixBstarNoOffenderAt t) :
    GGSixBstarNoOffenderInput := fun G _ _ p B Bs x L D J t n f ψ hctx hC =>
  h t G p B Bs x L D J n f ψ hctx hC

theorem ggSixBstarNoOffenderAt_of_placeholder (t : StatedLieTag)
    (ht : t = .G2 ∨ t = .trialityD4 ∨ t = .twistedB2 ∨ t = .twistedG2 ∨ t = .twistedF4 ∨
      t = .Tits) : GGSixBstarNoOffenderAt t := by
  intro G _ _ p B Bs x L D J n f ψ hctx
  have hrk := hctx.2.2.2.1.2
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact absurd hrk (show ¬ 2 ≤ 0 by omega)

theorem ggSixBstarNoOffenderAt_POmegaOdd : GGSixBstarNoOffenderAt .POmegaOdd :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ hctx => absurd rfl hctx.2.2.2.1.1.2.2.2

theorem ggSixBstarNoOffenderInput_of_remaining (hPSL : GGSixBstarNoOffenderAt .PSL)
    (hPSU : GGSixBstarNoOffenderAt .PSU) (hPSp : GGSixBstarNoOffenderAt .PSp)
    (hPlus : GGSixBstarNoOffenderAt .POmegaPlus) (hMinus : GGSixBstarNoOffenderAt .POmegaMinus)
    (hF4 : GGSixBstarNoOffenderAt .F4) (hE6 : GGSixBstarNoOffenderAt .E6)
    (hE7 : GGSixBstarNoOffenderAt .E7) (hE8 : GGSixBstarNoOffenderAt .E8)
    (hTwE6 : GGSixBstarNoOffenderAt .twistedE6) : GGSixBstarNoOffenderInput := by
  refine ggSixBstarNoOffenderInput_of_tags fun t => ?_
  cases t with
  | PSL => exact hPSL
  | PSU => exact hPSU
  | PSp => exact hPSp
  | POmegaOdd => exact ggSixBstarNoOffenderAt_POmegaOdd
  | POmegaPlus => exact hPlus
  | POmegaMinus => exact hMinus
  | F4 => exact hF4
  | E6 => exact hE6
  | E7 => exact hE7
  | E8 => exact hE8
  | twistedE6 => exact hTwE6
  | G2 => exact ggSixBstarNoOffenderAt_of_placeholder _ (Or.inl rfl)
  | trialityD4 => exact ggSixBstarNoOffenderAt_of_placeholder _ (Or.inr (Or.inl rfl))
  | twistedB2 => exact ggSixBstarNoOffenderAt_of_placeholder _ (Or.inr (Or.inr (Or.inl rfl)))
  | twistedG2 =>
    exact ggSixBstarNoOffenderAt_of_placeholder _ (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  | twistedF4 =>
    exact ggSixBstarNoOffenderAt_of_placeholder _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  | Tits =>
    exact ggSixBstarNoOffenderAt_of_placeholder _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))

@[expose] def GGRootPlaneAt (t : StatedLieTag) : Prop :=
  GGRootPlaneInputOn fun t' _ _ _ => t' = t

@[expose] def GGPSLNonsplit (t : StatedLieTag) (_n f p : ℕ) : Prop :=
  t = .PSL ∧ ¬ p ∣ 2 ^ f - 1

theorem ggRootPlaneInputOn_notPSLSplit_of_tags (hns : GGRootPlaneInputOn GGPSLNonsplit)
    (h : ∀ t, t ≠ .PSL → GGRootPlaneAt t) :
    GGRootPlaneInputOn fun t n f p => ¬ GGPSLSplit t n f p := by
  intro G _ _ p B Bs x L D J t n f ψ hP hctx s1
  by_cases ht : t = .PSL
  · exact hns G p B Bs x L D J t n f ψ ⟨ht, fun hp => hP ⟨ht, hp⟩⟩ hctx s1
  · exact h t ht G p B Bs x L D J t n f ψ rfl hctx s1

theorem ggRootPlaneAt_of_placeholder (t : StatedLieTag)
    (ht : t = .G2 ∨ t = .trialityD4 ∨ t = .twistedB2 ∨ t = .twistedG2 ∨ t = .twistedF4 ∨
      t = .Tits) : GGRootPlaneAt t := by
  intro G _ _ p B Bs x L D J t' n f ψ ht' hctx
  subst ht'
  have hrk := hctx.2.2.2.1.2
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact absurd hrk (show ¬ 2 ≤ 0 by omega)

theorem ggRootPlaneAt_POmegaOdd : GGRootPlaneAt .POmegaOdd := by
  intro G _ _ p B Bs x L D J t n f ψ ht hctx
  subst ht
  exact absurd rfl hctx.2.2.2.1.1.2.2.2

theorem ggRootPlaneInputOn_notPSLSplit_of_remaining (hns : GGRootPlaneInputOn GGPSLNonsplit)
    (hPSU : GGRootPlaneAt .PSU) (hPSp : GGRootPlaneAt .PSp) (hPlus : GGRootPlaneAt .POmegaPlus)
    (hMinus : GGRootPlaneAt .POmegaMinus) (hF4 : GGRootPlaneAt .F4) (hE6 : GGRootPlaneAt .E6)
    (hE7 : GGRootPlaneAt .E7) (hE8 : GGRootPlaneAt .E8) (hTwE6 : GGRootPlaneAt .twistedE6) :
    GGRootPlaneInputOn fun t n f p => ¬ GGPSLSplit t n f p := by
  refine ggRootPlaneInputOn_notPSLSplit_of_tags hns fun t ht => ?_
  cases t with
  | PSL => exact absurd rfl ht
  | PSU => exact hPSU
  | PSp => exact hPSp
  | POmegaOdd => exact ggRootPlaneAt_POmegaOdd
  | POmegaPlus => exact hPlus
  | POmegaMinus => exact hMinus
  | F4 => exact hF4
  | E6 => exact hE6
  | E7 => exact hE7
  | E8 => exact hE8
  | twistedE6 => exact hTwE6
  | G2 => exact ggRootPlaneAt_of_placeholder _ (Or.inl rfl)
  | trialityD4 => exact ggRootPlaneAt_of_placeholder _ (Or.inr (Or.inl rfl))
  | twistedB2 => exact ggRootPlaneAt_of_placeholder _ (Or.inr (Or.inr (Or.inl rfl)))
  | twistedG2 => exact ggRootPlaneAt_of_placeholder _ (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  | twistedF4 =>
    exact ggRootPlaneAt_of_placeholder _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  | Tits => exact ggRootPlaneAt_of_placeholder _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))

end Tags

end CFSG.StandardType
