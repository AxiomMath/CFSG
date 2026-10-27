module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogLargeReeNormalForm
public import CFSG.LieType.Ree.LargeReeModelSchreier
public import CFSG.LocalAnalysis.StandardType.GGTableBOutdiagTriality
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Ree
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open CFSG.ComponentClassification.UnbalancedCatalog
  (large_Ree_full_inner_field_automorphism_normal_form)

theorem ggOutCyclic_of_isCyclic_outer {G : Type*} [Group G] (h : IsCyclic (Outer G)) :
    GGOutCyclic G :=
  ggOutCyclic_of_hom (QuotientGroup.mk' (inner G)) (QuotientGroup.mk'_surjective _)
    (QuotientGroup.ker_mk' _)

section TwF4


theorem ggOutCyclic_twF4 {a : ℕ} (ha : 1 ≤ a) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    GGOutCyclic (LargeEvenCenterQuot (LargeEvenTwF4H a K)) := by
  have : CharP K ReeTag.F4.prime := charP_two_of_card hK
  obtain ⟨-, -, -, hcyc, -⟩ := large_Ree_full_inner_field_automorphism_normal_form a ha K hK
  obtain ⟨e₁⟩ := centerQuot_twF4H_equiv K a
  obtain ⟨E⟩ := ReeTag.nonempty_derivedCentralQuotient_mulEquiv_reeGamma ha hK
  have e₂ : DerivedCentralQuotient (reeFixedGroup Tag.F4 K reeF4Perm
        fun i => if i ∈ reeF4Long then 2 ^ a else 2 ^ (a + 1)) ≃*
      DerivedCentralQuotient (ReeTag.F4.reeGamma K a) := by
    rw [ReeTag.reeGamma_eq_reeFixedGroup]
    exact MulEquiv.refl _
  exact (ggOutCyclic_of_isCyclic_outer hcyc).of_mulEquiv (e₁.trans (e₂.trans E))

theorem largeEvenLabelAll_outdiag_twF4' {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (ht : lab.tag = .twF4) : LargeEvenLabelAll lab fun R _ I _ => GGOutdiagCyclic R I := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨-, hl⟩ := hlab
  dsimp only at ht
  subst ht
  obtain ⟨-, -, h3⟩ := hl
  intro Q hQ
  exact recipeTwF4_and (P := fun R _ I _ => GGOutdiagCyclic R I)
    (fun K _ _ hK => (ggOutCyclic_twF4 (by omega) K hK).ggOutdiagCyclic _) hQ

theorem ggLNoncyclicInput_of_twE6
    (h : ∀ lab, LargeEvenInLambda2 lab → lab.tag = .twE6 →
      LargeEvenLabelAll lab (LargeEvenSimpleGuard fun R _ I _ => GGOutdiagCyclic R I)) :
    GGLNoncyclicInput :=
  ggLNoncyclicInput_of_open fun lab hlab ht => by
    rcases ht with ht | ht
    · exact h lab hlab ht
    · exact (largeEvenLabelAll_outdiag_twF4' hlab ht).mono fun _ _ _ _ hO _ _ => hO

theorem ggLNoncyclicInput_of_twE6Diag (hE6 : GGTwistedE6DiagInput) : GGLNoncyclicInput :=
  ggLNoncyclicInput_of_twE6 fun _ hlab ht => largeEvenLabelAll_outdiag_twE6 hE6 hlab ht

theorem ggTableBInputs_of_twE6
    (h₀ : ∀ lab, LargeEvenInLambda2 lab → lab.tag = .twE6 →
      LargeEvenLabelAll lab (LargeEvenSimpleGuard fun R _ I _ => GGOutdiagCyclic R I))
    (h : ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → LargeEvenInLambda2 lab →
      LargeEvenSplit p lab → LargeEvenLabelAll lab fun R _ I _ =>
        ∃ r, GGTorusLift p r R ∧ GGBstarBound p r R I ∧ GGEndNode p r R I) :
    GGLNoncyclicInput ∧ GGBstarInput ∧ GGStdSubPreInput :=
  ggTableBInputs_of_open (fun lab hlab ht => by
    rcases ht with ht | ht
    · exact h₀ lab hlab ht
    · exact (largeEvenLabelAll_outdiag_twF4' hlab ht).mono fun _ _ _ _ hO _ _ => hO) h

end TwF4

end CFSG.StandardType
