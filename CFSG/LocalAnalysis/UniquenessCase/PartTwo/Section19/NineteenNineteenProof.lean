module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenSeventeen
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.StatementsC
public import CFSG.LocalAnalysis.UniquenessCase.UC6C636a
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf47WCfg

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
  (normalizer_le_normalizer_oUpperTwo)

variable {G : Type} [Group G] [Finite G]

@[expose] def Gap19_19 (D : Data G) : Prop :=
  ∀ (V₀ V : Subgroup G) (p : ℕ) (L A : Subgroup G) (t : G) (B : Subgroup G) (r : ℕ)
    (Y N Dsub H S : Subgroup G) (h : Ctx19_14 D V₀ V p L A t B r Y N Dsub H S),
    R19_17At D V₀ V p L A t B r Y N Dsub H S h → S17.R17_42At D V₀ V →
    ((P19_16_1 D Dsub ∨ P19_16_2 D Dsub ∨ P19_16_3 D Dsub ∨ P19_16_4 D Dsub) →
      S17.oUpperTwo (Opp 2 (Dsub ⊓ D.M)) ≤ IOf D p L →
      A ≤ normalizer ((S17.oUpperTwo (Opp 2 (Dsub ⊓ D.M)) : Subgroup G) : Set G) →
      P19_19 D p L A Dsub (S17.oUpperTwo (Opp 2 (Dsub ⊓ D.M)))) ∧
    (P19_16_5 D Dsub →
      ∀ (d : ℕ) (K J : Fin d → Subgroup G), IsDynkinComponentFamily D Dsub d K J →
        ∀ i : Fin d, J i ≤ IOf D p L → P19_19 D p L A Dsub (J i))

theorem le_normalizer_oUpperTwo_inf (D : Data G) {V₀ V : Subgroup G} {p : ℕ}
    {L A : Subgroup G} {t : G} {B : Subgroup G} {r : ℕ} {Y N Dsub H S : Subgroup G}
    (h : Ctx19_14 D V₀ V p L A t B r Y N Dsub H S)
    (h17 : R19_17At D V₀ V p L A t B r Y N Dsub H S h) :
    A ≤ normalizer ((S17.oUpperTwo (Opp 2 (Dsub ⊓ D.M)) : Subgroup G) : Set G) := by
  have hLcal : L ∈ calC D.M := S17.calLp_subset_calC D p h.ctx.hyp.hL
  have hBM : B ≤ D.M := by
    rw [h.ctx.hB]
    exact (sup_le h.ctx.hA (Subgroup.zpowers_le.mpr h.ctx.htA)).trans
      (IOf_le_M D p hLcal.1.le)
  have hAM : A ≤ D.M := (ctx19_A_le_B h).trans hBM
  have h17' : A ≤ normalizer (Dsub : Set G) := h17
  have hAX : A ≤ normalizer ((Dsub ⊓ D.M : Subgroup G) : Set G) :=
    (le_inf h17' (hAM.trans le_normalizer)).trans inf_normalizer_le_normalizer_inf
  intro a ha
  exact normalizer_le_normalizer_oUpperTwo _
    (CFSG.LocalAnalysis.UniquenessCase.UC6.mem_normalizer_Opp_uc6 (hAX ha) 2)

theorem nineteen_nineteen_of (D : Data G) {V₀ V : Subgroup G} {p : ℕ} {L A : Subgroup G}
    {t : G} {B : Subgroup G} {r : ℕ} {Y N Dsub H S : Subgroup G}
    (h : Ctx19_14 D V₀ V p L A t B r Y N Dsub H S)
    (h17 : R19_17At D V₀ V p L A t B r Y N Dsub H S h) (h42 : S17.R17_42At D V₀ V)
    (hgap : Gap19_19 D) :
    R19_19At D V₀ V p L A t B r Y N Dsub H S h := by
  obtain ⟨h14, h5⟩ := hgap V₀ V p L A t B r Y N Dsub H S h h17 h42
  exact ⟨fun hc hJ => h14 hc hJ (le_normalizer_oUpperTwo_inf D h h17), h5⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19
