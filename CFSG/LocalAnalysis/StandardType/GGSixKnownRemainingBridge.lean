module

public import CFSG.LocalAnalysis.StandardType.GGSixJNotA6KnownDefs
public import CFSG.LocalAnalysis.StandardType.GGSixKnownRemainingDefs
public import CFSG.RankThree.PartOne.S12K.Rigidity
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.LieType.Ree.LargeReeEightTorus
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
public import CFSG.LocalAnalysis.SectionRank.BruhatLift
public import CFSG.LocalAnalysis.SectionRank.ClassicalOdd
public import CFSG.LocalAnalysis.SectionRank.EvenCover.LinearStep
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SLTwo
public import CFSG.LocalAnalysis.SectionRank.LargeReeCover
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Sporadic.Schreier.TitsOther
public import CFSG.Walter.Defs

public section

namespace CFSG.StandardType

open CFSG.Blueprint CFSG.LieType.Universal CFSG.Assembly.LowTwoRank CFSG.RankThree.PartOne.S12K
open CFSG.Open (ordG2 ordTrialityD4 ordSuzuki ordTwistedF4 ordTits)

section KnownLie

theorem subsingleton_ggU_K_of_placeholder (t : StatedLieTag)
    (ht : t = .G2 ∨ t = .trialityD4 ∨ t = .twistedB2 ∨ t = .twistedG2 ∨ t = .twistedF4 ∨
      t = .Tits) (n f : ℕ) : Subsingleton (ggU t n f).K := by
  have h : ggU t n f = trivialUniversal := by
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  rw [h]
  exact Matrix.SpecialLinearGroup.subsingleton_of_subsingleton

theorem false_of_ctxV2_nongenuine (t : StatedLieTag)
    (ht : t = .G2 ∨ t = .trialityD4 ∨ t = .twistedB2 ∨ t = .twistedG2 ∨ t = .twistedF4 ∨
      t = .Tits ∨ t = .POmegaOdd) {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} {n f : ℕ} {ψ : (ggU t n f).K →* G}
    (h : GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ) : False := by
  have hadm := h.2.2.2.1.1
  have hrk := h.2.2.2.1.2
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hrk (show ¬ 2 ≤ 0 by omega)
  · exact absurd hrk (show ¬ 2 ≤ 0 by omega)
  · exact absurd hrk (show ¬ 2 ≤ 0 by omega)
  · exact absurd hrk (show ¬ 2 ≤ 0 by omega)
  · exact absurd hrk (show ¬ 2 ≤ 0 by omega)
  · exact absurd hrk (show ¬ 2 ≤ 0 by omega)
  · exact hadm.2.2.2 rfl

theorem ggSixFieldExtTableCAt_of_nongenuine (t : StatedLieTag)
    (ht : t = .G2 ∨ t = .trialityD4 ∨ t = .twistedB2 ∨ t = .twistedG2 ∨ t = .twistedF4 ∨
      t = .Tits ∨ t = .POmegaOdd) : GGSixFieldExtTableCAt t := by
  intro G _ _ p B Bs x L D J n f ψ hctx
  exact (false_of_ctxV2_nongenuine t ht hctx).elim

theorem ggSixFieldExtTableCInput_of_remaining (h : GGSixFieldExtTableCRemaining) :
    GGSixFieldExtTableCInput := by
  obtain ⟨hPSL, hPSU, hPSp, hPlus, hMinus, hF4, hE6, hE7, hE8, hTw⟩ := h
  have hAll : ∀ t, GGSixFieldExtTableCAt t := by
    intro t
    cases t with
    | PSL => exact hPSL
    | PSU => exact hPSU
    | PSp => exact hPSp
    | POmegaPlus => exact hPlus
    | POmegaMinus => exact hMinus
    | F4 => exact hF4
    | E6 => exact hE6
    | E7 => exact hE7
    | E8 => exact hE8
    | twistedE6 => exact hTw
    | _ => exact ggSixFieldExtTableCAt_of_nongenuine _ (by simp)
  intro G _ _ p B Bs x L D J t
  exact hAll t G p B Bs x L D J

section CardOfLieModel

theorem false_of_lieModel_nongenuine (t : StatedLieTag)
    (ht : t = .G2 ∨ t = .trialityD4 ∨ t = .twistedB2 ∨ t = .twistedG2 ∨ t = .twistedF4 ∨
      t = .Tits ∨ t = .POmegaOdd) {X : Type} [Group X] (n f : ℕ) (ψ : (ggU t n f).K →* X)
    (G₀ : Subgroup X) (hrange : ψ.range = G₀)
    (hLie : LieModel (↥G₀ ⧸ Subgroup.center ↥G₀) t n 2 f) : False := by
  obtain ⟨hadm, hcard⟩ := card_of_lieModel_two hLie
  by_cases hpl : t = .G2 ∨ t = .trialityD4 ∨ t = .twistedB2 ∨ t = .twistedG2 ∨ t = .twistedF4 ∨
      t = .Tits
  · haveI := subsingleton_ggU_K_of_placeholder t hpl n f
    subst hrange
    haveI : Subsingleton ↥ψ.range :=
      (MonoidHom.rangeRestrict_surjective ψ).subsingleton
    haveI : Subsingleton (↥ψ.range ⧸ Subgroup.center ↥ψ.range) :=
      (QuotientGroup.mk_surjective (s := Subgroup.center ↥ψ.range)).subsingleton
    have h1 : Nat.card (↥ψ.range ⧸ Subgroup.center ↥ψ.range) = 1 :=
      Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, ⟨1⟩⟩
    rw [h1] at hcard
    have hf : 1 ≤ f := hadm.2.1
    have hq : 2 ≤ 2 ^ f := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
    have key : ∀ (k : ℕ), k ≠ 0 → (2 ^ f) ^ k ∣ charTwoOrder t n f → False := by
      intro k hk hd
      rw [← hcard] at hd
      have h2 := Nat.eq_one_of_dvd_one hd
      have h3 := Nat.le_self_pow hk (2 ^ f)
      omega
    rcases hpl with rfl | rfl | rfl | rfl | rfl | rfl
    · exact key 6 (by norm_num) (by
        simp only [charTwoOrder, ordG2]
        exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left dvd_rfl _) _)
    · exact key 12 (by norm_num) (by
        simp only [charTwoOrder, ordTrialityD4]
        exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left dvd_rfl _) _) _)
    · exact key 2 (by norm_num) (by
        simp only [charTwoOrder, ordSuzuki]
        exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left dvd_rfl _) _)
    · exact absurd hadm.2.2.2.1 (by norm_num)
    · exact key 12 (by norm_num) (by
        simp only [charTwoOrder, ordTwistedF4]
        exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left
          (dvd_mul_of_dvd_left dvd_rfl _) _) _) _)
    · simp only [charTwoOrder, ordTits] at hcard
      omega
  · have hodd : t = .POmegaOdd := by
      rcases ht with h | h | h | h | h | h | h
      all_goals first | exact h | exact absurd (by simp [h]) hpl
    subst hodd
    exact hadm.2.2.2 rfl

theorem ggSixLieKnown_of_nongenuine (t : StatedLieTag)
    (ht : t = .G2 ∨ t = .trialityD4 ∨ t = .twistedB2 ∨ t = .twistedG2 ∨ t = .twistedF4 ∨
      t = .Tits ∨ t = .POmegaOdd) : GGSixLieKnown t := by
  intro X _ _ n f ψ p G₀ B₁ D J L x hrange _ hLie
  exact (false_of_lieModel_nongenuine t ht n f ψ G₀ hrange hLie).elim

theorem ggSixA6KnownRedAt_of_nongenuine (t : StatedLieTag)
    (ht : t = .G2 ∨ t = .trialityD4 ∨ t = .twistedB2 ∨ t = .twistedG2 ∨ t = .twistedF4 ∨
      t = .Tits ∨ t = .POmegaOdd) : GGSixA6KnownRedAt t := by
  intro X _ _ n f ψ p G₀ B₁ D J L x hrange _ hLie
  exact (false_of_lieModel_nongenuine t ht n f ψ G₀ hrange hLie).elim

theorem ggSixLieKnownTags_of_remaining (h : GGSixLieKnownRemaining) : GGSixLieKnownTags := by
  obtain ⟨hPSL, hPSU, hPSp, hPlus, hMinus, hF4, hE6, hE7, hE8, hTw⟩ := h
  intro t
  cases t with
  | PSL => exact hPSL
  | PSU => exact hPSU
  | PSp => exact hPSp
  | POmegaPlus => exact hPlus
  | POmegaMinus => exact hMinus
  | F4 => exact hF4
  | E6 => exact hE6
  | E7 => exact hE7
  | E8 => exact hE8
  | twistedE6 => exact hTw
  | _ => exact ggSixLieKnown_of_nongenuine _ (by simp)

theorem ggSixA6KnownRed_of_remaining (h : GGSixA6KnownRedRemaining) : GGSixA6KnownRed := by
  obtain ⟨hPSL, hPSU, hPSp, hPlus, hMinus, hF4, hE6, hE7, hE8, hTw⟩ := h
  have hAll : ∀ t, GGSixA6KnownRedAt t := by
    intro t
    cases t with
    | PSL => exact hPSL
    | PSU => exact hPSU
    | PSp => exact hPSp
    | POmegaPlus => exact hPlus
    | POmegaMinus => exact hMinus
    | F4 => exact hF4
    | E6 => exact hE6
    | E7 => exact hE7
    | E8 => exact hE8
    | twistedE6 => exact hTw
    | _ => exact ggSixA6KnownRedAt_of_nongenuine _ (by simp)
  intro X _ _ t
  exact hAll t X

end CardOfLieModel

end KnownLie

end CFSG.StandardType
