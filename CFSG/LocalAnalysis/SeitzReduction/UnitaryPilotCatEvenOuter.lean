module

public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotCatTypeDet
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotCatCovers
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotCatStatement
public import CFSG.Sporadic.Schreier.TitsInner

public section

namespace CFSG.SeitzReduction.UnitaryPilot

open CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.SeitzReduction.F4Pilot (FixedCentralizerTwoFree)

theorem sumTypeDet_of_simple {m : ℕ} (hdet : SUmEvenTypeDetAt m) {D : Type} [Group D]
    (hq : IsQuasisimple D) (hs : IsSimpleGroup D) {f : ℕ}
    (hDm : LieModel (D ⧸ center D) .PSU m 2 f) {t : StatedLieTag} {n f' : ℕ}
    (hadm : StatedLieAdmissible t n 2 f') (hD : LieModel D t n 2 f') :
    t = .PSU ∧ n = m ∧ f' = f :=
  hdet (D ⧸ center D) f t n f' hDm hadm
    (LinearPilot.lieModel_quotient_center_of_center_eq_bot
      (F4Pilot.center_eq_bot_of_isQuasisimple hq hs) hD)

@[expose] def CatSUmEvenOuterFamilyAt (τ : StatedLieTag) (m : ℕ) : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    ∀ n e : ℕ, StatedLieAdmissible τ n 2 e → LieModel S τ n 2 e →
    ∀ σ : MulAut S, orderOf σ = 2 → σ ∉ (MulAut.conj : S →* MulAut S).range →
    ∀ (f : ℕ) (D : Subgroup (fixedSubgroup σ)), IsComponent D →
      LieModel (D ⧸ center D) .PSU m 2 f → FixedCentralizerTwoFree σ D →
        LieModel S .PSL m 2 (2 * f)

theorem catSUmEvenOuterAt_of_families {m : ℕ} (h : ∀ τ, CatSUmEvenOuterFamilyAt τ m) :
    CatSUmEvenOuterAt m := by
  intro S _ _ hS hna heven σ hσ hout f D hD hDm hodd
  obtain ⟨τ, n, e, hadm, hmS⟩ := heven
  exact h τ S hS hna n e hadm hmS σ hσ hout f D hD hDm hodd

theorem catSUmEvenOuterFamily_of_not_admissible {τ : StatedLieTag}
    (hτ : ∀ n e : ℕ, ¬ StatedLieAdmissible τ n 2 e) (m : ℕ) : CatSUmEvenOuterFamilyAt τ m :=
  fun _ _ _ _ _ n e hadm => absurd hadm (hτ n e)

theorem catSUmEvenOuterFamily_POmegaOdd (m : ℕ) : CatSUmEvenOuterFamilyAt .POmegaOdd m :=
  catSUmEvenOuterFamily_of_not_admissible (τ := .POmegaOdd) (fun _ _ hadm => hadm.2.2.2 rfl) m

theorem catSUmEvenOuterFamily_twistedG2 (m : ℕ) : CatSUmEvenOuterFamilyAt .twistedG2 m :=
  catSUmEvenOuterFamily_of_not_admissible (τ := .twistedG2)
    (fun _ _ hadm => absurd hadm.2.2.2.1 (by norm_num)) m

theorem catSUmEvenOuterFamily_of_involutions_inner {τ : StatedLieTag}
    (hτ : ∀ (K : Type) [Group K] (n e : ℕ), StatedLieAdmissible τ n 2 e → LieModel K τ n 2 e →
      ∀ α : MulAut K, α ^ 2 = 1 → α ∈ (MulAut.conj : K →* MulAut K).range) (m : ℕ) :
    CatSUmEvenOuterFamilyAt τ m := by
  intro S _ _ _ _ n e hadm hmS σ hσ hout
  exact absurd (hτ S n e hadm hmS σ (hσ ▸ pow_orderOf_eq_one σ)) hout

section SuzukiReeTits


theorem catSUmEvenOuterFamily_twistedB2 (m : ℕ) : CatSUmEvenOuterFamilyAt .twistedB2 m := by
  refine catSUmEvenOuterFamily_of_involutions_inner (τ := .twistedB2) (fun K _ n e _ hmK => ?_) m
  refine Sporadic.Schreier.Tits.CLS_Suzuki_large_Ree_Tits_involutions_inner K e (Or.inl ?_)
  rcases hmK with ⟨ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, -, h⟩
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)
  · exact h

theorem catSUmEvenOuterFamily_twistedF4 (m : ℕ) : CatSUmEvenOuterFamilyAt .twistedF4 m := by
  refine catSUmEvenOuterFamily_of_involutions_inner (τ := .twistedF4) (fun K _ n e _ hmK => ?_) m
  refine Sporadic.Schreier.Tits.CLS_Suzuki_large_Ree_Tits_involutions_inner K e
    (Or.inr (Or.inl ?_))
  rcases hmK with ⟨ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, -, h⟩ | ⟨-, ht, -⟩
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)
  · exact h
  · exact absurd ht (by decide)

theorem catSUmEvenOuterFamily_Tits (m : ℕ) : CatSUmEvenOuterFamilyAt .Tits m := by
  refine catSUmEvenOuterFamily_of_involutions_inner (τ := .Tits) (fun K _ n e hadm hmK => ?_) m
  obtain rfl : e = 1 := hadm.2.2.2.2
  refine Sporadic.Schreier.Tits.CLS_Suzuki_large_Ree_Tits_involutions_inner K 1
    (Or.inr (Or.inr ?_))
  rcases hmK with ⟨ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, -, h⟩ | ⟨-, ht, -⟩
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)
  · exact h
  · exact absurd ht (by decide)

theorem catSUmEvenOuterAt_of_open_families {m : ℕ} (hPSL : CatSUmEvenOuterFamilyAt .PSL m)
    (hPSU : CatSUmEvenOuterFamilyAt .PSU m) (hPSp : CatSUmEvenOuterFamilyAt .PSp m)
    (hOp : CatSUmEvenOuterFamilyAt .POmegaPlus m) (hOm : CatSUmEvenOuterFamilyAt .POmegaMinus m)
    (hG2 : CatSUmEvenOuterFamilyAt .G2 m) (hF4 : CatSUmEvenOuterFamilyAt .F4 m)
    (hE6 : CatSUmEvenOuterFamilyAt .E6 m) (hE7 : CatSUmEvenOuterFamilyAt .E7 m)
    (hE8 : CatSUmEvenOuterFamilyAt .E8 m) (h2E6 : CatSUmEvenOuterFamilyAt .twistedE6 m)
    (h3D4 : CatSUmEvenOuterFamilyAt .trialityD4 m) : CatSUmEvenOuterAt m := by
  apply catSUmEvenOuterAt_of_families
  intro τ
  cases τ
  · exact hPSL
  · exact hPSU
  · exact hPSp
  · exact catSUmEvenOuterFamily_POmegaOdd m
  · exact hOp
  · exact hOm
  · exact hG2
  · exact hF4
  · exact hE6
  · exact hE7
  · exact hE8
  · exact h2E6
  · exact h3D4
  · exact catSUmEvenOuterFamily_twistedB2 m
  · exact catSUmEvenOuterFamily_twistedG2 m
  · exact catSUmEvenOuterFamily_twistedF4 m
  · exact catSUmEvenOuterFamily_Tits m

end SuzukiReeTits

end CFSG.SeitzReduction.UnitaryPilot
