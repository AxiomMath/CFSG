module

public import CFSG.Timmesfeld.Exceptional.DeepMain
public import CFSG.Timmesfeld.Bridge.InductionE
import CFSG.Timmesfeld.Bridge.SchurNarrow
import CFSG.LocalAnalysis.ShultStronglyClosedTI.NoLeastLocalFailure
public import CFSG.Timmesfeld.Bridge.NoPolarConnected
public import CFSG.Timmesfeld.Exceptional.CaseSplit

public section

namespace CFSG.Timmesfeld.Moufang

open CFSG.Blueprint Deep

@[expose] def ExcDiam4InputNJ2 : Prop :=
  ∀ (G : Type) [Group G] (D : Set G), Hyp G D → RootIH G → (∀ d ∈ D, rootSet D d = {d}) →
    (∃ d ∈ D, ∃ c ∈ D, ¬ Commute d c ∧ Odd (orderOf (d * c)) ∧ orderOf (d * c) ≠ 3) →
    ¬ NativeSporadic.IsSporadic G .J2 → NoLevi D → ExcNoPlane D → ExcDiam4 D

@[expose] def ExceptionalNoLeviTO5StepNJ2 : Prop :=
  ∀ (G : Type) [Group G] (D : Set G), Hyp G D → RootIH G → (∀ d ∈ D, rootSet D d = {d}) →
    (∃ d ∈ D, ∃ c ∈ D, ¬ Commute d c ∧ Odd (orderOf (d * c)) ∧ orderOf (d * c) ≠ 3) →
    ¬ NativeSporadic.IsSporadic G .J2 → NoLevi D → ExcNoPlane D → ExcTO5 D

@[expose] def ExceptionalNoPlaneStepNJ2 : Prop :=
  ∀ (G : Type) [Group G] (D : Set G), Hyp G D → RootIH G → (∀ d ∈ D, rootSet D d = {d}) →
    (∃ d ∈ D, ∃ c ∈ D, ¬ Commute d c ∧ Odd (orderOf (d * c)) ∧ orderOf (d * c) ≠ 3) →
    ¬ NativeSporadic.IsSporadic G .J2 → ExcOrderBound D ∧ NoPolar D ∧ ExcNoPlane D

@[expose] def ExceptionalGlobalStepNJ2 : Prop :=
  ∀ (G : Type) [Group G] (D : Set G), Hyp G D → RootIH G → (∀ d ∈ D, rootSet D d = {d}) →
    (∃ d ∈ D, ∃ c ∈ D, ¬ Commute d c ∧ Odd (orderOf (d * c)) ∧ orderOf (d * c) ≠ 3) →
    ¬ NativeSporadic.IsSporadic G .J2 → CommLambda D ∧ LL5 D ∧ NoPolar D

theorem exceptionalNoLeviTO5StepNJ2_of_diam4 (h : ExcDiam4InputNJ2) :
    ExceptionalNoLeviTO5StepNJ2 := by
  intro G _ D hH IH hsing hex hJ hNL hPl
  have := hH.finite
  have hNP := hNL.noPolar hH.isClass hH.root hsing hPl
  exact excTO5_of_diam4 hH.isClass hH.root hNL hNP hPl (p1_of_noPolar_noPlane hH hNP hPl)
    (h G D hH IH hsing hex hJ hNL hPl)

theorem exceptionalNoPlaneStepNJ2_of_cases (hI : ExceptionalLeviStep)
    (hP : ExceptionalNoLeviPlaneStep) (hT : ExceptionalNoLeviTO5StepNJ2) :
    ExceptionalNoPlaneStepNJ2 := by
  intro G _ D h IH hsing hex hJ
  have hNL := hI G D h IH hsing hex
  have hPl := hP G D h IH hsing hex hNL
  exact hNL.residual_of_to5 h hsing hPl (hT G D h IH hsing hex hJ hNL hPl)

theorem exceptionalGlobalStepNJ2_of_noPlane (hI : ExceptionalNoPlaneStepNJ2) :
    ExceptionalGlobalStepNJ2 := by
  intro G _ D h IH hsing hex hJ
  obtain ⟨hOB, hNP, hPl⟩ := hI G D h IH hsing hex hJ
  have hconj : ∀ g : G, ∀ x ∈ D, g * x * g⁻¹ ∈ D := fun g x hx => h.conj_mem g hx
  exact ⟨commLambda_of_noPolar_noPlane h.root hconj hNP hPl,
    ll5_of_orderBound h.root hconj hOB, hNP⟩

@[expose] def ExcThreeNearInput : Prop :=
  ∀ (G : Type) [Group G] (D : Set G), Hyp G D → (∀ d ∈ D, rootSet D d = {d}) → NoLevi D →
    ExcNoPlane D → (∀ d ∈ D, (collinearSet D d).ncard % 3 ≠ 1) →
    ∀ c ∈ D, ∀ p ∈ D, p ∉ nbhd D c 3 → ¬ ThreeNear D c p

@[expose] def ExcCycInput : Prop :=
  ∀ (G : Type) [Group G] (D : Set G), Hyp G D → RootIH G → (∀ d ∈ D, rootSet D d = {d}) →
    (∃ d ∈ D, ∃ c ∈ D, ¬ Commute d c ∧ Odd (orderOf (d * c)) ∧ orderOf (d * c) ≠ 3) →
    ¬ NativeSporadic.IsSporadic G .J2 → NoLevi D → ExcNoPlane D →
    (∀ d ∈ D, (collinearSet D d).ncard % 3 = 1) → ExcDiam4 D

theorem excDiam4InputNJ2_of (hW : ExcThreeNearInput) (hC : ExcCycInput) : ExcDiam4InputNJ2 := by
  intro G _ D hH IH hsing hex hJ hNL hPl
  have := hH.finite
  have hconj : ∀ g : G, ∀ x ∈ D, g * x * g⁻¹ ∈ D := fun g x hx => hH.conj_mem g hx
  have hNP := hNL.noPolar hH.isClass hH.root hsing hPl
  have hP1 := p1_of_noPolar_noPlane hH hNP hPl
  have hQ := commLambda_of_noPolar_noPlane hH.root hconj hNP hPl
  have hconn := Bridge.commConnected_of_noPolar
    (Bridge.asc73Input_of_theoremTwo CFSG.ShultStronglyClosedTI.theoremTwo) hH hNP
  have hconst : ∀ d ∈ D, ∀ e ∈ D, (collinearSet D d).ncard = (collinearSet D e).ncard := by
    intro d hd e he
    obtain ⟨d₀, hD₀⟩ := hH.isClass
    rw [hD₀] at hd he
    obtain ⟨g, rfl⟩ := isConj_iff.1 (hd.symm.trans he)
    exact (ncard_collinearSet_conj hH.isClass g d).symm
  by_cases h1 : ∀ d ∈ D, (collinearSet D d).ncard % 3 = 1
  · exact hC G D hH IH hsing hex hJ hNL hPl h1
  · push Not at h1
    obtain ⟨d, hd, hd1⟩ := h1
    have h3 : ∀ e ∈ D, (collinearSet D e).ncard % 3 ≠ 1 := fun e he => by
      rwa [← hconst d hd e he]
    exact excDiam4_of_noThreeNear hH.isClass hH.root hsing hQ hNL hNP hPl hP1 hconn
      (hW G D hH hsing hNL hPl h3) h3

end CFSG.Timmesfeld.Moufang

namespace CFSG.Timmesfeld.Bridge

open CFSG.Blueprint

theorem outcome_of_stepsSE_NJ2 (hL : LargeStepSE) (hX : Moufang.ExceptionalGlobalStepNJ2)
    (hconn : ∀ (G : Type) [Group G] (D : Set G), Hyp G D → Moufang.NoPolar D →
      Closure.CommConnected D)
    (hA : ARSInput) {G : Type} [Group G] {D : Set G} (h : Hyp G D) : Outcome G := by
  suffices key : ∀ n : ℕ, ∀ (G : Type) [Group G] (D : Set G), Nat.card G = n → Hyp G D →
      Outcome G ∧ ((∃ d ∈ D, ∃ e ∈ rootSet D d, e ≠ d) →
        RootClosure D ∧ SpecialClosure D ∧ RootMoufang D ∧ ExistsCommSpec D) from
    (key _ G D rfl h).1
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro G _ D hn h
    have IH : RootIHStructE G := fun G' _ D' h' hlt => ih _ (hn ▸ hlt) G' D' rfl h'
    refine ⟨?_, hL G D h IH⟩
    by_cases hJ : NativeSporadic.IsSporadic G .J2
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hJ))))))
    · refine outcome_at h (fun hl => ?_)
        (fun hsing hex => hX G D h IH.toStruct.rootIH hsing hex hJ) (hconn G D h) hA
      obtain ⟨hc, hs, hm, _⟩ := hL G D h IH hl
      exact ⟨hc, hs, hm⟩

end CFSG.Timmesfeld.Bridge
