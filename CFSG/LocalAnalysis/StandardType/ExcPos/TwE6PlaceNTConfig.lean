module

public import CFSG.LocalAnalysis.StandardType.ExcPos.UnitRAssembly
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeExcTw
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.LocalAnalysis.StandardType.GGInnerDiagMarkingE6TwRankOne
import CFSG.LocalAnalysis.StandardType.GGInnerDiagMpRest

public noncomputable section

namespace CFSG.StandardType.LieKnownR2.ExcPos

open CFSG.Assembly CFSG.Open CFSG.StandardType CFSG.StandardType.GGFinModel
  CFSG.StandardType.LieCore CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.ClassicalPosition
  CFSG.LieType.Universal CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.StandardType.RCKRP
open CFSG.StandardType.ExcFramesHalf (IsToralSubgroup)
open scoped commutatorElement


theorem rckCompCore_of_twE6Pos {X : Type} [Group X] [Finite X] {n f p : ℕ}
    {ψ : (ggU .twistedE6 n f).K →* X} {G₀ B₁ D J L : Subgroup X} {x : X} {A : Subgroup X}
    (hpos : GGSixPosHyp .twistedE6 n f ψ p G₀ B₁ D J L x) (hA : TwE6BigGroup n f p ψ G₀ B₁ A) :
    RCKCompCore .twistedE6 n f ψ p G₀ A B₁ D J L := by
  obtain ⟨hψr, hψk, hLM, hOdd, hp, hp2, -, -, -, hB₁card, hDB, hDcard, hB₁NJ, hB₁CJ, hJc,
    hJodd, hx, hx1, hLG, hLc, hJL, hDnL, -, hB₁NL, hMark2, -, -, hA6, -, -, -⟩ := hpos
  obtain ⟨hB₁A, hAel, hAN, hAinn, hAC, hSC, hrank⟩ := hA
  have hadm : StatedLieAdmissible .twistedE6 n 2 f := CFSG.Blueprint.LieModel.admissible hLM
  have hrk : 2 ≤ (ggU .twistedE6 n f).D.rank := by
    rw [show (ggU .twistedE6 n f).D.rank = 4 from rfl]
    decide
  have hperfU : commutator (ggU .twistedE6 n f).K = ⊤ := (ggU_perfect_lieModel hadm hrk).1
  have hperf : commutator ↥G₀ = ⊤ := by
    rw [← hψr]
    have hsurj : Function.Surjective (MonoidHom.rangeRestrict ψ) :=
      MonoidHom.rangeRestrict_surjective ψ
    have hmap : Subgroup.map (MonoidHom.rangeRestrict ψ) (commutator (ggU .twistedE6 n f).K) =
        commutator ↥ψ.range := by
      rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top_of_surjective _ hsurj,
        commutator_def]
    rw [hperfU, Subgroup.map_top_of_surjective _ hsurj] at hmap
    exact hmap.symm
  have hpres : GGPresentsG0 G₀ (ggU .twistedE6 n f).D .twistedE6 n f ψ :=
    ⟨⟨hadm, hrk⟩, ⟨hψr, hψk⟩, hperf, hLM⟩
  have hMark1 := ggInnerDiagMarkingAt_twistedE6 X n f ψ G₀ hpres
  refine ⟨hpres, hOdd, hp, hp2, hAel, hB₁A, hDB, hDcard, hAN, ?_, hB₁NJ, hB₁CJ, hB₁card, hSC,
    hrank, hAC, hB₁NL, hMark2, ?_, hJodd, hLG, ⟨x, hx, hx1, hLc⟩, hDnL, ?_, hA6⟩
  · exact largeEvenMarking_mono (fun lab R _ I F θ hP a ha => hP a (hAN ha) (hAinn a ha)) hMark1
  · rw [inf_comm]
    exact hJc
  · have hJD : J ≤ Subgroup.centralizer (D : Set X) := hJc.1.trans inf_le_right
    exact hJc.of_le_of_le (le_inf hJL hJD) (inf_le_inf_right _ hLG)

theorem rckBridgeFrame_of_partner {X : Type} [Group X] {f p : ℕ} {G₀ A : Subgroup X}
    (hAel : IsElemAbelian p A) {θ : ↥G₀ →* ModGL (langTag .twistedE6) GGL}
    (hθker : θ.ker = Subgroup.center ↥G₀)
    (hθrange : θ.range = ⁅ggFixGp .twistedE6 f, ggFixGp .twistedE6 f⁆)
    (Θ : ↥A →* ModGL (langTag .twistedE6) GGL) (hΘR : ∀ a : ↥A, Θ a ∈ ggFixGp .twistedE6 f)
    (hpart : ∀ a : ↥A, GGLiePartner G₀ θ (a : X) (Θ a)) (hΘinj : Function.Injective Θ) :
    RCKBridgeFrame .twistedE6 f p G₀ A θ Θ.range := by
  refine ⟨hθker, hθrange, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨a, rfl⟩
    exact hΘR a
  · have h1 : IsElemAbelian p (A.subgroupOf A) := hAel.subgroupOf A
    rw [Subgroup.subgroupOf_self] at h1
    rw [MonoidHom.range_eq_map]
    exact h1.map Θ
  · exact (Nat.card_congr (MonoidHom.ofInjective hΘinj).toEquiv).symm
  · intro d hd
    exact ⟨Θ ⟨d, hd⟩, ⟨⟨d, hd⟩, rfl⟩, hpart ⟨d, hd⟩⟩
  · rintro _ ⟨a, rfl⟩
    exact ⟨(a : X), a.2, hpart a⟩

theorem not_isToralSubgroup_range_of_nt {X : Type} [Group X] {A B₁ : Subgroup X}
    (Θ : ↥A →* ModGL (langTag .twistedE6) GGL)
    (hnt : ¬ NoOffTwE6Three.IsToralE6 GGL ((B₁.subgroupOf A).map Θ)) :
    ¬ IsToralSubgroup (langTag .twistedE6) GGL Θ.range := by
  rintro ⟨g, hg, hT⟩
  exact hnt ⟨g, hg, fun x hx => hT x (Subgroup.map_le_range Θ _ hx)⟩

theorem twE6_caseVData_of_nontoral
    {X : Type} [Group X] [Finite X] {n f p : ℕ} {ψ : (ggU .twistedE6 n f).K →* X}
    {G₀ B₁ D J L : Subgroup X} {x : X} {A : Subgroup X}
    (hpos : GGSixPosHyp .twistedE6 n f ψ p G₀ B₁ D J L x) (hA : TwE6BigGroup n f p ψ G₀ B₁ A)
    {θ : ↥G₀ →* ModGL (langTag .twistedE6) GGL} (hθker : θ.ker = Subgroup.center ↥G₀)
    (hθrange : θ.range = ⁅ggFixGp .twistedE6 f, ggFixGp .twistedE6 f⁆)
    (Θ : ↥A →* ModGL (langTag .twistedE6) GGL) (hΘR : ∀ a : ↥A, Θ a ∈ ggFixGp .twistedE6 f)
    (hpart : ∀ a : ↥A, GGLiePartner G₀ θ (a : X) (Θ a)) (hΘinj : Function.Injective Θ)
    (hnt : ¬ NoOffTwE6Three.IsToralE6 GGL ((B₁.subgroupOf A).map Θ)) :
    RCKCompCore .twistedE6 n f ψ p G₀ A B₁ D J L ∧
      RCKBridgeFrame .twistedE6 f p G₀ A θ Θ.range ∧ RCKExcCaseVData .twistedE6 f p G₀ A B₁ := by
  have hcore := rckCompCore_of_twE6Pos hpos hA
  have hfr := rckBridgeFrame_of_partner hA.2.1 hθker hθrange Θ hΘR hpart hΘinj
  have hfl := rckExcFloorsTwE6_frame hcore hfr
  exact ⟨hcore, hfr, rckExcCaseVData_of_frame (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) hcore hfr
    (not_isToralSubgroup_range_of_nt (B₁ := B₁) Θ hnt) hfl⟩

end CFSG.StandardType.LieKnownR2.ExcPos
