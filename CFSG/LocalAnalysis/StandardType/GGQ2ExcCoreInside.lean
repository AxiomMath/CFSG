module

public import CFSG.LocalAnalysis.StandardType.GGQ2ExcCoreDefs
public import CFSG.LocalAnalysis.StandardType.GGQ2ExcCoreInsideWit
public import Certificates.Certificate712571
public import Certificates.Certificate712572
public import Certificates.Certificate712573
import CFSG.LocalAnalysis.StandardType.GGQ2ExcCensusInsideCode
import CFSG.LocalAnalysis.StandardType.GGQ2ExcCoreInsideA8
import CFSG.LocalAnalysis.StandardType.GGQ2ExcCoreInsideGe
import CFSG.LocalAnalysis.StandardType.GGQ2ExcCoreInsideSat
import CFSG.LocalAnalysis.StandardType.GGQ2ExcCoreNormLe
import CFSG.LocalAnalysis.StandardType.GGQ2ExcCensusInsideCodeBase
import CFSG.LocalAnalysis.StandardType.GGQ2ExcCensusInsideImg
import CFSG.LocalAnalysis.StandardType.GGQ2ExcCensusInsideList

public section

namespace CFSG.StandardType.GGQ2Frame.ExcPlacement

open CFSG CFSG.Assembly CFSG.StandardType CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus

private theorem not_insideFlag {m : Fin 6} (hm : m = 0 ∨ m = 4) {c : Finset (ExcRaw.Root m)} :
    ¬ ExcRaw.InsideFlag m c := by
  unfold ExcRaw.InsideFlag
  rintro (⟨h | h, -⟩ | ⟨h, -⟩) <;> rcases hm with rfl | rfl <;> exact absurd h (by decide)


theorem excCoreInside_of_insideCensus {m : Fin 6} {τ : Tag}
    (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (hcen : ExcRaw.InsideCensus m)
    (hflag : ∀ {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} {S : LangSetup τ L p}
      {T₀ : Subgroup (ModGL τ L)} {c : Finset (ExcRaw.Root m)}, NegLangTwo S →
      ∀ (d : ExcCoordDatum S T₀ m), ExcRaw.InsideFlag m c →
        ggLinImage (p := 3) d.coord (codeComponent S d.γ c) ≤ ExcRaw.inside m c) :
    ExcCoreInside m τ := by
  intro L _ _ p S hS T₀ d c hc
  refine le_antisymm ?_ (inside_le_ggLinImage_codeComponent hτ hS d c)
  obtain ⟨U, hU⟩ := hc.1
  rcases hcen U c hU with hw | hfl
  · obtain ⟨w⟩ := hw
    obtain ⟨A, a, j, hj⟩ := d.exists_famCharHom_componentRoots_eq hc.1
    refine ggLinImage_codeComponent_le_inside d w (J := {j}) ?_
    ext α
    rw [mem_unionRoots_iff, ← hj]
    simp
  · exact hflag hS d hfl

theorem excCoreInside_F4 : ExcCoreInside 0 .F4 :=
  excCoreInside_of_insideCensus (Or.inl rfl) ExcRaw.insideCensus_F4
    fun _ _ hfl => absurd hfl (not_insideFlag (Or.inl rfl))

theorem excCoreInside_E7 : ExcCoreInside 4 .E7 :=
  excCoreInside_of_insideCensus (Or.inr (Or.inr (Or.inl rfl))) ExcRaw.insideCensus_E7
    fun _ _ hfl => absurd hfl (not_insideFlag (Or.inr rfl))

theorem excCoreInside_E8 : ExcCoreInside 5 .E8 :=
  excCoreInside_of_insideCensus (Or.inr (Or.inr (Or.inr rfl))) ExcRaw.insideCensus_E8
    fun hS d hfl => by
      unfold ExcRaw.InsideFlag at hfl
      rcases hfl with ⟨h | h, -⟩ | ⟨-, ⟨w⟩⟩
      · exact absurd h (by decide)
      · exact absurd h (by decide)
      · exact ggLinImage_codeComponent_le_inside_of_a8 (Or.inr (Or.inr rfl)) hS d w

end CFSG.StandardType.GGQ2Frame.ExcPlacement

end
