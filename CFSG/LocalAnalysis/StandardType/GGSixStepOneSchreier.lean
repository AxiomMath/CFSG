module

public import CFSG.LocalAnalysis.StandardType.GGSixStepOne
public import CFSG.LocalAnalysis.SeitzReduction.PerfectCentralizer
public import CFSG.LocalAnalysis.ComponentInitial.KProperPumpUpStatement
public import CFSG.Timmesfeld.Final.Simple
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.ClassicalGroups
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.Sporadic.Th.F2Spec

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21
  CFSG.ComponentClassification.OuterAutomorphisms

@[expose] def GGLieSchreierInput : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (t : StatedLieTag) (n f : ℕ), StatedLieAdmissible t n 2 f →
    commutator X = ⊤ → LieModel X t n 2 f → Group.IsSolvable (Outer X)

section Schreier

theorem ggSchreierPerfectInput_of_lieSchreier (hSch : GGLieSchreierInput) :
    GGSchreierPerfectInput := by
  intro G _ _ t n f ψ G₀ hpres hodd K hKN hK
  obtain ⟨⟨hadm, -⟩, -, hperf, hmodel⟩ := hpres
  have hG₀perf : Group.IsPerfect ↥G₀ := Group.isPerfect_def.mpr hperf
  have hXperf : Group.IsPerfect (↥G₀ ⧸ Subgroup.center ↥G₀) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (Subgroup.center ↥G₀))
      (QuotientGroup.mk'_surjective _)
  have hOutX : Group.IsSolvable (Outer (↥G₀ ⧸ Subgroup.center ↥G₀)) :=
    hSch _ t n f hadm (Group.isPerfect_def.mp hXperf) hmodel
  have hOut : Group.IsSolvable (Outer ↥G₀) := solvable_of_centerQuotient ↥G₀
  have hCs : Group.IsSolvable
      (Subgroup.centralizer (G₀ : Set G) ⊓ Subgroup.normalizer (G₀ : Set G) : Subgroup G) :=
    CFSG.Milestones.odd_order_solvable (Odd.of_dvd_nat hodd (Subgroup.card_dvd_of_le inf_le_left))
  exact CFSG.SeitzReduction.perfect_le_of_isSolvable_outer hOut Subgroup.le_normalizer le_rfl hCs
    hK hKN

end Schreier

section Catalogue

theorem ggLieSchreierInput_of_schreierFor
    (h : CFSG.LocalAnalysis.ComponentInitial.SchreierFor InCatalog) : GGLieSchreierInput := by
  intro X _ _ t n f _ hperf hmodel
  have hs : IsSimpleGroup X := CFSG.Timmesfeld.isSimpleGroup_of_lieModel hmodel
  have hnonab : ∃ a b : X, a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    have hbot : commutator X = ⊥ := by
      rw [commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro a _
      rw [Subgroup.mem_centralizer_iff]
      intro b _
      exact hcon b a
    obtain ⟨u, v, huv⟩ := hs.toNontrivial.exists_pair_ne
    have h1 : ∀ w : X, w = 1 := fun w => by
      have : w ∈ commutator X := hperf ▸ Subgroup.mem_top w
      rwa [hbot, Subgroup.mem_bot] at this
    exact huv ((h1 u).trans (h1 v).symm)
  exact h X hnonab (inCatalog_of_lieModel_std X hmodel)

end Catalogue

end CFSG.StandardType
