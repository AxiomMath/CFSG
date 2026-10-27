module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6UniqueCompLabel
public import CFSG.LocalAnalysis.StandardType.GGExcCompSLMarking
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6Bridge
public import CFSG.LocalAnalysis.StandardType.GGSpJoinNbrModel
import CFSG.LocalAnalysis.StandardType.GGInndiagCommRestE6

public section

namespace CFSG.StandardType.TablePThreeKG

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.AlgebraicGroups CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

private theorem ggTorsion_E6eps_uniqueCompLabel_componentLabel
    {X R : Type} [Group X] [Finite X] [Group R]
    {δ : MulAut X} {J : Subgroup X} {lab : LargeEvenLabel}
    {P : LargeEvenLabel → LargeEvenLabel → Prop}
    (hXc : commutator X = ⊤) (hδ1 : δ ≠ 1) (hδp : δ ^ 3 = 1)
    (hcomp : IsComponentOf J (ggAutFixedSubgroup δ))
    (huniq : ∀ Q' : Subgroup X, IsComponentOf Q' (ggAutFixedSubgroup δ) → Q' = J)
    (θ : X ⧸ Subgroup.center X ≃* R)
    (hβ : ggInducedAut θ δ ∈
      CFSG.ComponentClassification.OuterAutomorphisms.innAutDerived R)
    (hU : UniqueCompLabelAt (P lab) R) :
    ∃ lab' : LargeEvenLabel, LargeEvenInLambda2 lab' ∧
      GGHasLabel lab' (↥J ⧸ Subgroup.center ↥J) ∧ P lab lab' := by
  let δbar : MulAut R := ggInducedAut θ δ
  have hδbar1 : δbar ≠ 1 := by
    intro h
    apply hδ1
    exact ggInducedAut_injective_of_perfect hXc θ (h.trans (map_one _).symm)
  have hδbarp : δbar ^ 3 = 1 := by
    dsimp [δbar]
    rw [← map_pow, hδp, map_one]
  let Jbar : Subgroup R :=
    J.map ((θ : X ⧸ Subgroup.center X →* R).comp (QuotientGroup.mk' (Subgroup.center X)))
  have hJbar : IsComponentOf Jbar (ggAutFixedSubgroup δbar) := by
    dsimp [Jbar, δbar]
    exact ggTorsion_isComponentOf_image θ hcomp
  have hC : CFSG.Open.IsComponentOf Jbar
      (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup δbar) := by
    have hfix : CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup δbar =
        ggAutFixedSubgroup δbar := Subgroup.ext fun _ => Iff.rfl
    rw [hfix]
    exact isComponentOf_iff_open.mp hJbar
  have huniqJbar : ∀ K : Subgroup R,
      CFSG.Open.IsComponentOf K (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup δbar) →
        K = Jbar := by
    intro K hK
    have hK' : IsComponentOf K (ggAutFixedSubgroup δbar) := by
      have hfix : CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup δbar =
          ggAutFixedSubgroup δbar := Subgroup.ext fun _ => Iff.rfl
      exact isComponentOf_iff_open.mpr (by simpa [hfix] using hK)
    obtain ⟨K0, hK0, hK0map⟩ := exists_component_of_induced hXc θ δ hK'
    have hK0J : K0 = J := huniq K0 hK0
    calc K = K0.map ((θ : X ⧸ Subgroup.center X →* R).comp
            (QuotientGroup.mk' (Subgroup.center X))) := hK0map.symm
      _ = J.map ((θ : X ⧸ Subgroup.center X →* R).comp
            (QuotientGroup.mk' (Subgroup.center X))) := by rw [hK0J]
      _ = Jbar := rfl
  obtain ⟨lab', hlab', hhas_bar, hP⟩ := hU δbar hβ hδbarp hδbar1 Jbar hC huniqJbar
  obtain ⟨eJ⟩ := ggTorsion_centerQuot_image_equiv θ hcomp.2.2.1
  have hhas : GGHasLabel lab' (↥J ⧸ Subgroup.center ↥J) := by
    unfold GGHasLabel at hhas_bar ⊢
    refine largeEvenRawDatum_mono (fun R' _ I' F' ⟨ψ⟩ => ?_) hhas_bar
    exact ⟨eJ.trans ψ⟩
  exact ⟨lab', hlab', hhas, hP⟩

theorem ggTorsion_E6eps_uniqueCompLabel
    {Q : LargeEvenLabel → Prop} {P : LargeEvenLabel → LargeEvenLabel → Prop}
    (hQ : ∀ lab, Q lab → lab.tag = .E6 ∨ lab.tag = .twE6)
    (hcat : ∀ lab, Q lab → ∀ (R : Type) [Group R],
      CFSG.Blueprint.ChevalleyExceptionalModel R (markTag lab) 2 lab.n →
        UniqueCompLabelAt (P lab) R)
    {X : Type} [Group X] [Finite X] {δ : MulAut X} {J : Subgroup X}
    (hdat : GGTorsionDatum Q 3 δ J)
    (huniq : ∀ Q' : Subgroup X, IsComponentOf Q' (ggAutFixedSubgroup δ) → Q' = J) :
    LargeEvenMarking X fun lab _ _ _ _ _ =>
      Q lab ∧ ∃ lab' : LargeEvenLabel, LargeEvenInLambda2 lab' ∧
        GGHasLabel lab' (↥J ⧸ Subgroup.center ↥J) ∧ P lab lab' := by
  obtain ⟨hp, hp2, hδp, hδ1, hcomp, hmark⟩ := hdat
  obtain ⟨hXc, lab, hlab, hraw⟩ := hmark
  have hQlab : Q lab :=
    largeEvenRawDatum_elim_const
      (largeEvenRawDatum_mono (fun R _ I F h => h.2.2.elim fun _ hh => hh.1) hraw)
  have htag : lab.tag = .E6 ∨ lab.tag = .twE6 := hQ lab hQlab
  have hrawMM : LargeEvenRawDatumLegacy lab
      (fun R _ I _ => (IsSimpleGroup R ∧ (∃ a b : R, a * b ≠ b * a) ∧
        ∃ θ : X ⧸ Subgroup.center X ≃* R, Q lab ∧
          ggInducedAut θ δ ∈ I) ∧ MarkedModel lab R) :=
    largeEvenRawDatum_markedModel hlab (fun R _ I F h => h.2.1) hraw
  have hinndiag : LargeEvenLabelAll lab (LargeEvenSimpleGuard GGInndiagCommEq) := by
    rcases htag with h | h
    · exact largeEvenLabelAll_inndiagComm_E6 h
    · exact largeEvenLabelAll_inndiagComm_twE6 hlab h
  have hraw' := hinndiag _ hrawMM
  obtain ⟨R, _, I, F, ⟨⟨hs, hna, θ, _, hδI⟩, hm⟩, hGuard⟩ :=
    largeEvenRawDatum_exists hraw'
  have hEq : GGInndiagCommEq R I F := hGuard hs hna
  have hβ : ggInducedAut θ δ ∈
      CFSG.ComponentClassification.OuterAutomorphisms.innAutDerived R := by
    have hmem : ggInducedAut θ δ ∈ ggInndiag R I :=
      Subgroup.mem_sup_right (Subgroup.subset_closure hδI)
    have hmem2 : ggInducedAut θ δ ∈ ggInndiagComm R := by rw [← hEq]; exact hmem
    rwa [ggInndiagComm_eq_innAutDerived] at hmem2
  have ht_mem : markTag lab ∈ CFSG.Blueprint.chevalleyExceptionalTags := by
    rcases htag with h | h <;>
      simp [markTag, CFSG.Blueprint.chevalleyExceptionalTags, h]
  have hchev : CFSG.Blueprint.ChevalleyExceptionalModel R (markTag lab) 2 lab.n := by
    have hm0 : CFSG.Blueprint.LieModel R (markTag lab) (markRank lab) (markChar lab)
        (markDeg lab) := hm
    have h := hm0.chevalleyExceptionalModel ht_mem
    have hchar : markChar lab = 2 := by rcases htag with h | h <;> simp [markChar, h]
    have hdeg : markDeg lab = lab.n := by rcases htag with h | h <;> simp [markDeg, h]
    rw [hchar, hdeg] at h
    exact h
  have hU : UniqueCompLabelAt (P lab) R := hcat lab hQlab R hchev
  obtain ⟨lab', hlab', hhas, hP⟩ :=
    ggTorsion_E6eps_uniqueCompLabel_componentLabel hXc hδ1 hδp hcomp huniq θ hβ hU
  refine ⟨hXc, lab, hlab, largeEvenRawDatum_mono ?_ hraw⟩
  rintro R' _ I' F' ⟨hs', hna', θ', hPlab', _⟩
  exact ⟨hs', hna', θ', hPlab', ⟨lab', hlab', hhas, hP⟩⟩

end CFSG.StandardType.TablePThreeKG
