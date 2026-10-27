module

public import CFSG.LocalAnalysis.StandardType.GGOppositeRadicalExcOpp
public import CFSG.LocalAnalysis.StandardType.GGOppositeRadicalPSL
public import CFSG.LieType.Steinberg.Adjoint.Perfect
public import CFSG.LieType.CurtisTits.ExceptionalQuasisimple
public import CFSG.LieType.CurtisTits.Recognition
public import CFSG.LieType.Steinberg.Isogeny.E6
public import CFSG.LieType.Steinberg.Isogeny.E7
public import CFSG.LieType.HighestRoot.ModelCenter
public import CFSG.LieType.Chevalley.AdjointCenter
public import CFSG.ClassicalInvolution.Q3.ModelCenter
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoOddLieDefs
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoStandardDefs

public section

namespace CFSG.StandardType

open CFSG.Open CFSG.LieType.BorelTits CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal

namespace GGOppRadExc

theorem isSimpleGroup_of_isQuasisimple {G : Type*} [Group G] (hq : CFSG.IsQuasisimple G)
    (hZ : Subgroup.center G = ⊥) : IsSimpleGroup G := by
  have : Nontrivial (G ⧸ Subgroup.center G) := hq.2.1.toNontrivial
  have : Nontrivial G := (QuotientGroup.mk'_surjective (Subgroup.center G)).nontrivial
  refine ⟨fun N hN => ?_⟩
  rcases CFSG.LieType.CurtisTits.le_center_or_eq_top_of_isQuasisimple hq N with h | h
  · exact Or.inl (le_bot_iff.mp (hZ ▸ h))
  · exact Or.inr h

variable {τ : Tag} {K : Type} [Field K]

theorem ggOppRadGood_of_surjective [Finite K] [CharP K 2] {U : Type*} [Group U] [Finite U]
    (hU : CFSG.IsQuasisimple U) (hZ : ∀ z ∈ Subgroup.center U, z ^ 2 = 1 → z = 1)
    (φ : U →* ↥(adjointGroup τ K)) (hφ : Function.Surjective φ) (hφ1 : ∃ u, φ u ≠ 1)
    {Q : Subgroup U} (hQne : Q ≠ ⊥) (hQ : GGRadicalTwo ⊤ Q) : GGOppRadGood ⊤ Q := by
  have := finite_modGL (τ := τ) (K := K)
  have hC : IsSimpleGroup ↥(adjointGroup τ K) := isSimpleGroup_of_isQuasisimple
    (CFSG.LieType.CurtisTits.isQuasisimple_of_surjective hU hφ hφ1) center_adjointGroup_eq_bot
  set ψ : U →* ModGL τ K := (adjointGroup τ K).subtype.comp φ with hψ
  have hrange : ψ.range = adjointGroup τ K := by
    rw [hψ, MonoidHom.range_comp, (MonoidHom.range_eq_top).mpr hφ, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  have hkerφ : φ.ker ≤ Subgroup.center U :=
    CFSG.LieType.CurtisTits.ker_le_center_of_isQuasisimple hU hφ1
  have hker : ψ.ker ≤ Subgroup.center U := fun z hz => hkerφ (by
    rw [MonoidHom.mem_ker] at hz ⊢
    exact Subtype.ext hz)
  have hinv : ∀ z ∈ ψ.ker, z ^ 2 = 1 → z = 1 := fun z hz h2 => hZ z (hker hz) h2
  have hperf : commutator U = ⊤ := hU.1.commutator_eq_top
  refine GGOppRad.GGOppRadGood.of_map_perfect ψ hperf hker hinv hQ ?_
  have hrad := GGOppRad.radicalTwo_map ψ hker hinv hQ
  rw [hrange] at hrad ⊢
  refine ggOppRadGood_adjointGroup ?_ hrad
  intro hbot
  apply hQne
  have hc := GGOppRad.card_map_eq ψ hinv hQ.isPGroup
  rw [hbot, Subgroup.card_bot] at hc
  exact Subgroup.eq_bot_of_card_eq Q hc.symm

theorem universal_conclusion_adjointGroup [Finite K] [CharP K 2]
    (hq : CFSG.IsQuasisimple ↥(adjointGroup τ K)) :
    Finite ↥(adjointGroup τ K) ∧
      (∀ z ∈ Subgroup.center ↥(adjointGroup τ K), z ^ 2 = 1 → z = 1) ∧
      ∀ Q : Subgroup ↥(adjointGroup τ K), Q ≠ ⊥ → GGRadicalTwo ⊤ Q → GGOppRadGood ⊤ Q := by
  have := finite_modGL (τ := τ) (K := K)
  have hZ : ∀ z ∈ Subgroup.center ↥(adjointGroup τ K), z ^ 2 = 1 → z = 1 := fun z hz _ => by
    rw [center_adjointGroup_eq_bot, Subgroup.mem_bot] at hz
    exact hz
  refine ⟨inferInstance, hZ, fun Q hQne hQ => ?_⟩
  obtain ⟨u, hu⟩ : ∃ u : ↥(adjointGroup τ K), u ≠ 1 := by
    have : Nontrivial (↥(adjointGroup τ K) ⧸ Subgroup.center ↥(adjointGroup τ K)) :=
      hq.2.1.toNontrivial
    have : Nontrivial ↥(adjointGroup τ K) :=
      (QuotientGroup.mk'_surjective (Subgroup.center ↥(adjointGroup τ K))).nontrivial
    exact exists_ne 1
  exact ggOppRadGood_of_surjective hq hZ (MonoidHom.id _) Function.surjective_id ⟨u, hu⟩ hQne hQ

theorem universal_conclusion_of_surjective [Finite K] [CharP K 2] {U : Type*} [Group U]
    [Finite U] (hU : CFSG.IsQuasisimple U) (hZ : ∀ z ∈ Subgroup.center U, z ^ 2 = 1 → z = 1)
    (φ : U →* ↥(adjointGroup τ K)) (hφ : Function.Surjective φ) (hφ1 : ∃ u, φ u ≠ 1) :
    Finite U ∧ (∀ z ∈ Subgroup.center U, z ^ 2 = 1 → z = 1) ∧
      ∀ Q : Subgroup U, Q ≠ ⊥ → GGRadicalTwo ⊤ Q → GGOppRadGood ⊤ Q :=
  ⟨inferInstance, hZ, fun _ hQne hQ => ggOppRadGood_of_surjective hU hZ φ hφ hφ1 hQne hQ⟩

end GGOppRadExc

section Tags


theorem ggOppositeRadicalUniversalAt_F4 : GGOppositeRadicalUniversalAt .F4 := by
  intro n f _ _
  exact GGOppRadExc.universal_conclusion_adjointGroup
    (CFSG.LieType.Steinberg.Adjoint.isQuasisimple_f4 (GaloisField 2 f))

theorem ggOppositeRadicalUniversalAt_E8 : GGOppositeRadicalUniversalAt .E8 := by
  intro n f _ _
  exact GGOppRadExc.universal_conclusion_adjointGroup
    (CFSG.LieType.Steinberg.Adjoint.isQuasisimple_e8 (GaloisField 2 f))

theorem ggOppositeRadicalUniversalAt_E6 : GGOppositeRadicalUniversalAt .E6 := by
  intro n f _ _
  have : Finite ↥(CFSG.LieType.Steinberg.Minuscule.e6Data_valid.minGroup (GaloisField 2 f)) := by
    have : Finite (Module.End (GaloisField 2 f)
        (Fin CFSG.LieType.Steinberg.Minuscule.e6Data.d →₀ GaloisField 2 f)) :=
      Module.finite_of_finite (GaloisField 2 f)
    infer_instance
  exact GGOppRadExc.universal_conclusion_of_surjective
    (U := ↥(CFSG.LieType.Steinberg.Minuscule.e6Data_valid.minGroup (GaloisField 2 f)))
    (CFSG.LieType.CurtisTits.isQuasisimple_e6 (GaloisField 2 f))
    (CFSG.ComponentClassification.RankTwoOddLie.centerPPrime_e6 (p := 2) (GaloisField 2 f))
    (CFSG.LieType.Steinberg.Isogeny.e6Isogeny (GaloisField 2 f))
    (CFSG.LieType.Steinberg.Isogeny.e6Isogeny_surjective (GaloisField 2 f))
    (CFSG.LieType.Steinberg.Isogeny.e6Isogeny_ne_one (GaloisField 2 f))

theorem ggOppositeRadicalUniversalAt_E7 : GGOppositeRadicalUniversalAt .E7 := by
  intro n f _ _
  have : Finite ↥(CFSG.LieType.Steinberg.Minuscule.e7Data_valid.minGroup (GaloisField 2 f)) := by
    have : Finite (Module.End (GaloisField 2 f)
        (Fin CFSG.LieType.Steinberg.Minuscule.e7Data.d →₀ GaloisField 2 f)) :=
      Module.finite_of_finite (GaloisField 2 f)
    infer_instance
  exact GGOppRadExc.universal_conclusion_of_surjective
    (U := ↥(CFSG.LieType.Steinberg.Minuscule.e7Data_valid.minGroup (GaloisField 2 f)))
    (CFSG.LieType.CurtisTits.isQuasisimple_e7 (GaloisField 2 f))
    (CFSG.ComponentClassification.RankTwoOddLie.centerPPrime_e7 (p := 2) (GaloisField 2 f))
    (CFSG.LieType.Steinberg.Isogeny.e7Isogeny (GaloisField 2 f))
    (CFSG.LieType.Steinberg.Isogeny.e7Isogeny_surjective (GaloisField 2 f))
    (CFSG.LieType.Steinberg.Isogeny.exists_e7Isogeny_ne_one (GaloisField 2 f))

theorem ggOppositeRadicalCountNormalAt_F4 : GGOppositeRadicalCountNormalAt .F4 :=
  ggOppositeRadicalCountNormalAt_of_universal ggOppositeRadicalUniversalAt_F4

theorem ggOppositeRadicalCountNormalAt_E6 : GGOppositeRadicalCountNormalAt .E6 :=
  ggOppositeRadicalCountNormalAt_of_universal ggOppositeRadicalUniversalAt_E6

theorem ggOppositeRadicalCountNormalAt_E7 : GGOppositeRadicalCountNormalAt .E7 :=
  ggOppositeRadicalCountNormalAt_of_universal ggOppositeRadicalUniversalAt_E7

theorem ggOppositeRadicalCountNormalAt_E8 : GGOppositeRadicalCountNormalAt .E8 :=
  ggOppositeRadicalCountNormalAt_of_universal ggOppositeRadicalUniversalAt_E8

end Tags

end CFSG.StandardType
