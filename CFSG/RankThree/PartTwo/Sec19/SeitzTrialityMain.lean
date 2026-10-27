module

public import CFSG.RankThree.PartTwo.Sec19.SeitzTrialityFacts
public import CFSG.RankThree.PartTwo.Sec19.SeitzTrialityNF1
public import CFSG.RankThree.PartTwo.Sec19.SeitzTrialityNF4
public import CFSG.RankThree.PartTwo.Sec19.SeitzTrialityNFX
public import CFSG.RankThree.PartTwo.Sec19.SeitzTrialityTorus
public import CFSG.RankThree.PartTwo.Sec19.SeitzTrialityQ2Model

public section

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration
open CFSG.RankThree.PartTwo.Sec11 CFSG.RankThree.PartOne.CTP
open CFSG.RankThree.PartOne.Census3 (IsoLie)

namespace CFSG.RankThree.PartTwo.Sec19

section BridgeBigOuter

@[expose] def TrialityThreeOuterModelBig : Prop :=
  ∀ (n : ℕ), 2 ≤ n → ∀ (X : Type) [Field X] [Finite X] (σ : X ≃+* X),
    Nat.card X = (2 ^ n) ^ 3 → (∀ c : X, σ c = c ^ (2 ^ n)) →
      ∀ E : Subgroup (MulAut (C0 σ)), CFSG.IsElementaryAbelian 3 E → Nat.card E = 3 ^ 2 →
        ¬ (∀ φ ∈ E, ∃ g : C0 σ, φ = MulAut.conj g) → Subgroup.closure (fixUnion E) = ⊤

theorem trialityThreeOuterBig_of_model (h : TrialityThreeOuterModelBig) :
    ∀ q : TauCeti.PrimePower, q.p = 2 → 2 ≤ q.exponent → ∀ (K : Type) [Group K] [Finite K]
      [IsSimpleGroup K], IsoLie K (.trialityD4 q) → ∀ E : Subgroup (MulAut K),
        CFSG.IsElementaryAbelian 3 E → Nat.card E = 3 ^ 2 →
        ¬ (∀ φ ∈ E, ∃ g : K, φ = MulAut.conj g) → Subgroup.closure (fixUnion E) = ⊤ := by
  intro q hq hge K _ _ _ hiso E hE hcard hout
  obtain ⟨X, hF, hfin, σ, hcardX, hσ, -, ⟨e⟩⟩ :=
    CFSG.RankThree.PartOne.CTP.exists_trialityD4_model hq hiso
  have hE' : CFSG.IsElementaryAbelian 3 (E.map (MulAut.congr e).toMonoidHom) :=
    CFSG.LieType.SeitzGeneration.isElementaryAbelian_of_isElemAbelian
      (CFSG.LieType.SeitzGeneration.isElemAbelian_map_congr e
        (CFSG.Open.isElemAbelian_iff_isElementaryAbelian.mpr hE))
  have hcard' : Nat.card (E.map (MulAut.congr e).toMonoidHom) = 3 ^ 2 :=
    (CFSG.LieType.SeitzGeneration.card_map_congr e E).trans hcard
  have hnle : ¬ E ≤ (MulAut.conj : K →* MulAut K).range := fun hle =>
    hout fun φ hφ => (MonoidHom.mem_range.mp (hle hφ)).imp fun g hg => hg.symm
  have hnle' := CFSG.LieType.SeitzGeneration.not_le_range_conj_map_congr e hnle
  have hout' : ¬ (∀ φ ∈ E.map (MulAut.congr e).toMonoidHom, ∃ g : C0 σ, φ = MulAut.conj g) :=
    fun hall => hnle' fun φ hφ => MonoidHom.mem_range.mpr ((hall φ hφ).imp fun g hg => hg.symm)
  refine (planeGen_iff_closure_fixUnion E).mp (planeGen_of_outer_model e ?_)
  rw [planeGen_iff_closure_fixUnion]
  exact h q.exponent hge X σ hcardX hσ (E.map (MulAut.congr e).toMonoidHom) hE' hcard' hout'

end BridgeBigOuter

section AssemblyOuter

variable {X : Type} [Field X] [Finite X] (σ : X ≃+* X)

theorem trialityThreeOuterModelBig_holds (hgold : CFSG.Goldschmidt.TopStatement) :
    TrialityThreeOuterModelBig := by
  intro n hn X _ _ σ hX hσ E hE hcard hout
  classical
  have hD : D4Par n X σ := ⟨by omega, hX, hσ⟩
  have hAB := trialityABFacts_of_par hgold hD hn
  have hR1 := trialityR1Facts_of_par hgold hD
  have hk4 := hD.four_le_card_fix hn
  haveI : Finite (C0 σ) := finite_C0
  rw [← planeGen_iff_closure_fixUnion]
  obtain ⟨x, hx3, hx1, g, e, he, hβ3, hcomm, hEeq⟩ :=
    outer_plane_shape σ n (by omega) hX hσ E hE hcard hout
  have hxE : (MulAut.conj x : MulAut (C0 σ)) ∈ E := by
    rw [hEeq]; exact Subgroup.subset_closure (by simp)
  have hβE : (MulAut.conj g * tauAut σ ^ e : MulAut (C0 σ)) ∈ E := by
    rw [hEeq]; exact Subgroup.subset_closure (by simp)
  have hβ1 : (MulAut.conj g * tauAut σ ^ e : MulAut (C0 σ)) ≠ 1 := by
    intro h1
    apply hout
    have hle : E ≤ (MulAut.conj : C0 σ →* MulAut (C0 σ)).range := by
      rw [hEeq, Subgroup.closure_le]
      intro φ hφ
      rcases hφ with rfl | hφ
      · exact ⟨x, rfl⟩
      · rw [Set.mem_singleton_iff] at hφ
        rw [hφ, h1]
        exact ⟨1, by simp⟩
    intro φ hφ
    exact (MonoidHom.mem_range.mp (hle hφ)).imp fun k hk => hk.symm
  rcases three_conj_dichotomy σ n (by omega) hX hσ hx3 hx1 with hXc | hY
  · by_cases hG : HasGLine σ x g e
    · obtain ⟨ψ, a, ha, ha3, ha1, hmap⟩ := outer_G_case σ hAB n hn hX hσ he hx3 hx1 hβ3 hcomm hG
      rw [hEeq]
      refine (planeGen_map_congr ψ _).mp ?_
      rw [hmap]
      rcases ha with ha | ha
      · exact hR1.N3 hk4 ha ha3 ha1
      · exact hR1.N4 hk4 ha ha3 ha1
    · obtain ⟨h, hh, hcm, hne⟩ := outer_X_case σ hAB n hn hX hσ he hXc hβ3 hβ1 hcomm hG
      exact planeGen_of_pair σ n hn hX hσ hXc hxE hβE hβ1 hh hcm hne
  · obtain ⟨ψ, b, hb, hb3, hb1, hmap⟩ := outer_Y_case σ hAB n hn hX hσ he hx3 hx1 hβ3 hcomm hY
    rw [hEeq]
    refine (planeGen_map_congr ψ _).mp ?_
    rw [hmap]
    exact hR1.N4 hk4 hb hb3 hb1

theorem trialityThreeOuter_of_pieces (hgold : CFSG.Goldschmidt.TopStatement)
    (h1 : TrialityThreeOuterTwo) : TrialityThreeOuter :=
  trialityThreeOuter_of_split h1
    (trialityThreeOuterBig_of_model (trialityThreeOuterModelBig_holds hgold))

end AssemblyOuter

end CFSG.RankThree.PartTwo.Sec19
