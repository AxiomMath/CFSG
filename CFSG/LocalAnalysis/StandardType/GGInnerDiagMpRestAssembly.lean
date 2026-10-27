module

public import CFSG.LocalAnalysis.StandardType.GGInnerDiagMpRestLinear
public import CFSG.LocalAnalysis.StandardType.GGInnerDiagMpRestTypeDet
public import CFSG.LocalAnalysis.StandardType.GGInnerDiagMpRestInner

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.Assembly.LowTwoRank

section Inputs

@[expose] def GGInnerDiagStdUnitary : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (n f : ℕ) (ψ : (ggU .PSU n f).K →* G),
    StatedLieAdmissible .PSU n 2 f → 2 ≤ (ggU .PSU n f).D.rank → ¬ (2 ^ f + 1).Coprime n →
    ψ.ker ≤ Subgroup.center (ggU .PSU n f).K →
    ∀ (K : Type) [Field K] [Finite K], Nat.card K = (2 ^ f) ^ 2 →
      ∃ θ₀ : ↥ψ.range ⧸ Subgroup.center ↥ψ.range ≃*
          LargeEvenProj (LargeEvenSUGroup (Fin n) K (2 ^ f)),
        GGRevProp (ggU .PSU n f).D ψ ψ.range
          (ggInndiag (LargeEvenProj (LargeEvenSUGroup (Fin n) K (2 ^ f)))
            (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin n) K (2 ^ f)))
              (LargeEvenGUSet (Fin n) K (2 ^ f)))) θ₀

@[expose] def GGInnerDiagStdE6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (f : ℕ) (ψ : (ggU .E6 0 f).K →* G),
    StatedLieAdmissible .E6 0 2 f → Even f → ψ.ker ≤ Subgroup.center (ggU .E6 0 f).K →
    ∀ (K : Type) [Field K] [Finite K], Nat.card K = 2 ^ f →
      ∃ θ₀ : ↥ψ.range ⧸ Subgroup.center ↥ψ.range ≃*
          LargeEvenCenterQuot (LargeEvenChevH (LargeEvenCartanE 6) K false),
        GGRevProp (ggU .E6 0 f).D ψ ψ.range
          (ggInndiag (LargeEvenCenterQuot (LargeEvenChevH (LargeEvenCartanE 6) K false))
            (LargeEvenChevIDImage (LargeEvenCartanE 6) K
              (LargeEvenChevH (LargeEvenCartanE 6) K false))) θ₀

@[expose] def GGInnerDiagStdTwE6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (f : ℕ) (ψ : (ggU .twistedE6 0 f).K →* G),
    StatedLieAdmissible .twistedE6 0 2 f → ψ.ker ≤ Subgroup.center (ggU .twistedE6 0 f).K →
    ∀ (K : Type) [Field K] [Finite K], Nat.card K = (2 ^ f) ^ 2 →
      ∃ θ₀ : ↥ψ.range ⧸ Subgroup.center ↥ψ.range ≃*
          LargeEvenCenterQuot (LargeEvenTwistedH (LargeEvenCartanE 6) K LargeEvenRhoE6 f),
        GGRevProp (ggU .twistedE6 0 f).D ψ ψ.range
          (ggInndiag (LargeEvenCenterQuot (LargeEvenTwistedH (LargeEvenCartanE 6) K
              LargeEvenRhoE6 f))
            (LargeEvenChevIDImage (LargeEvenCartanE 6) K
              (LargeEvenTwistedH (LargeEvenCartanE 6) K LargeEvenRhoE6 f))) θ₀

end Inputs

section Families

@[expose] def GGMpUnitaryRestLabel (lab : LargeEvenLabel) : Prop :=
  lab.tag = .twA ∧ ¬ (2 ^ lab.n + 1).Coprime (lab.rank + 1)

theorem ggInnerDiagStdOn_unitaryRest (hstd : GGInnerDiagStdUnitary) :
    GGInnerDiagStdOn GGMpUnitaryRestLabel := by
  intro G _ _ t n f ψ hadm hrk hker lab hlab hU Q hQ
  obtain ⟨tg, l, n'⟩ := lab
  obtain ⟨h, hc⟩ := hU
  dsimp only at h hc
  subst h
  obtain ⟨K, _, _, hK, hQK⟩ := hQ
  refine ⟨K, inferInstance, inferInstance, hK, hQK, fun _ _ hM ⟨e⟩ => ?_⟩
  obtain ⟨rfl, rfl, rfl⟩ := unitary_param_eq hlab (Or.inl rfl)
    (MarkedModel.of_mulEquiv e.symm hM) hadm (lieModel_range_centerQuot hadm hrk ψ hker)
  exact hstd G _ _ ψ hadm hrk hc hker K hK

theorem ggInnerDiagStdOn_E6_even (hstd : GGInnerDiagStdE6) :
    GGInnerDiagStdOn fun lab => lab.tag = .E6 ∧ Even lab.n := by
  intro G _ _ t n f ψ hadm hrk hker lab hlab hE Q hQ
  obtain ⟨tg, l, n'⟩ := lab
  obtain ⟨hE, hev⟩ := hE
  dsimp only at hE hev
  subst hE
  obtain ⟨hn, hl⟩ := hlab
  dsimp only at hn hl
  subst hl
  obtain ⟨K, _, _, hK, hQK⟩ := hQ
  refine ⟨K, inferInstance, inferInstance, hK, hQK, fun _ _ hM ⟨e⟩ => ?_⟩
  obtain ⟨h1, h2, -, h3⟩ := ggMarkTypeDet_E6 hn t _ n f hadm hrk
    (lieModel_range_centerQuot hadm hrk ψ hker) (MarkedModel.of_mulEquiv e.symm hM)
  change StatedLieTag.E6 = t at h1
  subst h1
  change 0 = n at h2
  subst h2
  change n' = f at h3
  subst h3
  exact hstd G n' ψ hadm hev hker K hK

theorem ggInnerDiagStdOn_twE6 (hstd : GGInnerDiagStdTwE6) :
    GGInnerDiagStdOn fun lab => lab.tag = .twE6 := by
  intro G _ _ t n f ψ hadm hrk hker lab hlab hE Q hQ
  obtain ⟨tg, l, n'⟩ := lab
  dsimp only at hE
  subst hE
  obtain ⟨hn, hl⟩ := hlab
  dsimp only at hn hl
  subst hl
  obtain ⟨K, _, _, hK, hQK⟩ := hQ
  refine ⟨K, inferInstance, inferInstance, hK, hQK, fun _ _ hM ⟨e⟩ => ?_⟩
  obtain ⟨h1, h2, -, h3⟩ := ggMarkTypeDet_twE6 hn t _ n f hadm hrk
    (lieModel_range_centerQuot hadm hrk ψ hker) (MarkedModel.of_mulEquiv e.symm hM)
  change StatedLieTag.twistedE6 = t at h1
  subst h1
  change 0 = n at h2
  subst h2
  change n' = f at h3
  subst h3
  exact hstd G n' ψ hadm hker K hK


theorem ggInnerDiagMpInputOn_unitary (hstd : GGInnerDiagStdUnitary) :
    GGInnerDiagMpInputOn GGMpUnitaryLabel :=
  ggInnerDiagMpInputOn_mono (S := GGMpUnitaryLabel)
    (T := fun lab => GGMpUnitaryCopLabel lab ∨ GGMpUnitaryRestLabel lab) (fun lab _ h => by
      rcases h with h | h
      · by_cases hc : (2 ^ lab.n + 1).Coprime (lab.rank + 1)
        · exact Or.inl (Or.inl ⟨h, hc⟩)
        · exact Or.inr ⟨h, hc⟩
      · exact Or.inl (Or.inr h))
    (ggInnerDiagMpInputOn_or ggInnerDiagMpInputOn_unitaryCop
      (ggInnerDiagMpInputOn_of_std (fun lab hlab _ => ggInndiagNormalInput_holds lab hlab)
        (ggInnerDiagStdOn_unitaryRest hstd)))

theorem ggInnerDiagMpInputOn_E6 (hstd : GGInnerDiagStdE6) :
    GGInnerDiagMpInputOn fun lab => lab.tag = .E6 :=
  ggInnerDiagMpInputOn_mono (S := fun lab => lab.tag = .E6)
    (T := fun lab => (lab.tag = .E6 ∧ Odd lab.n) ∨ (lab.tag = .E6 ∧ Even lab.n))
    (fun lab _ h => (Nat.even_or_odd lab.n).elim (fun he => Or.inr ⟨h, he⟩)
      (fun ho => Or.inl ⟨h, ho⟩))
    (ggInnerDiagMpInputOn_or ggInnerDiagMpInputOn_E6_odd
      (ggInnerDiagMpInputOn_of_std (fun lab hlab _ => ggInndiagNormalInput_holds lab hlab)
        (ggInnerDiagStdOn_E6_even hstd)))

theorem ggInnerDiagMpInputOn_twE6 (hstd : GGInnerDiagStdTwE6) :
    GGInnerDiagMpInputOn fun lab => lab.tag = .twE6 :=
  ggInnerDiagMpInputOn_of_std (fun lab hlab _ => ggInndiagNormalInput_holds lab hlab)
    (ggInnerDiagStdOn_twE6 hstd)

theorem ggInnerDiagMpInputOn_rest_of_std (hU : GGInnerDiagStdUnitary) (hE6 : GGInnerDiagStdE6)
    (h2E6 : GGInnerDiagStdTwE6) : GGInnerDiagMpInputOn fun lab => ¬ GGInnerDiagInnLabel lab :=
  ggInnerDiagMpInputOn_rest_of_families ggInnerDiagMpInputOn_linear
    (ggInnerDiagMpInputOn_unitary hU) (ggInnerDiagMpInputOn_E6 hE6)
    (ggInnerDiagMpInputOn_twE6 h2E6) ggInnerDiagMpInputOn_triD4 ggInnerDiagMpInputOn_twF4
    ggInnerDiagMpInputOn_b2der

theorem ggInnerDiagMpInput_of_std (hU : GGInnerDiagStdUnitary) (hE6 : GGInnerDiagStdE6)
    (h2E6 : GGInnerDiagStdTwE6) : GGInnerDiagMpInput :=
  ggInnerDiagMpInput_of_rest (ggInnerDiagMpInputOn_rest_of_std hU hE6 h2E6)

end Families

end CFSG.StandardType
