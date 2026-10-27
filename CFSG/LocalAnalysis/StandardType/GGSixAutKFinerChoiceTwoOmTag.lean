module

public import CFSG.LocalAnalysis.StandardType.GGSixAutKFinerChoiceTwoOmGlue
public import CFSG.LocalAnalysis.StandardType.GGSixSeventeenWitOm
public import CFSG.LocalAnalysis.StandardType.GGSixAutKFinerChoiceTwo

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData

namespace ChoiceTwoOm

section Spin

variable {G : Type} [Group G] [Finite G] {U : Type} [Group U] {B Bs : Subgroup G}
  {x : G} {L D J : Subgroup G} {d : ℕ}
  {Q : QuadraticForm (GaloisField 2 1) (Fin d → GaloisField 2 1)}

theorem choice_of_spinModel (hnd : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule (GaloisField 2 1) (Fin d → GaloisField 2 1),
      Module.finrank (GaloisField 2 1) T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (ψ : U →* G) (hψ : Function.Injective ψ) (hrange : ψ.range = ggG0 3 B x L D J)
    (π : U →* matrixDerived Q) (hπ : Function.Bijective π)
    (hC : Subgroup.centralizer (ψ.range : Set G) = ⊥)
    (hdiag : ∀ b ∈ Bs, ∃ g ∈ ψ.range, b * g ∈ Subgroup.centralizer (ψ.range : Set G))
    (hBs : GGBstar 3 B Bs) (hB4 : 3 ^ 4 ≤ Nat.card B)
    (hDB : D ≤ Bs) (hD9 : Nat.card D = 3 ^ 2) (hDJ : D = B ⊓ Subgroup.centralizer (J : Set G))
    (hJq : CFSG.IsQuasisimple J) (hJG : J ≤ ggG0 3 B x L D J)
    (hJD : J ≤ Subgroup.centralizer (D : Set G))
    (hJc : Nat.card (Bs ⊓ Subgroup.centralizer (J : Set G) : Subgroup G) ≤ 3 ^ 3)
    {b : G} (hb : b ∈ Bs) (hb1 : b ≠ 1) {L₁ : Subgroup G}
    (hL₁ : IsComponentOf L₁ (ggG0 3 B x L D J ⊓ Subgroup.centralizer {b}))
    (hL₁c : Nat.card (Bs ⊓ Subgroup.centralizer (L₁ : Set G) : Subgroup G) ≤ 3 ^ 2) :
    ∃ m ∈ ggG0 3 B x L D J ⊓ Subgroup.normalizer (Bs : Set G),
      ∃ g ∈ L₁, (∃ l ∈ L₁, g * l ≠ l * g) ∧
        g ∈ Subgroup.centralizer (D.map (MulAut.conj m⁻¹).toMonoidHom : Set G) ∧
        Nat.Coprime (orderOf g) 3 := by
  set πe := MulEquiv.ofBijective π hπ with hπe
  set φ : matrixDerived Q →* G := ψ.comp πe.symm.toMonoidHom with hφ
  have hφinj : Function.Injective φ := hψ.comp πe.symm.injective
  have hφrange : φ.range = ψ.range := by
    ext y
    constructor
    · rintro ⟨X, rfl⟩
      exact ⟨_, rfl⟩
    · rintro ⟨u, rfl⟩
      exact ⟨πe u, by simp [hφ]⟩
  have hBφ : Bs ≤ φ.range := by
    intro b hb
    obtain ⟨g, hg, hbg⟩ := hdiag b hb
    rw [hC, Subgroup.mem_bot] at hbg
    rw [hφrange, eq_inv_of_mul_eq_one_left hbg]
    exact ψ.range.inv_mem hg
  exact choice_of_matrixModel hnd hT φ hφinj (hφrange.trans hrange) hBs hBφ hB4 hDB hD9 hDJ hJq
    hJG hJD hJc hb hb1 hL₁ hL₁c

theorem card_b_ge {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {Δ : UniversalRootDatum U} {t : StatedLieTag} {n f : ℕ} {ψ : U →* G}
    (hctx : GGSixCtxV2 p B Bs x L D J Δ t n f ψ) : p ^ 4 ≤ Nat.card B := by
  have hBcard : Nat.card B = p ^ LargeEvenTwoLocalRank p G := hctx.sstar.1.2.1
  rw [hBcard]
  exact Nat.pow_le_pow_right hctx.prime.pos hctx.beta.2.2.2

end Spin

end ChoiceTwoOm

section Tags

theorem ggStepTwoChoiceThreeTwoTag_POmegaPlus : GGStepTwoChoiceThreeTwoTag .POmegaPlus := by
  intro G _ _ p B Bs x L D J n
  by_cases hn : 3 ≤ n
  · rw [ggU_POmegaPlus_eq hn]
    intro ψ hctx s1 _ b L₁ hpair hp3 _
    subst hp3
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨hrange, hker⟩ := hctx.2.2.2.2.1
    have hψinj : Function.Injective ψ := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff,
        ← RootCentOmega.center_spinGroup_quadPlus_eq_bot_charTwo hn]
      exact hker
    have hCψ : Subgroup.centralizer (ψ.range : Set G) = ⊥ := by
      rw [hrange]
      exact s1.1
    obtain ⟨hnd, hT⟩ := regular_coordinateQuadPlus n (GaloisField 2 1) hn
    have hJcomp := hctx.j_isComponentOf_inf
    have hJq : CFSG.IsQuasisimple J :=
      (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native J).1
        hJcomp.2.2
    have hJD : J ≤ Subgroup.centralizer (D : Set G) := fun j hj =>
      (Subgroup.mem_inf.mp (hJcomp.1 hj)).2
    exact ChoiceTwoOm.choice_of_spinModel hnd hT ψ hψinj hrange (AutOm.spinModelPlus hn)
      ⟨AutOm.spinModelPlus_injective hn, AutOm.spinModelPlus_surjective hn⟩ hCψ
      (fun b hb => PsiDiag.SpinP.exists_mem_centralizer hn ψ hker (hctx.2.2.2.2.2.2.1.2 b hb))
      hctx.bstar (ChoiceTwoOm.card_b_ge hctx) hctx.d_le_bstar hctx.card_d
      hctx.stdSub.1.2.2.2.2.2.2 hJq hctx.le_ggG0 hJD hctx.card_bstar_inf_centralizer_le
      hpair.1 hpair.2.1 hpair.2.2.1 hpair.2.2.2
  · intro ψ hctx
    exact absurd hctx.2.2.2.1.1.2.2 (by omega)

theorem ggStepTwoChoiceThreeTwoTag_POmegaMinus : GGStepTwoChoiceThreeTwoTag .POmegaMinus := by
  intro G _ _ p B Bs x L D J n
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [show ggU .POmegaMinus n 1 = ⟨spinGroup (quadMinus n (GaloisField 2 1)
      (minusCoeffs 2 1).1 (minusCoeffs 2 1).2), Spin.Twisted.minusDatum n (minusCoeffs_irr 2 1)⟩
      from rfl]
  intro ψ hctx s1 _ b L₁ hpair hp3 _
  subst hp3
  have hn : 4 ≤ n := hctx.2.2.2.1.1.2.2
  have hirr := minusCoeffs_irr 2 1
  obtain ⟨hrange, hker⟩ := hctx.2.2.2.2.1
  have hψinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff, ← PsiDiag.SpinM.center_eq_bot hirr hn]
    exact hker
  have hCψ : Subgroup.centralizer (ψ.range : Set G) = ⊥ := by
    rw [hrange]
    exact s1.1
  obtain ⟨hnd, hT⟩ := regular_coordinateQuadMinus n (GaloisField 2 1) _ _ hn hirr
  have hJcomp := hctx.j_isComponentOf_inf
  have hJq : CFSG.IsQuasisimple J :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native J).1 hJcomp.2.2
  have hJD : J ≤ Subgroup.centralizer (D : Set G) := fun j hj =>
    (Subgroup.mem_inf.mp (hJcomp.1 hj)).2
  exact ChoiceTwoOm.choice_of_spinModel hnd hT ψ hψinj hrange (AutOm.spinModelMinus hn hirr)
    ⟨AutOm.spinModelMinus_injective hn hirr, AutOm.spinModelMinus_surjective hn hirr⟩ hCψ
    (fun b hb => PsiDiag.SpinM.exists_mem_centralizer hirr hn ψ hker
      (hctx.2.2.2.2.2.2.1.2 b hb))
    hctx.bstar (ChoiceTwoOm.card_b_ge hctx) hctx.d_le_bstar hctx.card_d
    hctx.stdSub.1.2.2.2.2.2.2 hJq hctx.le_ggG0 hJD hctx.card_bstar_inf_centralizer_le
    hpair.1 hpair.2.1 hpair.2.2.1 hpair.2.2.2

@[expose] def GGStepTwoChoiceThreeTwoRestFive : Prop :=
  GGStepTwoChoiceThreeTwoTag .F4 ∧ GGStepTwoChoiceThreeTwoTag .E6 ∧
    GGStepTwoChoiceThreeTwoTag .E7 ∧ GGStepTwoChoiceThreeTwoTag .E8 ∧
      GGStepTwoChoiceThreeTwoTag .twistedE6

theorem ggStepTwoChoiceThreeTwoRestSeven_of_five (h : GGStepTwoChoiceThreeTwoRestFive) :
    GGStepTwoChoiceThreeTwoRestSeven :=
  ⟨ggStepTwoChoiceThreeTwoTag_POmegaPlus, ggStepTwoChoiceThreeTwoTag_POmegaMinus, h⟩

theorem ggStepTwoChoiceThreeTwoRest_of_five (h : GGStepTwoChoiceThreeTwoRestFive) :
    GGStepTwoChoiceThreeTwoRest :=
  ggStepTwoChoiceThreeTwoRest_of_seven (ggStepTwoChoiceThreeTwoRestSeven_of_five h)

end Tags

end CFSG.StandardType
