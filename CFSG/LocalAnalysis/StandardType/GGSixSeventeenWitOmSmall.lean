module

public import CFSG.LocalAnalysis.StandardType.GGSixSeventeenWitOmSmallGlue
public import CFSG.LocalAnalysis.StandardType.GGSixSeventeenWitOm

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData

namespace SevOmSmall

section Spin

variable {G : Type} [Group G] [Finite G] {U : Type} [Group U] {p : ℕ} {B Bs : Subgroup G}
  {x : G} {L D J : Subgroup G} {t : StatedLieTag} {f d : ℕ}
  {Q : QuadraticForm (GaloisField 2 f) (Fin d → GaloisField 2 f)}

theorem witness_of_spinModel_small (hf : 1 ≤ f) (hnd : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule (GaloisField 2 f) (Fin d → GaloisField 2 f),
      Module.finrank (GaloisField 2 f) T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (ψ : U →* G) (hψ : Function.Injective ψ) (hrange : ψ.range = ggG0 p B x L D J)
    (π : U →* matrixDerived Q) (hπ : Function.Bijective π)
    (hC : Subgroup.centralizer (ψ.range : Set G) = ⊥)
    (hdiag : ∀ b ∈ Bs, ∃ g ∈ ψ.range, b * g ∈ Subgroup.centralizer (ψ.range : Set G))
    (hp : p.Prime) (hp2 : p ≠ 2) (hBs : GGBstar p B Bs) (hcard : p ^ 4 ≤ Nat.card Bs)
    (hsmall : (f = 1 ∧ p = 3) ∨ (f = 2 ∧ p = 5))
    {b : G} (hb : b ∈ Bs) (hb1 : b ≠ 1) {L₁ : Subgroup G}
    (hL₁ : IsComponentOf L₁ (ggG0 p B x L D J ⊓ Subgroup.centralizer {b}))
    (hex : ¬ GGSixSeventeenExcluded p t f L₁) (hpL : p ∣ Nat.card L₁) :
    (∃ L₂ : Subgroup G, IsComponentOf L₂ (ggG0 p B x L D J ⊓ Subgroup.centralizer {b}) ∧
      Nat.card (Bs ⊓ Subgroup.centralizer (L₂ : Set G) : Subgroup G) ≤ p ^ 2) ∨
    ∃ e ∈ L₁, GGSixSeventeenDirect p Bs D (ggG0 p B x L D J) e ∨
      (e ∈ Bs ∧ e ≠ 1 ∧ GGSixSeventeenSixteen p B Bs x L D J t f e) := by
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
  exact witness_of_matrixModel_small hf hnd hT φ hφinj (hφrange.trans hrange) hp hp2 hBs hBφ
    hcard hsmall hb hb1 hL₁ hex hpL

end Spin

end SevOmSmall

section Inputs

theorem ggSixSeventeenOmSmallInput_holds : GGSixSeventeenOmSmallInput := by
  intro G _ _ p B Bs x L D J t n f ψ hP
  obtain ⟨ht, hsmall⟩ := hP
  rcases ht with rfl | rfl
  · revert ψ
    by_cases hn : 3 ≤ n
    · rw [ggU_POmegaPlus_eq hn]
      intro ψ hctx s1 b L₁ hpair hpL
      obtain ⟨hb, hb1, hL₁, hex⟩ := hpair
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have hf : 1 ≤ f := hctx.2.2.2.1.1.2.1
      obtain ⟨hrange, hker⟩ := hctx.2.2.2.2.1
      have hψinj : Function.Injective ψ := by
        rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff,
          ← RootCentOmega.center_spinGroup_quadPlus_eq_bot_charTwo hn]
        exact hker
      have hCψ : Subgroup.centralizer (ψ.range : Set G) = ⊥ := by
        rw [hrange]
        exact s1.1
      obtain ⟨hnd, hT⟩ := regular_coordinateQuadPlus n (GaloisField 2 f) hn
      exact SevOmSmall.witness_of_spinModel_small (t := .POmegaPlus) hf hnd hT ψ hψinj hrange
        (AutOm.spinModelPlus hn)
        ⟨AutOm.spinModelPlus_injective hn, AutOm.spinModelPlus_surjective hn⟩ hCψ
        (fun b hb => PsiDiag.SpinP.exists_mem_centralizer hn ψ hker (hctx.2.2.2.2.2.2.1.2 b hb))
        hctx.prime hctx.ne_two hctx.bstar (SevOm.card_bstar_ge hctx) hsmall hb hb1 hL₁ hex hpL
    · intro ψ hctx
      exact absurd hctx.2.2.2.1.1.2.2 (by omega)
  · revert ψ
    rw [show ggU .POmegaMinus n f = ⟨spinGroup (quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1
        (minusCoeffs 2 f).2), Spin.Twisted.minusDatum n (minusCoeffs_irr 2 f)⟩ from rfl]
    intro ψ hctx s1 b L₁ hpair hpL
    obtain ⟨hb, hb1, hL₁, hex⟩ := hpair
    have hn : 4 ≤ n := hctx.2.2.2.1.1.2.2
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hf : 1 ≤ f := hctx.2.2.2.1.1.2.1
    have hirr := minusCoeffs_irr 2 f
    obtain ⟨hrange, hker⟩ := hctx.2.2.2.2.1
    have hψinj : Function.Injective ψ := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff, ← PsiDiag.SpinM.center_eq_bot hirr hn]
      exact hker
    have hCψ : Subgroup.centralizer (ψ.range : Set G) = ⊥ := by
      rw [hrange]
      exact s1.1
    obtain ⟨hnd, hT⟩ := regular_coordinateQuadMinus n (GaloisField 2 f) _ _ hn hirr
    exact SevOmSmall.witness_of_spinModel_small (t := .POmegaMinus) hf hnd hT ψ hψinj hrange
      (AutOm.spinModelMinus hn hirr)
      ⟨AutOm.spinModelMinus_injective hn hirr, AutOm.spinModelMinus_surjective hn hirr⟩ hCψ
      (fun b hb => PsiDiag.SpinM.exists_mem_centralizer hirr hn ψ hker
        (hctx.2.2.2.2.2.2.1.2 b hb))
      hctx.prime hctx.ne_two hctx.bstar (SevOm.card_bstar_ge hctx) hsmall hb hb1 hL₁ hex hpL

theorem ggSixSeventeenWitnessDvdOn_POmegaPlus :
    GGSixSeventeenWitnessDvdOn (fun t _ _ _ => t = .POmegaPlus) :=
  ggSixSeventeenWitnessDvdOn_POmegaPlus_of_small ggSixSeventeenOmSmallInput_holds

theorem ggSixSeventeenWitnessDvdOn_POmegaMinus :
    GGSixSeventeenWitnessDvdOn (fun t _ _ _ => t = .POmegaMinus) :=
  ggSixSeventeenWitnessDvdOn_POmegaMinus_of_small ggSixSeventeenOmSmallInput_holds

@[expose] def GGSixSeventeenWitnessRest12 : Prop :=
  GGSixSeventeenE8SevenInput ∧ GGSixSeventeenRootWitnessInputFor GGExceptionalTag

theorem ggSixSeventeenWitnessRest12_of_rest11 (h : GGSixSeventeenWitnessRest11) :
    GGSixSeventeenWitnessRest12 :=
  h.2

theorem ggSixSeventeenWitnessRest11_of_rest12 (h : GGSixSeventeenWitnessRest12) :
    GGSixSeventeenWitnessRest11 :=
  ⟨ggSixSeventeenOmSmallInput_holds, h⟩

end Inputs

section Wiring

theorem ggSixSeventeenWitnessInput_of_rest12 (h : GGSixSeventeenWitnessRest12) :
    GGSixSeventeenWitnessInputFor fun _ => True :=
  ggSixSeventeenWitnessInput_of_rest11 (ggSixSeventeenWitnessRest11_of_rest12 h)

end Wiring

end CFSG.StandardType
