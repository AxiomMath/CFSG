module

public import CFSG.LocalAnalysis.StandardType.GGSixSeventeenWitOmGlue
public import CFSG.LocalAnalysis.StandardType.GGSixBstarNoOffenderOmegaPM
public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitKGOmTag

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData

namespace SevOm

section Spin

variable {G : Type} [Group G] [Finite G] {U : Type} [Group U] {p : ℕ} {B Bs : Subgroup G}
  {x : G} {L D J : Subgroup G} {t : StatedLieTag} {f d : ℕ}
  {Q : QuadraticForm (GaloisField 2 f) (Fin d → GaloisField 2 f)}

theorem witness_of_spinModel (htL : t ≠ .PSL) (htU : t ≠ .PSU) (hf : 1 ≤ f)
    (hnd : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule (GaloisField 2 f) (Fin d → GaloisField 2 f),
      Module.finrank (GaloisField 2 f) T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (ψ : U →* G) (hψ : Function.Injective ψ) (hrange : ψ.range = ggG0 p B x L D J)
    (π : U →* matrixDerived Q) (hπ : Function.Bijective π)
    (hC : Subgroup.centralizer (ψ.range : Set G) = ⊥)
    (hdiag : ∀ b ∈ Bs, ∃ g ∈ ψ.range, b * g ∈ Subgroup.centralizer (ψ.range : Set G))
    (hp : p.Prime) (hp2 : p ≠ 2) (hBs : GGBstar p B Bs) (hcard : p ^ 4 ≤ Nat.card Bs)
    (hres : ¬ ((f = 1 ∧ p = 3) ∨ (f = 2 ∧ p = 5)))
    {b : G} (hb : b ∈ Bs) (hb1 : b ≠ 1) {L₁ : Subgroup G}
    (hL₁ : IsComponentOf L₁ (ggG0 p B x L D J ⊓ Subgroup.centralizer {b}))
    (hpL : p ∣ Nat.card L₁) :
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
  exact witness_of_matrixModel htL htU hf hnd hT φ hφinj (hφrange.trans hrange) hp hp2 hBs hBφ
    hcard hres hb hb1 hL₁ hpL

end Spin

theorem card_bstar_ge {G : Type} [Group G] [Finite G] {U : Type} [Group U] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {Δ : UniversalRootDatum U}
    {t : StatedLieTag} {n f : ℕ} {ψ : U →* G} (hctx : GGSixCtxV2 p B Bs x L D J Δ t n f ψ) :
    p ^ 4 ≤ Nat.card Bs := by
  have hBcard : Nat.card B = p ^ LargeEvenTwoLocalRank p G := hctx.sstar.1.2.1
  have hBBs : Nat.card B ≤ Nat.card Bs := Subgroup.card_le_of_le hctx.bstar.1
  calc p ^ 4 ≤ p ^ LargeEvenTwoLocalRank p G :=
        Nat.pow_le_pow_right hctx.prime.pos hctx.beta.2.2.2
    _ = Nat.card B := hBcard.symm
    _ ≤ Nat.card Bs := hBBs

end SevOm

section Inputs

@[expose] def GGSixSeventeenOmSmallInput : Prop :=
  GGSixSeventeenWitnessDvdOn fun t _ f p =>
    (t = .POmegaPlus ∨ t = .POmegaMinus) ∧ ((f = 1 ∧ p = 3) ∨ (f = 2 ∧ p = 5))

theorem ggSixSeventeenWitnessDvdOn_POmegaPlus_of_small (hsmall : GGSixSeventeenOmSmallInput) :
    GGSixSeventeenWitnessDvdOn (fun t _ _ _ => t = .POmegaPlus) := by
  intro G _ _ p B Bs x L D J t n f ψ hP
  subst hP
  by_cases hres : (f = 1 ∧ p = 3) ∨ (f = 2 ∧ p = 5)
  · exact hsmall G p B Bs x L D J _ n f ψ ⟨Or.inl rfl, hres⟩
  revert ψ
  by_cases hn : 3 ≤ n
  · rw [ggU_POmegaPlus_eq hn]
    intro ψ hctx s1 b L₁ hpair hpL
    obtain ⟨hb, hb1, hL₁, -⟩ := hpair
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hp : p.Prime := hctx.prime
    have hp2 : p ≠ 2 := hctx.ne_two
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
    obtain ⟨e, he, h⟩ := SevOm.witness_of_spinModel (t := .POmegaPlus) (by decide) (by decide)
      hf hnd hT ψ hψinj hrange (AutOm.spinModelPlus hn)
      ⟨AutOm.spinModelPlus_injective hn, AutOm.spinModelPlus_surjective hn⟩ hCψ
      (fun b hb => PsiDiag.SpinP.exists_mem_centralizer hn ψ hker (hctx.2.2.2.2.2.2.1.2 b hb))
      hp hp2 hctx.bstar (SevOm.card_bstar_ge hctx) hres hb hb1 hL₁ hpL
    exact Or.inr ⟨e, he, h⟩
  · intro ψ hctx
    exact absurd hctx.2.2.2.1.1.2.2 (by omega)

theorem ggSixSeventeenWitnessDvdOn_POmegaMinus_of_small (hsmall : GGSixSeventeenOmSmallInput) :
    GGSixSeventeenWitnessDvdOn (fun t _ _ _ => t = .POmegaMinus) := by
  intro G _ _ p B Bs x L D J t n f ψ hP
  subst hP
  by_cases hres : (f = 1 ∧ p = 3) ∨ (f = 2 ∧ p = 5)
  · exact hsmall G p B Bs x L D J _ n f ψ ⟨Or.inr rfl, hres⟩
  revert ψ
  rw [show ggU .POmegaMinus n f = ⟨spinGroup (quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1
      (minusCoeffs 2 f).2), Spin.Twisted.minusDatum n (minusCoeffs_irr 2 f)⟩ from rfl]
  intro ψ hctx s1 b L₁ hpair hpL
  obtain ⟨hb, hb1, hL₁, -⟩ := hpair
  have hn : 4 ≤ n := hctx.2.2.2.1.1.2.2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : p.Prime := hctx.prime
  have hp2 : p ≠ 2 := hctx.ne_two
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
  obtain ⟨e, he, h⟩ := SevOm.witness_of_spinModel (t := .POmegaMinus) (by decide) (by decide)
    hf hnd hT ψ hψinj hrange (AutOm.spinModelMinus hn hirr)
    ⟨AutOm.spinModelMinus_injective hn hirr, AutOm.spinModelMinus_surjective hn hirr⟩ hCψ
    (fun b hb => PsiDiag.SpinM.exists_mem_centralizer hirr hn ψ hker
      (hctx.2.2.2.2.2.2.1.2 b hb))
    hp hp2 hctx.bstar (SevOm.card_bstar_ge hctx) hres hb hb1 hL₁ hpL
  exact Or.inr ⟨e, he, h⟩

@[expose] def GGSixSeventeenWitnessRest11 : Prop :=
  GGSixSeventeenOmSmallInput ∧ GGSixSeventeenE8SevenInput ∧
    GGSixSeventeenRootWitnessInputFor GGExceptionalTag

theorem ggSixSeventeenWitnessRest11_of_rest10 (h : GGSixSeventeenWitnessRest10) :
    GGSixSeventeenWitnessRest11 := by
  obtain ⟨hPl, hMi, hE8, hex⟩ := h
  refine ⟨fun G _ _ p B Bs x L D J t n f ψ hP => ?_, hE8, hex⟩
  rcases hP.1 with rfl | rfl
  · exact hPl G p B Bs x L D J _ n f ψ rfl
  · exact hMi G p B Bs x L D J _ n f ψ rfl

theorem ggSixSeventeenWitnessRest10_of_rest11 (h : GGSixSeventeenWitnessRest11) :
    GGSixSeventeenWitnessRest10 :=
  ⟨ggSixSeventeenWitnessDvdOn_POmegaPlus_of_small h.1,
    ggSixSeventeenWitnessDvdOn_POmegaMinus_of_small h.1, h.2.1, h.2.2⟩

end Inputs

section Wiring

theorem ggSixSeventeenWitnessInput_of_rest11 (h : GGSixSeventeenWitnessRest11) :
    GGSixSeventeenWitnessInputFor fun _ => True :=
  ggSixSeventeenWitnessInput_of_rest10 ggNonsplitTag_POmegaPlus ggNonsplitTag_POmegaMinus
    (ggSixSeventeenWitnessRest10_of_rest11 h)

end Wiring

end CFSG.StandardType
