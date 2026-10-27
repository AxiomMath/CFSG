module

public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordModelSpNs
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutNonsplitOm

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.LieType.Universal.Spin.Twisted CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData Multiplicative
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.RankThree.PartOne.KCOrthComm (matrixDerivedEquiv)

@[expose] def GGOmCoordInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K : Type) [Field K] [Finite K] [CharP K 2]
    (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (p : ℕ) [Fact p.Prime],
    p ≠ 2 → ∀ Q : QuadraticForm K V, (QuadraticMap.polarBilin Q).Nondegenerate →
    (∃ T : Submodule K V, Module.finrank K T = 3 ∧ ∀ v ∈ T, Q v = 0) →
    ∀ φ : ↥(orthDerived Q) →* G, Function.Injective φ →
    ∀ Bs : Subgroup G, Bs ≤ φ.range → IsElemAbelian p Bs → p ^ 4 ≤ Nat.card Bs →
      (∀ g ∈ φ.range ⊓ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs) →
      ∃ (r : ℕ) (ι : Multiplicative (Fin r → ZMod p) →* G),
        Function.Injective ι ∧ ι.range = Bs ∧
        (∀ (π : Equiv.Perm (Fin r)) (η : Fin r → (ZMod p)ˣ),
          (∀ i, η i ∈ CoordSpNs.galSigns p (Nat.card K)) → ∏ i, η i = 1 →
          ∃ w ∈ φ.range ⊓ Subgroup.normalizer (Bs : Set G), ∀ s : Fin r → ZMod p,
            w⁻¹ * ι (ofAdd s) * w = ι (ofAdd fun i => (η i : ZMod p) * s (π i))) ∧
        (∀ (b : G) (L₁ : Subgroup G), b ∈ Bs → b ≠ 1 →
          IsComponentOf L₁ (φ.range ⊓ Subgroup.centralizer {b}) →
          Nat.card (Bs ⊓ Subgroup.centralizer (L₁ : Set G) : Subgroup G) ≤ p ^ 2 →
          ∀ β : Fin r → ZMod p, ι (ofAdd β) = b →
            (∃ j j' : Fin r, (∀ i, i ≠ j → i ≠ j' → β i = 0) ∧
              ∀ s : Fin r → ZMod p, s j = 0 → s j' = 0 → ι (ofAdd s) ∈ L₁) ∨
            (∃ (k : Fin r) (c : ZMod p) (ε : Fin r → (ZMod p)ˣ), c ≠ 0 ∧
              (∀ i, ε i ∈ CoordSpNs.galSigns p (Nat.card K)) ∧
              (∀ i, i ≠ k → β i = (ε i : ZMod p) * c) ∧
              ∀ s : Fin r → ZMod p, s k = 0 → ∑ i, (↑(ε i)⁻¹ : ZMod p) * s i = 0 →
                ι (ofAdd s) ∈ L₁)) ∧
        ∀ E J : Subgroup G, E ≤ Bs →
          IsComponentOf J (φ.range ⊓ Subgroup.centralizer (E : Set G)) →
          Nat.card (Bs ⊓ Subgroup.centralizer (J : Set G) : Subgroup G) ≤ p ^ 3 →
          StepTwoToral.GGStepTwoCoordShape p r (CoordSpNs.galSigns p (Nat.card K)) ι E

namespace CoordOm

theorem coordModel_of_model (hcoord : GGOmCoordInput) {G : Type} [Group G] [Finite G]
    {U : Type} [Group U] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {Δ : UniversalRootDatum U} {t : StatedLieTag} {n f : ℕ} {ψ : U →* G}
    (hctx : GGSixCtxV2 p B Bs x L D J Δ t n f ψ) (s1 : GGSixStepOne p B Bs x L D J) {d : ℕ}
    {Q : QuadraticForm (GaloisField 2 f) (Fin d → GaloisField 2 f)}
    (hnd : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule (GaloisField 2 f) (Fin d → GaloisField 2 f),
      Module.finrank (GaloisField 2 f) T = 3 ∧ ∀ v ∈ T, Q v = 0)
    (hψ : Function.Injective ψ) (π : U →* matrixDerived Q) (hπ : Function.Bijective π)
    (hdiag : ∀ b ∈ Bs, ∃ g ∈ ψ.range, b * g ∈ Subgroup.centralizer (ψ.range : Set G)) :
    ∃ (r : ℕ) (O : Subgroup (ZMod p)ˣ) (ι : Multiplicative (Fin r → ZMod p) →* G),
      StepTwoToral.GGStepTwoCoords p r O ι Bs (ggG0 p B x L D J) D
        (GGStepTwoPair p B Bs x L D J) := by
  classical
  have hp : p.Prime := hctx.prime
  have hp2 : p ≠ 2 := hctx.ne_two
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hrange : ψ.range = ggG0 p B x L D J := hctx.2.2.2.2.1.1
  have hC : Subgroup.centralizer (ψ.range : Set G) = ⊥ := by
    rw [hrange]
    exact s1.1
  set πe := MulEquiv.ofBijective π hπ with hπe
  set φ : ↥(orthDerived Q) →* G :=
    ψ.comp (πe.symm.toMonoidHom.comp (matrixDerivedEquiv Q).symm.toMonoidHom) with hφ
  have hφinj : Function.Injective φ :=
    hψ.comp (πe.symm.injective.comp (matrixDerivedEquiv Q).symm.injective)
  have hφr : φ.range = ψ.range := by
    ext y
    constructor
    · rintro ⟨X, rfl⟩
      exact ⟨_, rfl⟩
    · rintro ⟨u, rfl⟩
      exact ⟨matrixDerivedEquiv Q (πe u), by simp [hφ]⟩
  have hG₀ : φ.range = ggG0 p B x L D J := hφr.trans hrange
  have hBφ : Bs ≤ φ.range := by
    intro b hb
    obtain ⟨g, hg, hbg⟩ := hdiag b hb
    rw [hC, Subgroup.mem_bot] at hbg
    rw [hφr, eq_inv_of_mul_eq_one_left hbg]
    exact ψ.range.inv_mem hg
  have hBs := hctx.bstar
  obtain ⟨r, ι, hιinj, hιrange, hmove, hcomp, hshape⟩ :=
    hcoord G (GaloisField 2 f) (Fin d → GaloisField 2 f) p hp2 Q hnd hT φ hφinj Bs hBφ hBs.2.1
      hctx.pow_four_le_card_bstar (fun g hg hgp => hBs.2.2.2 g (Subgroup.mem_inf.mp hg).2 hgp)
  refine ⟨r, CoordSpNs.galSigns p (Nat.card (GaloisField 2 f)), ι,
    ⟨hιinj, hιrange, fun π η hη hprod => ?_, fun hr1 => ?_, fun b L₁ hpair β hβ => ?_⟩⟩
  ·
    obtain ⟨w, hw, hws⟩ := hmove π η hη hprod
    exact ⟨w, hG₀ ▸ hw, hws⟩
  ·
    have hr4 : 4 ≤ r := hctx.four_le_of_range_eq hιrange
    have hrp : p + 1 ≤ r := StepTwoToral.succ_le_of_natCast_sub_one_eq_zero hr1 (by omega)
    have hDB : D ≤ ι.range := by
      rw [hιrange]
      exact hctx.d_le_bstar
    have hJ := hctx.j_isComponentOf_inf
    rw [← hG₀] at hJ
    exact StepTwoToral.contrary_of_coordShape hDB hctx.card_d le_rfl
      (CoordSpNs.neg_one_mem_galSigns _ _) (CoordSpNs.neg_one_ne_one hp2) hrp
      (hshape D J hctx.d_le_bstar hJ hctx.card_bstar_inf_centralizer_le)
  ·
    obtain ⟨hb, hb1, hcomp', hcard⟩ := hpair
    rw [← hG₀] at hcomp'
    exact hcomp b L₁ hb hb1 hcomp' hcard β hβ

end CoordOm

section Reduction

theorem ggStepTwoCoordModelOn_POmegaPlus_of_coord (hcoord : GGOmCoordInput) :
    GGStepTwoCoordModelOn .POmegaPlus := by
  intro G _ _ p B Bs x L D J n f
  by_cases hn : 3 ≤ n
  · rw [ggU_POmegaPlus_eq hn]
    intro ψ hctx s1 _
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨-, hker⟩ := hctx.2.2.2.2.1
    have hψinj : Function.Injective ψ := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff,
        ← RootCentOmega.center_spinGroup_quadPlus_eq_bot_charTwo hn]
      exact hker
    obtain ⟨hnd, hT⟩ := regular_coordinateQuadPlus n (GaloisField 2 f) hn
    exact CoordOm.coordModel_of_model hcoord hctx s1 hnd hT hψinj (AutOm.spinModelPlus hn)
      ⟨AutOm.spinModelPlus_injective hn, AutOm.spinModelPlus_surjective hn⟩
      (fun b hb => PsiDiag.SpinP.exists_mem_centralizer hn ψ hker (hctx.2.2.2.2.2.2.1.2 b hb))
  · intro ψ hctx
    exact absurd hctx.2.2.2.1.1.2.2 (by omega)

theorem ggStepTwoCoordModelOn_POmegaMinus_of_coord (hcoord : GGOmCoordInput) :
    GGStepTwoCoordModelOn .POmegaMinus := by
  intro G _ _ p B Bs x L D J n f
  rw [show ggU .POmegaMinus n f = ⟨spinGroup (quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1
      (minusCoeffs 2 f).2), Spin.Twisted.minusDatum n (minusCoeffs_irr 2 f)⟩ from rfl]
  intro ψ hctx s1 _
  have hn : 4 ≤ n := hctx.2.2.2.1.1.2.2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hirr := minusCoeffs_irr 2 f
  obtain ⟨-, hker⟩ := hctx.2.2.2.2.1
  have hψinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff, ← PsiDiag.SpinM.center_eq_bot hirr hn]
    exact hker
  obtain ⟨hnd, hT⟩ := regular_coordinateQuadMinus n (GaloisField 2 f) _ _ hn hirr
  exact CoordOm.coordModel_of_model hcoord hctx s1 hnd hT hψinj (AutOm.spinModelMinus hn hirr)
    ⟨AutOm.spinModelMinus_injective hn hirr, AutOm.spinModelMinus_surjective hn hirr⟩
    (fun b hb => PsiDiag.SpinM.exists_mem_centralizer hirr hn ψ hker
      (hctx.2.2.2.2.2.2.1.2 b hb))

theorem ggStepTwoToralWitnessOn_POmegaPlus_of_coord (hcoord : GGOmCoordInput) :
    GGStepTwoToralWitnessOn .POmegaPlus :=
  ggStepTwoToralWitnessOn_of_coordModel (ggStepTwoCoordModelOn_POmegaPlus_of_coord hcoord)

theorem ggStepTwoToralWitnessOn_POmegaMinus_of_coord (hcoord : GGOmCoordInput) :
    GGStepTwoToralWitnessOn .POmegaMinus :=
  ggStepTwoToralWitnessOn_of_coordModel (ggStepTwoCoordModelOn_POmegaMinus_of_coord hcoord)

end Reduction

end CFSG.StandardType
