module

public import CFSG.LocalAnalysis.StandardType.GGRootPlaneOmModel
public import CFSG.LocalAnalysis.StandardType.GGRootPlaneOmEight
public import CFSG.LocalAnalysis.StandardType.GGRootPlaneRest
public import CFSG.LocalAnalysis.StandardType.GGSpNonsplitComp
public import CFSG.LocalAnalysis.StandardType.GGSpNonsplitFrame
public import CFSG.LocalAnalysis.StandardType.GGSixAutSteinbergOmegaPlusFour
public import CFSG.LocalAnalysis.StandardType.GGPsiDiagInnerSpin
public import CFSG.LocalAnalysis.StandardType.GGPsiDiagInnerMinus
public import CFSG.LocalAnalysis.StandardType.GGRootInvolutionCore
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataCoordinateRegular

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData

@[expose] def GGPOmegaPlusD4 (t : StatedLieTag) (n f p : ℕ) : Prop :=
  t = .POmegaPlus ∧ n = 4 ∧ (2 ^ f) ^ 2 ≡ 1 [MOD p]

@[expose] def GGPOmegaMinusD4 (t : StatedLieTag) (n _f _p : ℕ) : Prop :=
  t = .POmegaMinus ∧ n = 4

section D4Input

@[expose] def GGRootPlaneD4Input : Prop :=
  GGRootPlaneInputOn GGPOmegaPlusD4

end D4Input

section Helpers

theorem ggSixCtxV2_card_bstar {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {U : Type} [Group U] {Δ : UniversalRootDatum U} {t : StatedLieTag}
    {n f : ℕ} {ψ : U →* G} (hctx : GGSixCtxV2 p B Bs x L D J Δ t n f ψ) :
    p ^ 4 ≤ Nat.card Bs := by
  have hβ := hctx.1.2.2.2.2.2.1
  have hp : p.Prime := hβ.1
  have hm4 : 4 ≤ LargeEvenTwoLocalRank p G := hβ.2.2.2
  have hBcard : Nat.card B = p ^ LargeEvenTwoLocalRank p G := hctx.1.2.2.2.2.2.2.1.1.2.1
  calc p ^ 4 ≤ p ^ LargeEvenTwoLocalRank p G := Nat.pow_le_pow_right hp.pos hm4
    _ = Nat.card B := hBcard.symm
    _ ≤ Nat.card Bs := Subgroup.card_le_of_le hctx.2.1.1

theorem bstar_le_range_of_inner {G : Type} [Group G] {U : Type} [Group U] {ψ : U →* G}
    {Bs : Subgroup G} (hC : Subgroup.centralizer (ψ.range : Set G) = ⊥)
    (hdiag : ∀ b ∈ Bs, ∃ g ∈ ψ.range, b * g ∈ Subgroup.centralizer (ψ.range : Set G)) :
    Bs ≤ ψ.range := by
  intro b hb
  obtain ⟨g, hg, hbg⟩ := hdiag b hb
  rw [hC, Subgroup.mem_bot] at hbg
  rw [eq_inv_of_mul_eq_one_left hbg]
  exact inv_mem hg

end Helpers

section Tags

theorem ggRootPlaneInputOn_POmegaPlusLarge :
    GGRootPlaneInputOn fun t n _ _ => t = .POmegaPlus ∧ 5 ≤ n := by
  intro G _ _ p B Bs x L D J t n f ψ hP
  obtain ⟨rfl, hn5⟩ := hP
  have hn : 3 ≤ n := by omega
  revert ψ
  rw [ggU_POmegaPlus_eq hn]
  intro ψ hctx s1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : p.Prime := hctx.1.2.2.2.2.2.1.1
  have hp2 : p ≠ 2 := hctx.1.2.2.2.2.2.1.2.1
  obtain ⟨hrange, hker⟩ := hctx.2.2.2.2.1
  have hψinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff,
      ← RootCentOmega.center_spinGroup_quadPlus_eq_bot_charTwo hn]
    exact hker
  have hC : Subgroup.centralizer (ψ.range : Set G) = ⊥ := by
    rw [hrange]
    exact s1.1
  have hBψ : Bs ≤ ψ.range := bstar_le_range_of_inner hC fun b hb =>
    PsiDiag.SpinP.exists_mem_centralizer hn ψ hker (hctx.2.2.2.2.2.2.1.2 b hb)
  obtain ⟨hnd, hT⟩ := regular_coordinateQuadPlus n (GaloisField 2 f) hn
  obtain ⟨γ, hγ, -⟩ := exists_maxHeight (D := plusDatum n (GaloisField 2 f) hn)
    (show 0 < n by omega)
  obtain ⟨i, j, hij, s, t, -, hγX⟩ := exists_plusRootGroup_eq (K := GaloisField 2 f) hn hγ
  obtain ⟨E, u, hEB, hEel, hEcard, hcent, hord, hcomp⟩ := RootPlaneOm.exists_rootPlane_spin
    (plusIndexEquiv n) (AutOm.range_spinMatrix_plus hn)
    ⟨AutOm.spinModelPlus_injective hn, AutOm.spinModelPlus_surjective hn⟩ hnd hT (by omega)
    (plusFrame n (GaloisField 2 f) hn) hij s t hψinj hp hp2 hctx.2.1.2.1 hctx.2.1.2.2.2
    (ggSixCtxV2_card_bstar hctx) hBψ
  have hX : (plusDatum n (GaloisField 2 f) hn).rootGroup γ =
      ((plusFrame n (GaloisField 2 f) hn).longRoot hij s t).range := hγX
  refine ⟨E, γ, u, ψ (u * (plusFrame n (GaloisField 2 f) hn).longRoot hij s t (.ofAdd 1) * u⁻¹),
    hEB, hEel, hEcard, ⟨hγ, fun h => ?_⟩, ?_, ?_, hord, ?_⟩
  · rcases h with h | h | h <;> exact absurd h (by decide)
  · change E ≤ Subgroup.centralizer (((((plusDatum n (GaloisField 2 f) hn).rootGroup γ).map
      (MulAut.conj u).toMonoidHom).map ψ : Subgroup G) : Set G)
    rw [hX]
    exact hcent
  · change _ ∈ (((plusDatum n (GaloisField 2 f) hn).rootGroup γ).map
      (MulAut.conj u).toMonoidHom).map ψ
    rw [hX]
    exact ⟨_, ⟨_, ⟨.ofAdd 1, rfl⟩, rfl⟩, rfl⟩
  · intro e he he1
    obtain ⟨L₁, hL₁, hL₁c⟩ := hcomp e he he1
    exact Or.inr ⟨L₁, hrange ▸ hL₁, hL₁c⟩

theorem ggRootPlaneInputOn_POmegaMinusLarge :
    GGRootPlaneInputOn fun t n _ _ => t = .POmegaMinus ∧ 5 ≤ n := by
  intro G _ _ p B Bs x L D J t n f ψ hP
  obtain ⟨rfl, hn5⟩ := hP
  have hn : 4 ≤ n := by omega
  revert ψ
  rw [show ggU .POmegaMinus n f = ⟨spinGroup (quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1
      (minusCoeffs 2 f).2), Spin.Twisted.minusDatum n (minusCoeffs_irr 2 f)⟩ from rfl]
  intro ψ hctx s1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hirr := minusCoeffs_irr 2 f
  have hp : p.Prime := hctx.1.2.2.2.2.2.1.1
  have hp2 : p ≠ 2 := hctx.1.2.2.2.2.2.1.2.1
  obtain ⟨hrange, hker⟩ := hctx.2.2.2.2.1
  have hψinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff, ← PsiDiag.SpinM.center_eq_bot hirr hn]
    exact hker
  have hC : Subgroup.centralizer (ψ.range : Set G) = ⊥ := by
    rw [hrange]
    exact s1.1
  have hBψ : Bs ≤ ψ.range := bstar_le_range_of_inner hC fun b hb =>
    PsiDiag.SpinM.exists_mem_centralizer hirr hn ψ hker (hctx.2.2.2.2.2.2.1.2 b hb)
  obtain ⟨hnd, hT⟩ := regular_coordinateQuadMinus n (GaloisField 2 f) _ _ hn hirr
  obtain ⟨γ, hγ, hmax⟩ := exists_maxHeight (D := minusDatum n hirr) (show 0 < n - 1 by omega)
  have hlong : GGLongRoot (minusDatum n hirr) γ :=
    ⟨1, γ, hγ, hmax, by rw [map_one, Module.End.one_apply]⟩
  obtain ⟨i, j, hij, s, t, hst⟩ := RootCentOmega.exists_long_of_ggLongRoot_minus hirr hn hlong
  have hX : (minusDatum n hirr).rootGroup γ =
      ((minusFrame n (minusCoeffs 2 f).1 (minusCoeffs 2 f).2).longRoot hij s t).range :=
    minusRootGroup_eq_long n hirr hij s t hst
  obtain ⟨E, u, hEB, hEel, hEcard, hcent, hord, hcomp⟩ := RootPlaneOm.exists_rootPlane_spin
    (minusIndexEquiv n (by omega)) (AutOm.range_spinMatrix_minus hn hirr)
    ⟨AutOm.spinModelMinus_injective hn hirr, AutOm.spinModelMinus_surjective hn hirr⟩ hnd hT
    (by omega) (minusFrame n (minusCoeffs 2 f).1 (minusCoeffs 2 f).2).toHypFrame hij s t hψinj
    hp hp2 hctx.2.1.2.1 hctx.2.1.2.2.2 (ggSixCtxV2_card_bstar hctx) hBψ
  refine ⟨E, γ, u, ψ (u * (minusFrame n (minusCoeffs 2 f).1 (minusCoeffs 2 f).2).longRoot hij s t
    (.ofAdd 1) * u⁻¹), hEB, hEel, hEcard, ⟨hγ, fun _ => hlong⟩, ?_, ?_, hord, ?_⟩
  · change E ≤ Subgroup.centralizer (((((minusDatum n hirr).rootGroup γ).map
      (MulAut.conj u).toMonoidHom).map ψ : Subgroup G) : Set G)
    rw [hX]
    exact hcent
  · change _ ∈ (((minusDatum n hirr).rootGroup γ).map (MulAut.conj u).toMonoidHom).map ψ
    rw [hX]
    exact ⟨_, ⟨_, ⟨.ofAdd 1, rfl⟩, rfl⟩, rfl⟩
  · intro e he he1
    obtain ⟨L₁, hL₁, hL₁c⟩ := hcomp e he he1
    exact Or.inr ⟨L₁, hrange ▸ hL₁, hL₁c⟩

theorem ggRootPlaneInputOn_POmegaPlusFourNonsplit :
    GGRootPlaneInputOn fun t n f p => t = .POmegaPlus ∧ n = 4 ∧ ¬ (2 ^ f) ^ 2 ≡ 1 [MOD p] := by
  intro G _ _ p B Bs x L D J t n f ψ hP
  obtain ⟨rfl, rfl, hq⟩ := hP
  revert ψ
  rw [ggU_POmegaPlus_eq (by norm_num : 3 ≤ 4)]
  intro ψ hctx s1
  exfalso
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : p.Prime := hctx.1.2.2.2.2.2.1.1
  have hp2 : p ≠ 2 := hctx.1.2.2.2.2.2.1.2.1
  have hf : 1 ≤ f := hctx.2.2.2.1.1.2.1
  obtain ⟨hrange, hker⟩ := hctx.2.2.2.2.1
  have hψinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff,
      ← RootCentOmega.center_spinGroup_quadPlus_eq_bot_charTwo (by norm_num : 3 ≤ 4)]
    exact hker
  have hC : Subgroup.centralizer (ψ.range : Set G) = ⊥ := by
    rw [hrange]
    exact s1.1
  have hBψ : Bs ≤ ψ.range := bstar_le_range_of_inner hC fun b hb =>
    PsiDiag.SpinP.exists_mem_centralizer (by norm_num) ψ hker (hctx.2.2.2.2.2.2.1.2 b hb)
  obtain ⟨hnd, hT⟩ := regular_coordinateQuadPlus 4 (GaloisField 2 f) (by norm_num)
  obtain ⟨A, hA, hcardA⟩ := RootPlaneOm.exists_genMax_spin (plusIndexEquiv 4)
    (AutOm.range_spinMatrix_plus (by norm_num))
    ⟨AutOm.spinModelPlus_injective (by norm_num), AutOm.spinModelPlus_surjective (by norm_num)⟩
    hnd hT hψinj hp hp2 hctx.2.1.2.1 hctx.2.1.2.2.2 hBψ
  have h := (RootPlaneOm.eight_facts (Q := coordinateQuadPlus 4 (GaloisField 2 f)) hnd
    (by norm_num) hA (hcardA ▸ ggSixCtxV2_card_bstar hctx)).1
  rw [GaloisField.card 2 f (by omega)] at h
  exact hq h

theorem ggRootPlaneInputOn_POmegaMinusD4 : GGRootPlaneInputOn GGPOmegaMinusD4 := by
  intro G _ _ p B Bs x L D J t n f ψ hP
  obtain ⟨rfl, rfl⟩ := hP
  revert ψ
  rw [show ggU .POmegaMinus 4 f = ⟨spinGroup (quadMinus 4 (GaloisField 2 f) (minusCoeffs 2 f).1
      (minusCoeffs 2 f).2), Spin.Twisted.minusDatum 4 (minusCoeffs_irr 2 f)⟩ from rfl]
  intro ψ hctx s1
  exfalso
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hirr := minusCoeffs_irr 2 f
  have hp : p.Prime := hctx.1.2.2.2.2.2.1.1
  have hp2 : p ≠ 2 := hctx.1.2.2.2.2.2.1.2.1
  obtain ⟨hrange, hker⟩ := hctx.2.2.2.2.1
  have hψinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff, ← PsiDiag.SpinM.center_eq_bot hirr le_rfl]
    exact hker
  have hC : Subgroup.centralizer (ψ.range : Set G) = ⊥ := by
    rw [hrange]
    exact s1.1
  have hBψ : Bs ≤ ψ.range := bstar_le_range_of_inner hC fun b hb =>
    PsiDiag.SpinM.exists_mem_centralizer hirr le_rfl ψ hker (hctx.2.2.2.2.2.2.1.2 b hb)
  obtain ⟨hnd, hT⟩ := regular_coordinateQuadMinus 4 (GaloisField 2 f) _ _ le_rfl hirr
  obtain ⟨A, hA, hcardA⟩ := RootPlaneOm.exists_genMax_spin (minusIndexEquiv 4 (by norm_num))
    (AutOm.range_spinMatrix_minus le_rfl hirr)
    ⟨AutOm.spinModelMinus_injective le_rfl hirr, AutOm.spinModelMinus_surjective le_rfl hirr⟩
    hnd hT hψinj hp hp2 hctx.2.1.2.1 hctx.2.1.2.2.2 hBψ
  exact RootPlaneOm.not_le_card_of_minus_eight hirr hA (hcardA ▸ ggSixCtxV2_card_bstar hctx)

theorem ggRootPlaneAt_POmegaPlus_of_d4 (hD4 : GGRootPlaneD4Input) :
    GGRootPlaneAt .POmegaPlus := by
  intro G _ _ p B Bs x L D J t n f ψ ht hctx s1
  subst ht
  by_cases hn : 5 ≤ n
  · exact ggRootPlaneInputOn_POmegaPlusLarge G p B Bs x L D J .POmegaPlus n f ψ ⟨rfl, hn⟩ hctx s1
  · have hn4 : 4 ≤ n := hctx.2.2.2.1.1.2.2
    have hn4' : n = 4 := by omega
    by_cases hq : (2 ^ f) ^ 2 ≡ 1 [MOD p]
    · exact hD4 G p B Bs x L D J .POmegaPlus n f ψ ⟨rfl, hn4', hq⟩ hctx s1
    · exact ggRootPlaneInputOn_POmegaPlusFourNonsplit G p B Bs x L D J .POmegaPlus n f ψ
        ⟨rfl, hn4', hq⟩ hctx s1

theorem ggRootPlaneAt_POmegaMinus : GGRootPlaneAt .POmegaMinus := by
  intro G _ _ p B Bs x L D J t n f ψ ht hctx s1
  subst ht
  by_cases hn : 5 ≤ n
  · exact ggRootPlaneInputOn_POmegaMinusLarge G p B Bs x L D J .POmegaMinus n f ψ ⟨rfl, hn⟩ hctx
      s1
  · have hn4 : 4 ≤ n := hctx.2.2.2.1.1.2.2
    exact ggRootPlaneInputOn_POmegaMinusD4 G p B Bs x L D J .POmegaMinus n f ψ ⟨rfl, by omega⟩
      hctx s1


@[expose] def GGRootPlaneRestD4Exc : Prop :=
  GGRootPlaneD4Input ∧ GGRootPlaneAt .F4 ∧ GGRootPlaneAt .E6 ∧
    GGRootPlaneAt .E7 ∧ GGRootPlaneAt .E8 ∧ GGRootPlaneAt .twistedE6

theorem ggRootPlaneRestOmegaExc_of_d4Exc (h : GGRootPlaneRestD4Exc) :
    GGRootPlaneRestOmegaExc := by
  obtain ⟨hD4, hF4, hE6, hE7, hE8, hTwE6⟩ := h
  exact ⟨ggRootPlaneAt_POmegaPlus_of_d4 hD4, ggRootPlaneAt_POmegaMinus, hF4, hE6, hE7, hE8, hTwE6⟩

theorem ggRootPlaneInput_of_d4Exc (h : GGRootPlaneRestD4Exc) : GGRootPlaneInput :=
  ggRootPlaneInput_of_frame_comp ggSpNonsplitFrameInput_holds ggSpNonsplitCompInput_holds
    (ggRootPlaneRestOmegaExc_of_d4Exc h)

end Tags

end CFSG.StandardType
