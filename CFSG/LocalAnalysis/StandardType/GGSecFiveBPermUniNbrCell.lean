module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermUniNbrLabel
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165OmFam
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166FamB
import CFSG.LieType.Steinberg.CentralExt.OrthogonalTwoMultiplier
import CFSG.GroupTheory.CentralizerSup
import CFSG.GroupTheory.PLayer.PIndex
import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8ExcAction
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165OmDefs
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBExcE
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15ACoreArith
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15ACorePerm
import CFSG.LocalAnalysis.SeitzReduction.F4PilotUniqueStep3Basic
import CFSG.Quasithin.Background.F918D5

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal

private theorem gcd_four_of_odd {n : ℕ} (hn : Odd n) : Nat.gcd 4 n = 1 := by
  have h : Nat.Coprime 4 n := by
    simpa using (Nat.coprime_two_left.mpr hn).pow_left 2
  exact h.gcd_eq_one

private noncomputable def statedOmegaMinusCongr {K L : Type} [Field K] [Field L]
    (e : K ≃+* L) {m : ℕ} {b c : K} {b' c' : L} (hb : e b = b') (hc : e c = c') :
    StatedOmega (StatedQuadMinus m K b c) ≃* StatedOmega (StatedQuadMinus m L b' c') :=
  ((CFSG.Adapters.RankTwoModelTransports.glCongr
      (ι := Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) e).subgroupMap
    (StatedOmega (StatedQuadMinus m K b c))).trans
    (MulEquiv.subgroupCongr (CFSG.ClassicalInvolution.Upgrade.map_statedOmega e
      (CFSG.ClassicalInvolution.Upgrade.statedQuadMinus_comp e hb hc)))

private theorem center_eq_bot_of_psp_model {K : Type} [Group K] [Finite K]
    (hY : CFSG.IsQuasisimple K) {m f : ℕ} (hm2 : 2 ≤ m) (hmf : m ≤ 3 → 2 ≤ f)
    (hf : 1 ≤ f) (hmod : StatedClassicalModel (K ⧸ Subgroup.center K) .PSp m 2 f) :
    Subgroup.center K = ⊥ := by
  obtain ⟨-, F, hfield, hfinite, hFcard, ⟨e⟩⟩ := hmod
  let : Field F := hfield
  let : Finite F := hfinite
  have : Fintype F := Fintype.ofFinite F
  have : CharP F 2 :=
    CFSG.ABGLocalTools.SL2Facts.charP_of_card_eq_prime_pow Nat.prime_two hFcard
  have hmult1 : Nat.card (CFSG.Open.griessHopfMultiplier (StatedProj (StatedSp m F))) = 1 := by
    obtain ⟨-, ⟨eM⟩⟩ := CFSG.LieType.Steinberg.CentralExt.SpClosed.psp_even_hopfMultiplier
      (K := F) (n := m) (f := f) hFcard hf hm2 hmf
    rw [Nat.card_congr eM.toEquiv,
      Nat.card_congr (Multiplicative.toAdd :
        Multiplicative (ZMod (Nat.gcd 2 (Nat.card F - 1))) ≃ ZMod (Nat.gcd 2 (Nat.card F - 1))),
      Nat.card_zmod]
    have hodd : Odd (2 ^ f - 1) := by
      have h2even : Even (2 ^ f) := even_iff_two_dvd.mpr (dvd_pow_self 2 (by omega))
      have hpos : 1 ≤ 2 ^ f := Nat.one_le_two_pow
      exact Nat.Even.sub_odd hpos h2even odd_one
    have hg : Nat.gcd 2 (Nat.card F - 1) = 1 := by
      rw [hFcard]
      exact Nat.coprime_two_left.2 hodd
    rw [hg]
  have : Finite (CFSG.Open.griessHopfMultiplier (StatedProj (StatedSp m F))) :=
    Nat.finite_of_card_ne_zero (by rw [hmult1]; norm_num)
  have hdvd := CFSG.GH74.GLS.Stage2.Signalizer.Odd87.card_center_dvd_hopf hY e
  rw [hmult1] at hdvd
  exact Subgroup.card_eq_one.mp (Nat.dvd_one.mp hdvd)

private theorem center_eq_bot_of_pomegaPlus_model {K : Type} [Group K] [Finite K]
    (hY : CFSG.IsQuasisimple K) {n f : ℕ} (hn : 4 ≤ n) (hf : 1 ≤ f) (hnf : n = 4 → 2 ≤ f)
    (hmod : StatedClassicalModel (K ⧸ Subgroup.center K) .POmegaPlus n 2 f) :
    Subgroup.center K = ⊥ := by
  obtain ⟨-, F, hfield, hfinite, hFcard, ⟨e⟩⟩ := hmod
  let : Field F := hfield
  let : Finite F := hfinite
  have hmult1 : Nat.card (CFSG.Open.griessHopfMultiplier
      (StatedProj (StatedOmega (StatedQuadPlus n F)))) = 1 := by
    rcases Nat.lt_or_ge f 2 with hlt | hge
    · have hf1 : f = 1 := by omega
      have hn5 : 5 ≤ n := by
        by_contra h
        exact absurd (hnf (by omega)) (by omega)
      have hK2 : Nat.card F = 2 := by rw [hFcard, hf1]; norm_num
      obtain ⟨-, ⟨eM⟩⟩ :=
        CFSG.LieType.Steinberg.CentralExt.OrthogonalTwo.pomegaPlus_two_hopfMultiplier
          (n := n) (K := F) (p := 2) (f := f) hn5 hFcard hK2
      rw [Nat.card_congr eM.toEquiv]
      have hev : Even (2 ^ f) := Nat.even_pow.2 ⟨even_two, by omega⟩
      simp [CFSG.Blueprint.Multiplier.generic, CFSG.Blueprint.Multiplier.genericOrders, hev]
    · have hF4 : 4 ≤ Nat.card F := by
        rw [hFcard]
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hge
      obtain ⟨-, ⟨eM⟩⟩ :=
        CFSG.LieType.Steinberg.CentralExt.SpinPlusClosed.pomegaPlus_hopfMultiplier
          (n := n) (K := F) (p := 2) (f := f) (by omega) hFcard hF4
      rw [Nat.card_congr eM.toEquiv]
      have hev : Even (2 ^ f) := Nat.even_pow.2 ⟨even_two, by omega⟩
      simp [CFSG.Blueprint.Multiplier.generic, CFSG.Blueprint.Multiplier.genericOrders, hev]
  have : Finite (CFSG.Open.griessHopfMultiplier
      (StatedProj (StatedOmega (StatedQuadPlus n F)))) :=
    Nat.finite_of_card_ne_zero (by rw [hmult1]; norm_num)
  have hdvd := CFSG.GH74.GLS.Stage2.Signalizer.Odd87.card_center_dvd_hopf hY e
  rw [hmult1] at hdvd
  exact Subgroup.card_eq_one.mp (Nat.dvd_one.mp hdvd)

private theorem center_eq_bot_of_pomegaMinus_model {K : Type} [Group K] [Finite K]
    (hY : CFSG.IsQuasisimple K) {n f : ℕ} (hn : 4 ≤ n) (hf : 1 ≤ f)
    (hmod : StatedClassicalModel (K ⧸ Subgroup.center K) .POmegaMinus n 2 f) :
    Subgroup.center K = ⊥ := by
  obtain ⟨-, F, hfield, hfinite, hFcard, b, c, hirr, ⟨e⟩⟩ := hmod
  let : Field F := hfield
  let : Finite F := hfinite
  have heM : Nonempty (CFSG.Open.griessHopfMultiplier
      (StatedProj (StatedOmega (StatedQuadMinus n F b c))) ≃*
        Multiplicative (ZMod (Nat.gcd 4 ((2 ^ f) ^ n + 1)))) := by
    rcases Nat.lt_or_ge f 2 with hlt | hge
    · have hf1 : f = 1 := by omega
      have hK2 : Nat.card F = 2 := by rw [hFcard, hf1]; norm_num
      exact (CFSG.LieType.Steinberg.CentralExt.OrthogonalTwo.pomegaMinus_two_hopfMultiplier
        (n := n) (K := F) (b := b) (c := c) (p := 2) (f := f) hn hirr hFcard hK2).2
    · have hF4 : 4 ≤ Nat.card F := by
        rw [hFcard]
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hge
      exact (CFSG.LieType.Steinberg.CentralExt.SpinMinusClosed.pomegaMinus_hopfMultiplier
        (n := n) (K := F) (b := b) (c := c) hn hirr (p := 2) (f := f) hFcard hF4).2
  have hmult1 : Nat.card (CFSG.Open.griessHopfMultiplier
      (StatedProj (StatedOmega (StatedQuadMinus n F b c)))) = 1 := by
    obtain ⟨eM⟩ := heM
    rw [Nat.card_congr eM.toEquiv,
      Nat.card_congr (Multiplicative.toAdd :
        Multiplicative (ZMod (Nat.gcd 4 ((2 ^ f) ^ n + 1))) ≃
          ZMod (Nat.gcd 4 ((2 ^ f) ^ n + 1))),
      Nat.card_zmod]
    have heven : Even ((2 ^ f) ^ n) := by
      rw [← pow_mul]
      exact even_iff_two_dvd.mpr (dvd_pow_self 2
        (Nat.mul_ne_zero (by omega) (by omega)))
    exact gcd_four_of_odd (Even.add_one heven)
  have : Finite (CFSG.Open.griessHopfMultiplier
      (StatedProj (StatedOmega (StatedQuadMinus n F b c)))) :=
    Nat.finite_of_card_ne_zero (by rw [hmult1]; norm_num)
  have hdvd := CFSG.GH74.GLS.Stage2.Signalizer.Odd87.card_center_dvd_hopf hY e
  rw [hmult1] at hdvd
  exact Subgroup.card_eq_one.mp (Nat.dvd_one.mp hdvd)

private theorem sp_iso_of_hasLabel_B {K : Type} [Group K] [Finite K]
    (hY : CFSG.IsQuasisimple K) {n f : ℕ} (hn : 4 ≤ n) (hf : 1 ≤ f) (hnf : n = 4 → 2 ≤ f)
    (hmark : CFSG.LocalAnalysis.GLTheoremA.Y10F.HasLabel K
      (· = (⟨.B, n - 1, f⟩ : LargeEvenLabel))) :
    Nonempty (K ≃* StatedSp (n - 1) (GaloisField 2 f)) := by
  obtain ⟨-, -, hM⟩ := CFSG.LocalAnalysis.GLTheoremA.quasisimple_markedModel_of_isLabel hmark
  have hM' : CFSG.Blueprint.LieModel (K ⧸ Subgroup.center K) .PSp (n - 1) 2 f := hM
  have hmod : StatedClassicalModel (K ⧸ Subgroup.center K) .PSp (n - 1) 2 f :=
    hM'.statedClassicalModel (by decide)
  have hZ : Subgroup.center K = ⊥ :=
    center_eq_bot_of_psp_model hY (m := n - 1) (f := f) (by omega) (fun h => hnf (by omega))
      hf hmod
  obtain ⟨F', hfield, hfinite, hchar, hF'card, ⟨eSp⟩⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.Y10F.exists_mulEquiv_statedSp_of_isLabel
      (K := K) (N := n - 1) (n := f) hmark hZ
  let : Fintype F' := Fintype.ofFinite F'
  let : Fintype (GaloisField 2 f) := Fintype.ofFinite _
  have hcardF : Fintype.card F' = Fintype.card (GaloisField 2 f) := by
    rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card, hF'card,
      GaloisField.card 2 f (by omega)]
  let ε : F' ≃+* GaloisField 2 f := FiniteField.ringEquivOfCardEq hcardF
  exact ⟨eSp.trans
    (CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.statedSpCongr ε (n - 1))⟩

private theorem omPlus_iso_of_hasLabel_D {K : Type} [Group K] [Finite K]
    (hY : CFSG.IsQuasisimple K) {n f : ℕ} (hn : 4 ≤ n) (hf : 1 ≤ f) (hnf : n = 4 → 2 ≤ f)
    (hmark : CFSG.LocalAnalysis.GLTheoremA.Y10F.HasLabel K
      (· = (⟨.D, n, f⟩ : LargeEvenLabel))) :
    Nonempty (K ≃* StatedOmega (StatedQuadPlus n (GaloisField 2 f))) := by
  obtain ⟨-, -, hM⟩ := CFSG.LocalAnalysis.GLTheoremA.quasisimple_markedModel_of_isLabel hmark
  have hM' : CFSG.Blueprint.LieModel (K ⧸ Subgroup.center K) .POmegaPlus n 2 f := by
    simpa [CFSG.StandardType.MarkedModel, CFSG.StandardType.markTag, CFSG.StandardType.markRank,
      CFSG.StandardType.markChar, CFSG.StandardType.markDeg, if_neg (by omega : n ≠ 3)] using hM
  have hmod : StatedClassicalModel (K ⧸ Subgroup.center K) .POmegaPlus n 2 f :=
    hM'.statedClassicalModel (by decide)
  have hZ : Subgroup.center K = ⊥ := center_eq_bot_of_pomegaPlus_model hY hn hf hnf hmod
  obtain ⟨F', hfield, hfinite, hchar, hF'card, ⟨eOm⟩⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.Y10F.exists_mulEquiv_statedOmega_plus_of_hasLabel
      (K := K) (ℓ := n) (n := f) (by omega) hmark hZ
  let : Fintype F' := Fintype.ofFinite F'
  let : Fintype (GaloisField 2 f) := Fintype.ofFinite _
  have hcardF : Fintype.card F' = Fintype.card (GaloisField 2 f) := by
    rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card, hF'card,
      GaloisField.card 2 f (by omega)]
  let ε : F' ≃+* GaloisField 2 f := FiniteField.ringEquivOfCardEq hcardF
  exact ⟨eOm.trans (CFSG.SeitzReduction.OmegaPilot.statedOmegaPlusCongr ε n)⟩

private theorem omMinus_iso_of_hasLabel_twD {K : Type} [Group K] [Finite K]
    (hY : CFSG.IsQuasisimple K) {n f : ℕ} (hn : 4 ≤ n) (hf : 1 ≤ f)
    (hmark : CFSG.LocalAnalysis.GLTheoremA.Y10F.HasLabel K
      (· = (⟨.twD, n, f⟩ : LargeEvenLabel))) :
    ∃ b c : GaloisField 2 f, (∀ s : GaloisField 2 f, s ^ 2 + b * s + c ≠ 0) ∧
      Nonempty (K ≃* StatedOmega (StatedQuadMinus n (GaloisField 2 f) b c)) := by
  obtain ⟨-, -, hM⟩ := CFSG.LocalAnalysis.GLTheoremA.quasisimple_markedModel_of_isLabel hmark
  have hM' : CFSG.Blueprint.LieModel (K ⧸ Subgroup.center K) .POmegaMinus n 2 f := by
    simpa [CFSG.StandardType.MarkedModel, CFSG.StandardType.markTag, CFSG.StandardType.markRank,
      CFSG.StandardType.markChar, CFSG.StandardType.markDeg,
      if_neg (by omega : n ≠ 2), if_neg (by omega : n ≠ 3)] using hM
  have hmod : StatedClassicalModel (K ⧸ Subgroup.center K) .POmegaMinus n 2 f :=
    hM'.statedClassicalModel (by decide)
  have hZ : Subgroup.center K = ⊥ := center_eq_bot_of_pomegaMinus_model hY hn hf hmod
  obtain ⟨F', hfield, hfinite, hchar, b, c, hF'card, hirr, ⟨eOm⟩⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.Y10F.exists_mulEquiv_statedOmega_minus_of_hasLabel
      (K := K) (ℓ := n) (n := f) (by omega) hmark hZ
  let : Fintype F' := Fintype.ofFinite F'
  let : Fintype (GaloisField 2 f) := Fintype.ofFinite _
  have hcardF : Fintype.card F' = Fintype.card (GaloisField 2 f) := by
    rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card, hF'card,
      GaloisField.card 2 f (by omega)]
  let ε : F' ≃+* GaloisField 2 f := FiniteField.ringEquivOfCardEq hcardF
  refine ⟨ε b, ε c, ?_, ?_⟩
  · intro s hs
    obtain ⟨t, rfl⟩ := ε.surjective s
    exact hirr t (ε.injective (by
      simpa [map_add, map_mul, map_pow] using hs))
  · exact ⟨eOm.trans (statedOmegaMinusCongr ε rfl rfl)⟩

theorem GGInnerDiagOnLabel.uniNbrLabel_iso
    {G : Type} [Group G] [Finite G] {p : ℕ} {Bs K : Subgroup G} {n f : ℕ}
    (hK : GGInnerDiagOnLabel (fun _ lab => GGSecFiveBPermUniNbrLabel n f lab) p Bs K)
    (hn : 4 ≤ n) (hf : 1 ≤ f) (hnf : n = 4 → 2 ≤ f) :
    Nonempty (↥K ≃* StatedSp (n - 1) (GaloisField 2 f)) ∨
      (Even n ∧ ∃ b c : GaloisField 2 f, (∀ s : GaloisField 2 f, s ^ 2 + b * s + c ≠ 0) ∧
        Nonempty (↥K ≃* StatedOmega (StatedQuadMinus n (GaloisField 2 f) b c))) ∨
      (Odd n ∧ Nonempty (↥K ≃* StatedOmega (StatedQuadPlus n (GaloisField 2 f)))) := by
  obtain ⟨lab, hlab, hhas, R, hRgrp, I, Fset, θ, hP⟩ := largeEvenMarking_exists_hasLabel hK
  have hqs : CFSG.Assembly.IsQuasisimple ↥K := isQuasisimple_of_largeEvenMarking hK
  have hY : CFSG.IsQuasisimple ↥K := (TableBSymp.isQuasisimple_iff ↥K).mp hqs
  obtain ⟨t, r, e⟩ := lab
  have hlabn : e = f := by
    have h := hP.1
    unfold GGSecFiveBPermUniNbrLabel at h
    exact h.1
  have hcases : ((t = .B ∨ t = .C) ∧ r = n - 1) ∨
      (t = .D ∧ r = n ∧ Odd n) ∨ (t = .twD ∧ r = n ∧ Even n) := by
    have h := hP.1
    unfold GGSecFiveBPermUniNbrLabel at h
    exact h.2
  rcases hcases with ⟨ht, hr⟩ | ⟨ht, hr, hodd⟩ | ⟨ht, hr, heven⟩
  · rcases ht with ht | ht
    · subst ht; subst hr; subst hlabn
      refine Or.inl (sp_iso_of_hasLabel_B hY hn hf hnf ?_)
      exact largeEvenMarking_of_hasLabel hqs hlab hhas
    · subst ht; subst hr; subst hlabn
      refine Or.inl (sp_iso_of_hasLabel_B hY hn hf hnf ?_)
      exact largeEvenMarking_of_hasLabel hqs hlab hhas
  · subst ht; subst hr; subst hlabn
    refine Or.inr (Or.inr ⟨hodd, ?_⟩)
    exact omPlus_iso_of_hasLabel_D hY hn hf hnf (largeEvenMarking_of_hasLabel hqs hlab hhas)
  · subst ht; subst hr; subst hlabn
    obtain ⟨b, c, hirr, hiso⟩ :=
      omMinus_iso_of_hasLabel_twD hY hn hf (largeEvenMarking_of_hasLabel hqs hlab hhas)
    exact Or.inr (Or.inl ⟨heven, b, c, hirr, hiso⟩)

section Cell


theorem GGSecFiveRouteCfg.uniCell_of_bCoordinateBlock (hT : GGTBTorAll)
    (hLift : GGTBTorLiftRows) (hTCJ : GGTCJKnown) (hI3 : GGNbrSubcomponentInput)
    (hRig : GGLabelRigidInput) (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput)
    (hLB : GGLBalanceInput) (hPJ : GGStdSubPrimeInput) (hTE6R : GGTwE6ThreeNbrRankInput)
    {G : Type} [Group G] [Finite G] {p n f : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)} (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    (hn : 4 ≤ n) (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))) {K : Subgroup G}
    (hK𝒦 : K ∈ 𝒦) (i0 : Fin n)
    (hAut : (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n p i0)
    (hf : 1 ≤ f) (hnf : n = 4 → 2 ≤ f)
    (hL : GGInnerDiagOnLabel (fun p lab => GGSecFiveBPermUniLabel n p lab ∧ lab.n = f) p Bs L)
    (hJ : GGHasLabel ⟨.twA, n - 2, f⟩ (↥J ⧸ Subgroup.center ↥J)) :
    GGSecFiveBPermUniSpCell p Bs L 𝒦 n eta f K i0 ∨
      GGSecFiveBPermUniOmCell p Bs L 𝒦 n eta f K i0 := by
  obtain ⟨labL, hlabL, hhasL, R, hRgrp, I, Fset, θ, hPL⟩ := largeEvenMarking_exists_hasLabel hL
  have hpf : p ∣ 2 ^ f + 1 := by
    have h1 : p ∣ 2 ^ labL.n + 1 := by
      have h := hPL.1.1
      unfold GGSecFiveBPermUniLabel at h
      exact h.2.2
    rwa [hPL.1.2] at h1
  have hKlabel := GGSecFiveRouteCfg.uniNbr_label hT hLift hTCJ hI3 hRig hraw hiso hLB hPJ
    hTE6R hR hn eta hK𝒦 i0 hAut hf hnf hpf hJ
  rcases hKlabel.uniNbrLabel_iso hn hf hnf with hSp | hEven | hOdd
  · exact Or.inl ⟨hL, hK𝒦, hSp, hAut⟩
  · exact Or.inr ⟨hL, hK𝒦, Or.inl hEven, hAut⟩
  · exact Or.inr ⟨hL, hK𝒦, Or.inr hOdd, hAut⟩

end Cell

end CFSG.StandardType

end
