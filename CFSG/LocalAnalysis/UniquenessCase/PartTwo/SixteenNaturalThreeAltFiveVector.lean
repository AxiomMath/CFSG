module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3KbarPt

import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5JPAlt
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11E3A5Fix3
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenLin
import CFSG.LocalAnalysis.GLTheoremA.Sec5BTools
public import CFSG.CGT.PushingUpLit.BHS5.FiveFive
public import CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.Bridge
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporJ4Quot
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2Irr
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2TwentyTwoCapAltEquiv
public import CFSG.Quasithin.Background.C124B51Hyp
public import CFSG.Quasithin.Background.C124BlkTransfer
public import CFSG.Quasithin.Background.C124InterfaceDefs
public import CFSG.Quasithin.Background.C1GNC124
public import CFSG.Quasithin.Background.C1GNSolvConnect
public import CFSG.Quasithin.Background.C1PackC129Solv
public import CFSG.Quasithin.Background.F918V2GDA
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223P2Block
public import CFSG.Quasithin.EmptyFaithful.S152He4Core
public import CFSG.Quasithin.EmptyFaithful.SmithD391Main
public import CFSG.Quasithin.EmptyFaithful.T1515cA
public import CFSG.Quasithin.Vol2.Ch5Sec1L34Lem523
public import CFSG.Quasithin.Vol2.Ch5Sec1L34Lem523F
public import CFSG.Quasithin.Vol2.Ch5Sec1L34QHat
public import CFSG.Quasithin.Vol2.Ch6Defs
public import CFSG.Quasithin.Vol2.Ch6Vocab
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanBlockCycSmall
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrHom
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrXGen
import CFSG.LocalAnalysis.EvenSporadicStandard.Common.Fusion
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11BigDefs
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1KitDefs
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC2MSetting
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDeltaBound
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenWitt
import CFSG.RankThree.PartOne.KC.LinearPrimeFieldActorSolvableCore
import CFSG.SignalizerFunctorTheorem.Glauberman.Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {W : Type} [CommGroup W] [Finite W] {A H T : Subgroup (MulAut W)}

theorem ThreeNat.exists_fixed_vector_alt_five
    (h : ThreeNat A H T)
    (hA5 : UC22.IsAlt ↥H 5)
    (hD5 : SumOfNat (fun H U Z => AlternatingNatural H U Z 5) H
      (commSub ⊤ H) (commSub ⊤ H ⊓ fixV H) 3)
    (h7 : Nat.card ↥(irrSet H) = 7)
    (hK : Nat.card ↥(s1t3KBar A H) = 168) :
    ∃ w : W, w ≠ 1 ∧ w ∈ fixV T ∧
      ∃ E : Subgroup (MulAut W),
        E ≤ A ⊓ MulAction.stabilizer (MulAut W) w ∧
        IsElemAbelian 3 E ∧ Nat.card E = 9 := by
  classical
  have hW2 : ∀ w : W, w ^ 2 = 1 := fun w => by rw [pow_two]; exact h.elem w
  have hrow : s16h_H5RowA5 H (commSub ⊤ H) (commSub ⊤ H ⊓ fixV H) :=
    ⟨3, le_rfl, Or.inr ⟨hA5, hD5⟩⟩
  have hfix0 : commSub ⊤ H ⊓ fixV H = ⊥ := s16jp_row_A5 hW2 hrow
  have hfix : fixV H = ⊥ := by simpa [h.comm] using hfix0
  have hD5' : SumOfNat (fun H U Z => AlternatingNatural H U Z 5) H ⊤ ⊥ 3 := by
    simpa [h.comm, hfix] using hD5
  obtain ⟨I, hI, hIT, J2, hJ2K, _hTKJ2, hJ2mem, hJ2card, _hJ2exp⟩ :=
    h.exists_point_stabilizer h7 hK
  obtain ⟨I0, _hZI0, _hI0U, hI0sum⟩ := s16t3_sumOfNat_summand hD5' (0 : Fin 3)
  have hI0D5 : AlternatingNatural H I0 ⊥ 5 := s16t3_sumOfNat_one hI0sum
  have hI0shape : SumOfNatShape H I0 ⊥ 1 :=
    ⟨5, Or.inr (Or.inr (Or.inr (Or.inr
      ⟨hA5, s16t3_sumOfNat_singleton bot_le hI0D5⟩)))⟩
  have hI0mem : I0 ∈ irrSet H := by
    refine ⟨?_, ?_⟩
    · simpa using s16jp_alt5_commSub_sup hI0D5
    · simpa [hfix] using SumOfNatShape.isIrrOn h.quasi hI0shape
  obtain ⟨g, hg, hgI⟩ := h.trans I0 hI0mem I hI
  have hID5 : AlternatingNatural H I ⊥ 5 := by
    rw [hgI]
    simpa [AlternatingNatural, Subgroup.map_bot] using
      s16t3_realizes_map_of_mem_normalizer (D := FFModel.altDn 5) hg.2 hI0D5
  have hIbot : I ≠ ⊥ := by
    intro hbot
    have hlt : I ⊓ fixV H < I := hI.2.1
    rw [hfix, inf_bot_eq, hbot] at hlt
    exact lt_irrefl ⊥ hlt
  have hTp : IsPGroup 2 T := h.sylow.isPGroup
  obtain ⟨w, hwI, hw1, hwT⟩ :=
    s15_Lin_exists_ne_one_mem_fixV hTp hW2 hIbot hIT
  obtain ⟨y, hyH, hy3, hyw⟩ := s1611e3_a5_fix_three hA5 hID5 w hwI hw1
  have hJ2fix : ∀ k ∈ J2, ∀ u ∈ I, k u = u := by
    intro k hk u hu
    have hkK : k ∈ s1t3KBar A H := hJ2K hk
    have hkcent : k ∈ Subgroup.centralizer (H : Set (MulAut W)) :=
      (Subgroup.mem_inf.mp hkK).2
    have hkI : I.map k.toMonoidHom = I := (hJ2mem k hkK).1 hk
    let φ : ↥I ≃* ↥I :=
      (MulEquiv.subgroupMap k I).trans (MulEquiv.subgroupCongr hkI)
    have hφapply : ∀ u : ↥I, ((φ u : ↥I) : W) = k (u : W) := fun _ => rfl
    have hIshape : SumOfNatShape H I ⊥ 1 :=
      ⟨5, Or.inr (Or.inr (Or.inr (Or.inr
        ⟨hA5, s16t3_sumOfNat_singleton bot_le hID5⟩)))⟩
    have hZ : ∀ u : ↥I, ((φ u : ↥I) : W) ∈ (⊥ : Subgroup W) ↔
        (u : W) ∈ (⊥ : Subgroup W) := by
      intro u
      rw [Subgroup.mem_bot, Subgroup.mem_bot, hφapply]
      simp
    have hφE : ∀ l ∈ H, ∀ u : ↥I, ∀ hu : l (u : W) ∈ I,
        ((φ ⟨l (u : W), hu⟩ : ↥I) : W) * (l ((φ u : ↥I) : W))⁻¹ ∈
          (⊥ : Subgroup W) := by
      intro l hl u _hu
      have hcent : l * k = k * l :=
        (Subgroup.mem_centralizer_iff.mp hkcent) l hl
      have hstep : k (l (u : W)) = l (k (u : W)) := by
        have h1 : l (k (u : W)) = k (l (u : W)) := by
          have := congrArg (fun m : MulAut W => m (u : W)) hcent
          simpa [MulAut.mul_apply] using this
        exact h1.symm
      rw [Subgroup.mem_bot, hφapply, hφapply, hstep, mul_inv_cancel]
    have hconcl := SumOfNatShape.eq_of_equivariant h.quasi hIshape φ hZ hφE
    have h1 := hconcl ⟨u, hu⟩
    rw [Subgroup.mem_bot, hφapply] at h1
    exact mul_inv_eq_one.mp h1
  have h3dvd : 3 ∣ Nat.card ↥J2 := by
    rw [hJ2card]
    exact dvd_mul_right 3 _
  obtain ⟨z0, hz0order⟩ :=
    exists_prime_orderOf_dvd_card' (G := ↥J2) 3 (hp := ⟨Nat.prime_three⟩) h3dvd
  let z : MulAut W := (z0 : MulAut W)
  have hzK : z ∈ s1t3KBar A H := hJ2K z0.2
  have hzA : z ∈ A := (Subgroup.mem_inf.mp hzK).1
  have hz3 : orderOf z = 3 := by
    simp only [z, Subgroup.orderOf_coe, hz0order]
  have hzw : z w = w := hJ2fix z z0.2 w hwI
  obtain ⟨_N, _hNA, hLN, _hNfix, _hNcomm, hNKbot, _hNKsup, _⟩ :=
    h.structure_of_seven h7
  have hHKbot : H ⊓ s1t3KBar A H = ⊥ := by
    refine le_bot_iff.mp ?_
    calc H ⊓ s1t3KBar A H ≤ _N ⊓ s1t3KBar A H := inf_le_inf_right _ hLN
      _ = ⊥ := hNKbot
  have hyz : y * z = z * y :=
    (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hzK).2) y hyH
  have hzNot : z ∉ Subgroup.zpowers y := by
    intro hzyp
    have hzH : z ∈ H := Subgroup.zpowers_le.mpr hyH hzyp
    have hzbot : z ∈ (⊥ : Subgroup (MulAut W)) := by
      rw [← hHKbot]
      exact Subgroup.mem_inf.mpr ⟨hzH, hzK⟩
    have hz1 : z = 1 := Subgroup.mem_bot.mp hzbot
    have h1 : orderOf z = 1 := by rw [hz1]; exact orderOf_one
    rw [hz3] at h1
    norm_num at h1
  have hy3' : y ^ 3 = 1 := by
    have h1 := pow_orderOf_eq_one y
    rwa [hy3] at h1
  have hz3' : z ^ 3 = 1 := by
    have h1 := pow_orderOf_eq_one z
    rwa [hz3] at h1
  have hy1 : y ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hy3
    norm_num at hy3
  obtain ⟨hEea, hEcard⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.Prop53.isElemAbelian_card_sup_zpowers
      (p := 3) Nat.prime_three (a := z) (b := y) hyz.symm hz3' hy3' hy1 hzNot
  let E : Subgroup (MulAut W) := Subgroup.zpowers z ⊔ Subgroup.zpowers y
  have hEA : E ≤ A :=
    sup_le (Subgroup.zpowers_le.mpr hzA) (Subgroup.zpowers_le.mpr (h.le hyH))
  have hEw : E ≤ MulAction.stabilizer (MulAut W) w := by
    refine sup_le ?_ ?_
    · rw [Subgroup.zpowers_le, MulAction.mem_stabilizer_iff]
      exact hzw
    · rw [Subgroup.zpowers_le, MulAction.mem_stabilizer_iff]
      exact hyw
  refine ⟨w, hw1, hwT, E, le_inf hEA hEw, hEea, ?_⟩
  have h9 : (3 : ℕ) ^ 2 = 9 := by norm_num
  rwa [h9] at hEcard

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
