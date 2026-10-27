module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermOmFrameDefs
public import CFSG.LocalAnalysis.StandardType.GGAssemblyTwoHypSix
public import Certificates.Certificate117
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermOmKFrame
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermSpFrame
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermSpEquiv
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermSpLFrame
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermSpLFrameMp
import CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.SpinMinusComm
import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1OfPrim
import CFSG.LocalAnalysis.StandardType.GGTypeANbrKappaBase
import CFSG.LocalAnalysis.StandardType.GGFieldCaseTableBIrred
import CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.SpinPlusBlocks
import CFSG.LieType.Universal.Spin

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType CFSG.LieType.Universal
  CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
open CFSG.ClassicalInvolution.WeakCT (blockSL2)

open scoped MatrixGroups

theorem ggSecFiveBPermOm_agreement_crossing_of_frames {G : Type} [Group G] [Finite G]
    {p n r f : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hf : 2 ≤ f) (hr : 2 ≤ r)
    {Bs X₁ X₂ : Subgroup G} {x y : G}
    (hBc : ∀ a ∈ Bs, ∀ b ∈ Bs, a * b = b * a)
    (hBsmax : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hxBs : x ∈ Bs) (hX₁ : IsComponentOf X₁ (Subgroup.centralizer ({x} : Set G)))
    (hyBs : y ∈ Bs) (hX₂ : LargeEvenPComponent p (Subgroup.centralizer ({y} : Set G)) X₂)
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))} {π : Fin (r + 2) ≃ Fin n}
    (hA : (ggAutomizer X₁ Bs).map (MulAut.congr eta).toMonoidHom = aPermutationFull n p)
    {σ : SL(r + 2, GaloisField 2 f) →* G}
    {χ : Multiplicative (ZMod p) →* (GaloisField 2 f)ˣ}
    (hσ : GGSecFiveBPermSpLFrame Bs X₁ eta π σ χ)
    {κ : spinGroup (quadMinus (r + 2) (GaloisField 2 f) (minusCoeffs 2 f).1
      (minusCoeffs 2 f).2) →* G}
    {χ' : Multiplicative (ZMod p) →* (GaloisField 2 f)ˣ}
    (hκ : GGSecFiveBPermLinOmKFrame Bs X₂ eta π κ χ') :
    (∀ k : Fin r, (σ.comp (blockSL2 (GaloisField 2 f) (r + 1) k.succ)).range =
      (CurtisTits.rankOne (minusDatum (r + 2) (minusCoeffs_irr 2 f)).rootGroup
        k.castSucc).map κ) ∧
    ∀ a ∈ (σ.comp (blockSL2 (GaloisField 2 f) (r + 1) 0)).range,
      ∀ b ∈ (CurtisTits.rankOne (minusDatum (r + 2) (minusCoeffs_irr 2 f)).rootGroup
        (Fin.last r)).map κ, a * b = b * a := by
  have : NeZero r := ⟨by omega⟩
  have hAgree : ∀ k : Fin r,
      (σ.comp (blockSL2 (GaloisField 2 f) (r + 1) k.succ)).range =
        (CurtisTits.rankOne (minusDatum (r + 2) (minusCoeffs_irr 2 f)).rootGroup
          k.castSucc).map κ := by
    intro k
    have hk : k.castSucc.val + 1 < r + 2 - 1 := by
      have := k.isLt
      rw [Fin.val_castSucc]
      omega
    have hcardA : Nat.card ((CurtisTits.rankOne (minusDatum (r + 2)
        (minusCoeffs_irr 2 f)).rootGroup k.castSucc).map κ) =
        Nat.card (SL(2, GaloisField 2 f)) := by
      rw [CFSG.ClassicalInvolution.WeakCT.rankOne_minusDatum_long (minusCoeffs_irr 2 f)
          (n := r + 2) hk,
        Subgroup.card_map_of_injective hκ.1]
      exact (Nat.card_congr (MonoidHom.ofInjective
        (CFSG.ClassicalInvolution.WeakCT.rLong_injective
          (n := r + 2) (k := k.castSucc) hk)).toEquiv).symm
    have hcardB : Nat.card ((σ.comp (blockSL2 (GaloisField 2 f) (r + 1)
        k.succ)).range) ≤ Nat.card (SL(2, GaloisField 2 f)) := by
      rw [MonoidHom.range_comp]
      calc Nat.card (Subgroup.map σ (blockSL2 (GaloisField 2 f) (r + 1) k.succ).range) ≤
            Nat.card (blockSL2 (GaloisField 2 f) (r + 1) k.succ).range :=
            Nat.le_of_dvd Nat.card_pos (Subgroup.card_map_dvd _ σ)
        _ = Nat.card (SL(2, GaloisField 2 f)) := by
            rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective
              (CFSG.ClassicalInvolution.WeakCT.blockSL2_injective
              (r + 1) k.succ), Subgroup.card_top]
    have hLk := ggSecFiveBPermSp_reflComm_L hp2 hr hBc hBsmax hxBs hX₁ hσ k.succ
    rw [Fin.castSucc_succ] at hLk
    have hKk := ggSecFiveBPermOm_rankOne_le_reflComm hp2 hBsmax hκ k
    rw [hLk] at hKk
    exact (Subgroup.eq_of_le_of_card_ge hKk (by rw [hcardA]; exact hcardB)).symm
  refine ⟨hAgree, ?_⟩
  obtain ⟨w, φ, g, hw_eq, hwcoord, hgconj⟩ :=
    ggSecFiveBSp_conjData (r := r) (n := n) (p := p) (L := X₁) (Bs := Bs) (π := π) hr hA
  have hw0 : w (π 0) = π 2 := by
    rw [hw_eq]
    exact Equiv.swap_apply_left _ _
  have hw1 : w (π 1) = π 1 := by
    rw [hw_eq]
    exact Equiv.swap_apply_of_ne_of_ne
      (π.injective.ne (ggSecFiveBSp_fin_one_ne_zero (n := r + 2) (by omega)))
      (π.injective.ne (ggSecFiveBSp_fin_one_ne_two (n := r + 2) (by omega)))
  have hwlast : w (π (Fin.last (r + 1))) = π (Fin.last (r + 1)) := by
    rw [hw_eq]
    exact Equiv.swap_apply_of_ne_of_ne
      (π.injective.ne (ggSecFiveBSp_fin_last_ne_zero (r := r + 1) (by omega)))
      (π.injective.ne (ggSecFiveBSp_fin_last_succ_ne_two (r := r) hr))
  have hC1 : ⁅Subgroup.centralizer (ggBsCoordEq Bs eta (π 0) (π 1) : Set G), Bs⁆ =
      (σ.comp (blockSL2 (GaloisField 2 f) (r + 1) 0)).range := by
    have h := ggSecFiveBPermSp_reflComm_L hp2 hr hBc hBsmax hxBs hX₁ hσ (0 : Fin (r + 1))
    simpa only [ggSecFiveBSp_fin_castSucc_zero, ggSecFiveBSp_fin_succ_zero] using h
  have h1c : ((1 : Fin (r + 1)).castSucc : Fin (r + 2)) = 1 := by
    ext
    rw [Fin.val_castSucc, ggSecFiveBSp_fin_val_one (n := r + 1) (by omega),
      ggSecFiveBSp_fin_val_one (n := r + 2) (by omega)]
  have hA0 : (σ.comp (blockSL2 (GaloisField 2 f) (r + 1) 1)).range =
      (CurtisTits.rankOne (minusDatum (r + 2) (minusCoeffs_irr 2 f)).rootGroup
        (0 : Fin r).castSucc).map κ := by
    simpa only [Fin.succ_zero_eq_one'] using hAgree 0
  have hK10 : ⁅Subgroup.centralizer (ggBsCoordEq Bs eta (π 2) (π 1) : Set G), Bs⁆ =
      (CurtisTits.rankOne (minusDatum (r + 2) (minusCoeffs_irr 2 f)).rootGroup
        (0 : Fin r).castSucc).map κ := by
    rw [ggBsCoordEq_comm]
    have h := ggSecFiveBPermSp_reflComm_L hp2 hr hBc hBsmax hxBs hX₁ hσ (1 : Fin (r + 1))
    rw [h1c, ggSecFiveBSp_fin_succ_one hr] at h
    exact h.trans hA0
  have hfirst : (σ.comp (blockSL2 (GaloisField 2 f) (r + 1) 0)).range.map
      (MulAut.conj g).toMonoidHom =
      (CurtisTits.rankOne (minusDatum (r + 2) (minusCoeffs_irr 2 f)).rootGroup
        (0 : Fin r).castSucc).map κ := by
    calc (σ.comp (blockSL2 (GaloisField 2 f) (r + 1) 0)).range.map
          (MulAut.conj g).toMonoidHom
        = (⁅Subgroup.centralizer (ggBsCoordEq Bs eta (π 0) (π 1) : Set G), Bs⁆).map
            (MulAut.conj g).toMonoidHom := by rw [hC1]
      _ = ⁅Subgroup.centralizer (ggBsCoordEq Bs eta (w (π 0)) (w (π 1)) : Set G), Bs⁆ :=
          ggReflComm_map_conj hgconj hwcoord (π 0) (π 1)
      _ = ⁅Subgroup.centralizer (ggBsCoordEq Bs eta (π 2) (π 1) : Set G), Bs⁆ := by
          rw [hw0, hw1]
      _ = (CurtisTits.rankOne (minusDatum (r + 2) (minusCoeffs_irr 2 f)).rootGroup
            (0 : Fin r).castSucc).map κ := hK10
  have hM : ⁅Subgroup.centralizer
        (ggBsCoordZero Bs eta (π (Fin.last (r + 1))) : Set G), Bs⁆ =
      (CurtisTits.rankOne (minusDatum (r + 2) (minusCoeffs_irr 2 f)).rootGroup
        (Fin.last r)).map κ :=
    ggSecFiveBPermOm_singletonComm_K hp2 hf hr hBc hBsmax hyBs hX₂ hκ
  have hlast : ((CurtisTits.rankOne (minusDatum (r + 2) (minusCoeffs_irr 2 f)).rootGroup
        (Fin.last r)).map κ).map (MulAut.conj g).toMonoidHom =
      (CurtisTits.rankOne (minusDatum (r + 2) (minusCoeffs_irr 2 f)).rootGroup
        (Fin.last r)).map κ := by
    calc ((CurtisTits.rankOne (minusDatum (r + 2) (minusCoeffs_irr 2 f)).rootGroup
          (Fin.last r)).map κ).map (MulAut.conj g).toMonoidHom
        = (⁅Subgroup.centralizer
            (ggBsCoordZero Bs eta (π (Fin.last (r + 1))) : Set G), Bs⁆).map
            (MulAut.conj g).toMonoidHom := by rw [hM]
      _ = ⁅Subgroup.centralizer
            (ggBsCoordZero Bs eta (w (π (Fin.last (r + 1)))) : Set G), Bs⁆ :=
          ggSingletonComm_map_conj hgconj hwcoord (π (Fin.last (r + 1)))
      _ = ⁅Subgroup.centralizer
            (ggBsCoordZero Bs eta (π (Fin.last (r + 1))) : Set G), Bs⁆ := by
          rw [hwlast]
      _ = (CurtisTits.rankOne (minusDatum (r + 2) (minusCoeffs_irr 2 f)).rootGroup
            (Fin.last r)).map κ := hM
  intro a ha b hb
  have hca : (MulAut.conj g) a ∈
      (CurtisTits.rankOne (minusDatum (r + 2) (minusCoeffs_irr 2 f)).rootGroup
        (0 : Fin r).castSucc).map κ := by
    rw [← hfirst]
    exact Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom ha
  have hcb : (MulAut.conj g) b ∈
      (CurtisTits.rankOne (minusDatum (r + 2) (minusCoeffs_irr 2 f)).rootGroup
        (Fin.last r)).map κ := by
    rw [← hlast]
    exact Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom hb
  obtain ⟨A, hA, hAeq⟩ := Subgroup.mem_map.mp hca
  obtain ⟨B, hB, hBeq⟩ := Subgroup.mem_map.mp hcb
  have hij : (0 : Fin r).castSucc ≠ Fin.last r := by
    intro h
    have h' := congrArg Fin.val h
    rw [Fin.val_castSucc, ggSecFiveBSp_fin_val_zero, Fin.val_last] at h'
    omega
  have hadj : ¬ CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.BAdj (r + 2)
      (0 : Fin r).castSucc (Fin.last r) := by
    intro h
    rcases h with h | h
    · rw [Fin.val_castSucc, ggSecFiveBSp_fin_val_zero, Fin.val_last] at h
      omega
    · rw [Fin.val_castSucc, ggSecFiveBSp_fin_val_zero, Fin.val_last] at h
      omega
  have hcommSpin : A * B = B * A := by
    have hle := CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.rankOne_commute_B
      (n := r + 2) (hirr := minusCoeffs_irr 2 f) (i := (0 : Fin r).castSucc)
      (j := Fin.last r) hij hadj
    have hmem := hle hA
    rw [Subgroup.mem_centralizer_iff] at hmem
    exact (hmem B hB).symm
  have hcomm : ((MulAut.conj g) a) * ((MulAut.conj g) b) =
      ((MulAut.conj g) b) * ((MulAut.conj g) a) := by
    rw [← hAeq, ← hBeq]
    simpa using congrArg κ hcommSpin
  exact (commute_map_iff (MulAut.conj g).injective).mp hcomm

section Certs


theorem ggSecFiveBPermOmChartInput_of_frames (hMp : GGInnerDiagMpInput)
    (hK : GGSecFiveBPermOmKFrameInput) : GGSecFiveBPermOmChartInput := by
  intro G _ _ p B Bs x L D J 𝒦 hR hT1 n e hpres h4 eta hBfull hAfull hnbr hG0 hB hlab f K i0
    hcell
  obtain ⟨hp, hp2⟩ := ggRouteCfg_prime hR
  let _ : Fact p.Prime := ⟨hp⟩
  obtain ⟨r, π, -, κ, χ', hKF⟩ :=
    hK G p B Bs x L D J 𝒦 hR hT1 n e hpres h4 eta hBfull hAfull hnbr hG0 hB hlab f K i0 hcell
  have hn : n = r + 2 := by
    have h := Fintype.card_congr π
    simpa using h.symm
  have hr : 2 ≤ r := by omega
  obtain ⟨hf, hK𝒦, ⟨ψ, hker, hrange⟩, -, -⟩ := hcell
  have hcfg := hR.1.1
  obtain ⟨σ, χ, hLF⟩ := exists_ggSecFiveBPermSpLFrame hMp hcfg.tableB_facts.1
    hcfg.1.2.2.2.2.2.1.2.1 hcfg.2.1.2.1 hcfg.2.1.2.2.2 hR.1.2.2.1.1
    hcfg.card_bstar_inf_centralizer_L.le h4 eta hAfull (by omega) hker hrange r π
  obtain ⟨-, hBs, hxBs, -, -⟩ := hcfg.tableB_facts
  have hBc : ∀ a ∈ Bs, ∀ b ∈ Bs, a * b = b * a :=
    fun a ha b hb => CFSG.Open.IsElemAbelian.comm hBs ha hb
  have hBsmax : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs :=
    hR.1.1.2.1.2.2.2
  have hLcomp : IsComponentOf L (Subgroup.centralizer ({x} : Set G)) :=
    (hR.1.1.1.2.2.2.2.2.2.1 : LargeEvenSStar p B x L).2.2.2.1
  obtain ⟨y, hNy⟩ := hR.2.2.2.1.2 K hK𝒦
  have hyBs : y ∈ Bs := hR.1.1.2.1.1 hNy.1.2.1
  have hKcomp : LargeEvenPComponent p (Subgroup.centralizer ({y} : Set G)) K :=
    hNy.1.2.2.2.2.1
  exact ⟨r, hn, σ, κ, hLF.1, hLF.2.1, hKF.1, hKF.2.1,
    ggSecFiveBPermOm_agreement_crossing_of_frames hp2 hf hr hBc hBsmax hxBs hLcomp hyBs hKcomp
      hAfull hLF hKF⟩

end Certs

end CFSG.StandardType

end
