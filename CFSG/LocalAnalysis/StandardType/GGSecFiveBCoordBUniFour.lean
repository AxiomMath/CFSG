module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBUniLeaves
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBUniFourCharts
public import Certificates.Certificate117
import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBUniFrames
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermUniOmJoin
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermOmKCalib
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermUniOm
import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1OfPrim

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType CFSG.LieType.Universal
  CFSG.LieType.BorelTits CFSG.ClassicalGroups.UnitaryFlag
  CFSG.ClassicalGroups.Orthogonal.UnitaryOmega CFSG.ClassicalInvolution.Models.OrthogonalPairs
  CFSG.LocalAnalysis.ComponentInitial

section Inputs


theorem ggSecFiveBCoordBUniFourInput_of_completion
    (hC : GGUniFourCompletion) : GGSecFiveBCoordBUniFourInput := by
  intro hMp hRig G _ _ p B Bs x L D J 𝒦 hR _ _ _ _ i0 _ _ _ hBB _ _ f K hcell
  obtain ⟨hp, hp2⟩ := ggRouteCfg_prime hR
  haveI : Fact p.Prime := ⟨hp⟩
  have hf2 : 2 ≤ f := hcell.1
  have hpq : p ∣ 2 ^ f + 1 := hcell.2.2.1
  have hBsC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs :=
    hR.1.1.2.1.2.2.2
  have hq : 4 ≤ 2 ^ f :=
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
  have hq3 : ¬(3 = 3 ∧ 2 ^ f = 2) := fun h => absurd (h.2 ▸ hq) (by norm_num)
  obtain ⟨eta', hA, hxB, hX, F, _, _, _, _, E, hK, π, -, ⟨κ, χ, hκ⟩, σ, χ', hσ⟩ :=
    hcell.exists_frames hMp hRig hR hBB (m := 3) le_rfl
  have hM : ∀ c d : Fin (3 + 1), c ≠ d → c ≠ π (Fin.last 3) → d ≠ π (Fin.last 3) →
      ggBlockComm Bs eta' ({c, d} : Set (Fin (3 + 1))) ≤ L := by
    intro c d hcd hc hd
    obtain ⟨s, hs⟩ := Fin.exists_succAbove_eq (x := π.symm c) (y := Fin.last 3)
      (fun h => hc (by rw [← h, Equiv.apply_symm_apply]))
    obtain ⟨s', hs'⟩ := Fin.exists_succAbove_eq (x := π.symm d) (y := Fin.last 3)
      (fun h => hd (by rw [← h, Equiv.apply_symm_apply]))
    have hss' : s ≠ s' := by
      rintro rfl
      exact hcd (π.symm.injective (hs.symm.trans hs'))
    have h := uniFourChart_map_normBlock_pair hκ hK hσ hBsC hA hX hxB (Fin.last 3) hss'
    rw [hs, hs', Equiv.apply_symm_apply, Equiv.apply_symm_apply,
      show uniFourChart hK σ κ (Fin.last 3) = κ from uniFourChart_three hK σ κ] at h
    rw [← h, ← hκ.2.1]
    exact Subgroup.map_le_range _ _
  have hJK := hσ.range_comp_uniCast_le hK hf2 hp le_rfl hM
  obtain ⟨σ', hσ', hU1⟩ := exists_uniLFrame_calibrated hpq hK le_rfl hq3 hσ hκ
    (hσ.range_comp_uniCast_eq hp2 hK hpq le_rfl hq3 hκ hJK)
  have ha : ∀ i, Function.Injective (uniFourChart hK σ' κ i) := fun i =>
    (MulAut.conj _).injective.comp hκ.1
  have hcardF : 4 ≤ Nat.card (GaloisField 2 f) := by
    rw [GaloisField.card 2 f (by omega)]
    exact hq
  have hcardK : Nat.card F = (2 ^ f) ^ 2 := by rw [hK.card, ← pow_mul, mul_comm]
  obtain ⟨Ψ, hΨ, -, hΨr⟩ := hC (GaloisField 2 f) F f E hcardF hcardK G (uniFourChart hK σ' κ) ha
    (uniFourBlocks Bs eta' π) fun i S hS hS2 =>
      uniFourChart_map_normBlock_eq_uniFourBlocks hκ hK hσ' hBsC hA hX hxB hpq i S hS hS2
  obtain ⟨ψ, hψk, hψr⟩ :=
    exists_ggU_POmegaPlus_of_injective_normOmega (m := 3) (by norm_num) ⟨1, rfl⟩ hΨ
  exact ⟨ψ, hψk, hψr.trans (hΨr.trans (iSup_range_uniFourChart hK hq hκ.2.1 hσ'.1 hU1))⟩

end Inputs

end CFSG.StandardType

end
