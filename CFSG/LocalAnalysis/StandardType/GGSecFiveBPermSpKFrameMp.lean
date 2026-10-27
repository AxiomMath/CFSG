module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermSpFrameDefs
public import CFSG.LocalAnalysis.StandardType.GGAssemblyTwoHypSix
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermSpKFrameCore
import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1OfPrim

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal


theorem ggSecFiveBPermSpKFrameInput_of_mp (hMp : GGInnerDiagMpInput)
    (hL : GGSecFiveBPermSpLFrameInput) : GGSecFiveBPermSpKFrameInput := by
  intro G _ _ p B Bs x L D J 𝒦 hR hT1 n e hpres h4 eta hBfull hAfull hnbr hG0 f K i0 hcell
  obtain ⟨hp, hp2⟩ := ggRouteCfg_prime hR
  let _ : Fact p.Prime := ⟨hp⟩
  obtain ⟨r, rfl⟩ : ∃ r, n = r + 2 := ⟨n - 2, by omega⟩
  have hr : 2 ≤ r := by omega
  obtain ⟨σ, χL, hLF⟩ :=
    hL G p B Bs x L D J 𝒦 hR hT1 (r + 2) e hpres h4 eta hBfull hAfull hnbr hG0 f K i0 hcell r
      (Equiv.refl _)
  let ω : (GaloisField 2 f)ˣ := χL (Multiplicative.ofAdd 1)
  have hω : ω ^ p = 1 := by
    change (χL (Multiplicative.ofAdd 1)) ^ p = 1
    rw [← map_pow]
    have hpow : (Multiplicative.ofAdd 1 : Multiplicative (ZMod p)) ^ p = 1 := by
      rw [← ofAdd_nsmul]
      simp
    rw [hpow, map_one]
  have hωo : orderOf ω = p := by
    change orderOf (χL (Multiplicative.ofAdd 1)) = p
    rw [orderOf_injective χL hLF.2.2.1 (Multiplicative.ofAdd 1)]
    rw [orderOf_ofAdd_eq_addOrderOf]
    exact ZMod.addOrderOf_one p
  have hf : 2 ≤ f := hcell.1
  have hK𝒦 : K ∈ 𝒦 := hcell.2.1
  have hBs : GGBstar p B Bs := hR.1.1.2.1
  obtain ⟨y, hN⟩ := hR.2.2.2.1.2 K hK𝒦
  have hmark : GGInnerDiagOn Bs K := hR.1.2.2.1.2 y K hN
  let e' : ↥K ≃* StatedSp (r + 1) (GaloisField 2 f) := Classical.choice hcell.2.2.2.1
  have hA : (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock (r + 2) p i0 :=
    hcell.2.2.2.2
  obtain ⟨π, hπ0, κ, χ, hfr⟩ :=
    ggSecFiveBPermSpK_exists_frame hMp hp2 (by omega) hr hBs hmark e' eta hA hω hωo
  exact ⟨r, π, hπ0, κ, χ, hfr⟩

end CFSG.StandardType

end
