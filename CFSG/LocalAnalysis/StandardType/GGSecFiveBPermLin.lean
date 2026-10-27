module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermLinDefs
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermSU
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBJoinDefs
public import Certificates.Certificate117
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermQTwo
import CFSG.ClassicalInvolution.WeakCT.SpinMinusCharts
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermSp
import CFSG.LocalAnalysis.StandardType.GGSecFivePresTagSpin

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType CFSG.LieType.Universal
  CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
open CFSG.ClassicalInvolution.WeakCT (blockSL2)
open scoped MatrixGroups

theorem ggSecFiveData_of_omCharts {G : Type} [Group G] [Finite G] {p : ℕ} {B : Subgroup G}
    {x : G} {L D J : Subgroup G} {r f : ℕ} (hr : 2 ≤ r) (hf : 2 ≤ f)
    (σ : SL(r + 2, GaloisField 2 f) →* G) (hσ : σ.ker ≤ Subgroup.center SL(r + 2, GaloisField 2 f))
    (κ : spinGroup (quadMinus (r + 2) (GaloisField 2 f) (minusCoeffs 2 f).1
      (minusCoeffs 2 f).2) →* G) (hκ : Function.Injective κ)
    (hagree : ∀ k : Fin r, (σ.comp (blockSL2 (GaloisField 2 f) (r + 1) k.succ)).range =
      (CurtisTits.rankOne (minusDatum (r + 2) (minusCoeffs_irr 2 f)).rootGroup
        k.castSucc).map κ)
    (hcross : ∀ a ∈ (σ.comp (blockSL2 (GaloisField 2 f) (r + 1) 0)).range,
      ∀ b ∈ (CurtisTits.rankOne (minusDatum (r + 2) (minusCoeffs_irr 2 f)).rootGroup
        (Fin.last r)).map κ, a * b = b * a)
    (hG0 : ggG0 p B x L D J = σ.range ⊔ κ.range) :
    GGSecFiveData p B x L D J := by
  have hcard : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have hq : 4 ≤ Nat.card (GaloisField 2 f) := by
    rw [hcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  obtain ⟨Ψ, hker, hrange⟩ := CFSG.ClassicalInvolution.WeakCT.weakCT_spinMinus_even_of_charts hr
    hcard hq (minusCoeffs_irr 2 f) σ hσ κ hκ hagree hcross
  have hadm : StatedLieAdmissible .POmegaMinus (r + 3) 2 f :=
    ⟨Nat.prime_two, by omega, by omega⟩
  refine Or.inr (Or.inr ⟨.POmegaMinus, r + 3, f, ggSecFivePres_of_psi_POmegaMinus hadm ?_ Ψ hker
    (hrange.trans hG0.symm)⟩)
  simp only [bnRank]
  omega

theorem ggSecFiveBPermOffSpLinInput_of_rows (hJ : BMaxJoinInput) (hN : GGSecFiveBPermLinNbrInput)
    (hOm : GGSecFiveBPermOmChartInput) (hQ : GGSecFiveBPermQTwoRecInput)
    (hSU : GGSecFiveBPermSUDataInput) : GGSecFiveBPermOffSpLinInput := by
  intro G _ _ p B Bs x L D J 𝒦 hR hT1 n e hP hn eta h𝒦 hLeta hRM hG0 hcell hB hlab
  rcases hN G p B Bs x L D J 𝒦 hR hT1 n e hP hn eta h𝒦 hLeta hG0 hB hlab with
    hSp | ⟨f, K, i0, hc⟩ | ⟨m, K, i0, hc⟩ | ⟨a, K, i0, hc⟩
  · exact absurd hSp hcell
  · have hLK := ggG0_eq_sup_of_bCoordinateBlock hJ hR e hP (by omega) hRM eta h𝒦 hLeta hc.2.1
      hc.2.2.2.2
    obtain ⟨r, rfl, σ, κ, hσ, hσL, hκ, hκK, hagree, hcross⟩ :=
      hOm G p B Bs x L D J 𝒦 hR hT1 n e hP hn eta h𝒦 hLeta hRM hG0 hB hlab f K i0 hc
    exact ggSecFiveData_of_omCharts (by omega) hc.1 σ hσ κ hκ hagree hcross
      (by rw [hLK, hσL, hκK])
  · exact ggSecFiveBPermQTwoDataInput_of_rec hJ hQ G p B Bs x L D J 𝒦 hR hT1 n e hP hn eta h𝒦
      hLeta hRM hG0 hB hlab m K i0 hc
  · exact hSU G p B Bs x L D J 𝒦 hR hT1 n e hP hn eta h𝒦 hLeta hRM hG0 hB hlab a K i0 hc

end CFSG.StandardType

end
