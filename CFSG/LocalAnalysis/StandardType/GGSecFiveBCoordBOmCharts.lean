module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBOmDefs
public import CFSG.LocalAnalysis.StandardType.GGAssemblyTwoHypSix
public import Certificates.Certificate117
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermLinOmKFrameMp
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermLinOmKTorus
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermOmFrame
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermSpLFrameMp
import CFSG.LocalAnalysis.StandardType.GGSecFiveBSpCoordFrameFacts
import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1OfPrim
import CFSG.LocalAnalysis.StandardType.GGOneFiveNbr

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType CFSG.LieType.Universal
  CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
open scoped MatrixGroups

theorem prime_dvd_card_spinGroup_quadMinus {p r f : ℕ} [Fact p.Prime] (hr : 2 ≤ r)
    {ω : (GaloisField 2 f)ˣ} (hω : ω ^ p = 1) (hωo : orderOf ω = p) :
    p ∣ Nat.card (spinGroup (quadMinus (r + 2) (GaloisField 2 f) (minusCoeffs 2 f).1
      (minusCoeffs 2 f).2)) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  let T := spinMinusSplitTorus hr (minusCoeffs_irr 2 f) hω
  have hinj : Function.Injective T :=
    spinMinusSplitTorus_injective hr (minusCoeffs_irr 2 f) hω hωo
  have hdom : Nat.card (Fin (r + 1) → Multiplicative (ZMod p)) = p ^ (r + 1) := by
    rw [Nat.card_fun, Nat.card_congr (Multiplicative.toAdd (α := ZMod p)), Nat.card_zmod,
      Nat.card_eq_fintype_card, Fintype.card_fin]
  have hrange : Nat.card T.range = p ^ (r + 1) :=
    (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm.trans hdom
  have hdvd := Subgroup.card_subgroup_dvd_card T.range
  rw [hrange] at hdvd
  exact (dvd_pow_self p (by omega)).trans hdvd


theorem ggSecFiveBCoordBOmChartInput_of_mp
    (hMp : GGInnerDiagMpInput) : GGSecFiveBCoordBOmChartInput := by
  intro G _ _ p B Bs x L D J 𝒦 hR hT1 n e hpres h4 eta i0 hBfull hLeta hLab hBB hnbr hG0 f K hcell
  obtain ⟨hp, hp2⟩ := ggRouteCfg_prime hR
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨r, rfl⟩ : ∃ r, n = r + 2 := ⟨n - 2, by omega⟩
  have hr : 2 ≤ r := by omega
  obtain ⟨hf, hK𝒦, ⟨ψ, hker, hrange⟩, ⟨eL⟩, eta', -, hL', hK'⟩ := hcell
  obtain ⟨hcfg, -, hmarkAll, -, -, -⟩ := hR.1
  obtain ⟨hBle, hBs, -, hBsmax⟩ := hcfg.2.1
  have hBc : ∀ a ∈ Bs, ∀ b ∈ Bs, a * b = b * a :=
    fun a ha b hb => CFSG.Open.IsElemAbelian.comm hBs ha hb
  obtain ⟨-, -, hxBs, -, -⟩ := hcfg.tableB_facts
  obtain ⟨y, hNy⟩ := hR.2.2.2.1.2 K hK𝒦
  have hyBs : y ∈ Bs := hBle hNy.1.2.1
  have hKcomp : IsComponentOf K (Subgroup.centralizer ({y} : Set G)) :=
    (isComponentOf_of_isNeighborOf hcfg.1.2.2.2.2.2.2.2
      (isNeighborOf_of_ggNbr hcfg.2.2 hNy)).1
  obtain ⟨σ₀, χ₀, hσ₀⟩ :=
    exists_ggSecFiveBPermSpLFrame hMp hp hp2 hBs hBsmax (hmarkAll.2 y K hNy)
      (hR.card_inf_centralizer_nbr_le hBB hNy) (by omega) eta' hK' (by omega) hker hrange r
      (Equiv.refl _)
  let ω : (GaloisField 2 f)ˣ := χ₀ (Multiplicative.ofAdd 1)
  have hω : ω ^ p = 1 := by
    change (χ₀ (Multiplicative.ofAdd 1)) ^ p = 1
    rw [← map_pow]
    have hpow : (Multiplicative.ofAdd 1 : Multiplicative (ZMod p)) ^ p = 1 := by
      rw [← ofAdd_nsmul]
      simp
    rw [hpow, map_one]
  have hωo : orderOf ω = p := by
    change orderOf (χ₀ (Multiplicative.ofAdd 1)) = p
    rw [orderOf_injective χ₀ hσ₀.2.2.1 (Multiplicative.ofAdd 1), orderOf_ofAdd_eq_addOrderOf]
    exact ZMod.addOrderOf_one p
  obtain ⟨π, -, κ, χ', hκ⟩ :=
    ggSecFiveBPermLinOmK_exists_frame hMp hp2 (by omega) hr hcfg.2.1 hmarkAll.1 eL eta' hL' hω hωo
  obtain ⟨σ, χ, hσ⟩ :=
    exists_ggSecFiveBPermSpLFrame hMp hp hp2 hBs hBsmax (hmarkAll.2 y K hNy)
      (hR.card_inf_centralizer_nbr_le hBB hNy) (by omega) eta' hK' (by omega) hker hrange r π
  have hLcomp : LargeEvenPComponent p (Subgroup.centralizer ({x} : Set G)) L := by
    refine hR.largeEvenPComponent_L ?_
    rw [Nat.card_congr eL.toEquiv]
    exact prime_dvd_card_spinGroup_quadMinus hr hω hωo
  exact ⟨r, rfl, σ, κ, hσ.1, hσ.2.1, hκ.1, hκ.2.1,
    ggSecFiveBPermOm_agreement_crossing_of_frames hp2 hf hr hBc hBsmax hyBs hKcomp hxBs hLcomp
      hK' hσ hκ⟩

end CFSG.StandardType

end
