module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8Star
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8Fin
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8SetUp
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8Model
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8Lift
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8Image
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs15
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs16
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8Hypotheses
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8Inputs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenResultsB

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem c8_star_holds_of_good (D : Data G) (h61 : UC6.R6_1 D) (h129 : R129_1 D) (h22 : R1622 D)
    (h1217 : R1217 D) (hSpA : RSp6SmallMod) (hSpC : RSp6SpinCent) (hSpF : RSp6SpinForm)
    (hSpSt : RSp6SpinStab) (hle : C8TleKGood D) (hinv : C8InvThreePrimeGood D)
    {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V} (hS : Sect16 D V₀ V L hV)
    (h8 : Case167_8 D V₀ V hV L) (hG : C8Good D V₀ V L) : C8Star D V₀ V L hV := by
  have h26 : R16_26 D :=
    R16_26_of_fin D h61 (r16_26_fin_holds D h1217 hSpA hSpC hSpF hSpSt)
  obtain ⟨v₀, T₀, K, T', hU⟩ := c8_exists_setUp D h129 h22 h26 hS h8
  have hM : Mbar D.M V₀ V hV = lBar V₀ V hV L := c8_mbar_eq_lbar D h1217 hSpA hSpC hS h8
  have hPH : ptCent (Mbar D.M V₀ V hV) (mkTil V₀ V hV v₀) ≤ lBar V₀ V hV L := by
    rw [← hM]
    exact inf_le_left
  obtain ⟨ψ, hψ⟩ := c8_exists_model hPH h8.1 hU.e64
  have hperf : ⁅ptCent (Mbar D.M V₀ V hV) (mkTil V₀ V hV v₀),
      ptCent (Mbar D.M V₀ V hV) (mkTil V₀ V hV v₀)⁆ =
      ptCent (Mbar D.M V₀ V hV) (mkTil V₀ V hV v₀) := by
    rw [hψ]
    exact c8_commutator_pullSub_stabilizer ψ
  have hLift := c8_barSub_inf_centralizer_eq D hS hM v₀ hperf
  have hIm := c8_barSub_inf_eq D h61 hS h8 hM hU.mem ψ hψ hLift
  have hTK : T' ≤ K := hle V₀ V L hV hS h8 hG v₀ T₀ K T' hU
  obtain ⟨N, hNK, hN, h3, hinvN⟩ := hinv V₀ V L hV hS h8 hG v₀ T₀ K T' hU
  have hconj : ∀ {k x : G}, k ∈ K → x ∈ N → k * x * k⁻¹ ∈ N := by
    intro k x hk hx
    have h := hN.conj_mem ⟨x, hNK hx⟩ (by simpa [mem_subgroupOf] using hx) ⟨k, hk⟩
    simpa [mem_subgroupOf] using h
  refine c8_star_of_le_normal D hU.sylowM ψ (hIm.trans hψ) hTK hNK hN ?_ h3
  intro t ht ht2 k hk
  have htN : t ∈ N := hinvN t (hTK ht) ht2
  have h1 : k * t⁻¹ * k⁻¹ ∈ N := hconj hk (N.inv_mem htN)
  have h2 : t * (k * t⁻¹ * k⁻¹) ∈ N := N.mul_mem htN h1
  simpa [mul_assoc] using h2

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
