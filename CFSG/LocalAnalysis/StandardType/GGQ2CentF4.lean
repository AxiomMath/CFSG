module

public import CFSG.LocalAnalysis.StandardType.GGQ2CentralizerPort
public import CFSG.LocalAnalysis.StandardType.GGQTwoTBCF4Cent
public import Certificates.Certificate2264
public import Certificates.Certificate2267
public import Certificates.Certificate3951
public import Certificates.Certificate8033
public import Certificates.Certificate8064

import CFSG.LocalAnalysis.StandardType.GGQTwoAssemble
import CFSG.LocalAnalysis.StandardType.GGQTwoCavImage
import CFSG.LocalAnalysis.StandardType.GGCorFourTwoTableBReduce
import CFSG.LocalAnalysis.StandardType.GGTableBNoncyclic
import CFSG.LocalAnalysis.StandardType.GGTableBF4Basic
import CFSG.LocalAnalysis.StandardType.GGTableBF4TwoBstar
import CFSG.LocalAnalysis.StandardType.GGTableBF4TwoRank
import CFSG.LocalAnalysis.StandardType.GGF4ThreeNbrRank
import CFSG.LocalAnalysis.StandardType.GGF4ThreeSCCube
import CFSG.LocalAnalysis.StandardType.GGF4ThreeSCCubeHolds
import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.StandardType.GGQ2CentPort

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley

theorem actionThree_adjointF4Two
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2)
    {A : Subgroup (MulAut (adjointGroup .F4 K))} (hA : IsElemAbelian 3 A)
    (hcard : 3 ^ 4 ≤ Nat.card A) : actionThree A := by
  let c : adjointGroup .F4 K →* MulAut (adjointGroup .F4 K) := MulAut.conj
  have hinj : Function.Injective c :=
    mulAut_conj_injective (CFSG.LieType.Chevalley.center_adjointGroup_eq_bot (τ := .F4) (K := K))
  have hAinn : A ≤ c.range := fun a ha =>
    TableBF4Two.mem_range_conj_of_pow_three hK (hA.2 a ha)
  have hEmap : (A.comap c).map c = A := Subgroup.map_comap_eq_self hAinn
  have hEel : IsElemAbelian 3 (A.comap c) := hA.comap hinj
  have hEcard : Nat.card (A.comap c) = 3 ^ 4 := by
    refine le_antisymm (TableBF4Two.card_le_adjointF4 hK hEel) ?_
    rw [← Subgroup.card_map_of_injective (f := c) hinj, hEmap]
    exact hcard
  have hC := TBCF4.ggTBC_F4Two_centralizer_le hK hEel hEcard
  intro r hfix _
  have hcomm : ∀ e ∈ A.comap c, e * r = r * e := by
    intro e he
    have hre : c e r = r := hfix (c e) (Subgroup.mem_comap.mp he)
    have h1 : e * r * e⁻¹ = r := by simpa [c, MulAut.conj_apply] using hre
    calc e * r = (e * r * e⁻¹) * e := by group
      _ = r * e := by rw [h1]
  exact Subgroup.mem_comap.mp (hC (Subgroup.mem_centralizer_iff.mpr hcomm))

theorem f4TwoInput_holds :
    f4TwoInput := by
  intro G _ _ p B Bs x L D J hS hon R _ θ hN
  have hp3 : p = 3 := ggQ2_pThree hS
  subst hp3
  obtain ⟨hperf, lab, hlab, hraw⟩ := hon
  obtain ⟨-, -, -, -, -, -, -, ⟨hq2, htag⟩, -, -⟩ := largeEvenRawDatum_exists hraw
  have hn : lab.n = 1 := by
    have h1 : 1 ≤ lab.n := hlab.1
    have h2 : lab.n < 2 := hq2
    omega
  have hM : GGF4ThreeMarking Bs L := by
    refine ⟨hperf, lab, hlab, largeEvenRawDatum_mono ?_ hraw⟩
    rintro R' _ I F ⟨hs, hna, θ', -, hBsN, hind⟩
    exact ⟨hs, hna, θ', ⟨htag, rfl, by rw [hn]; norm_num⟩, hBsN, hind⟩
  have hγ : 3 ^ 4 ≤ Nat.card (ggGamma L hN).range :=
    ggF4Three_rank_of_marking (ggF4ThreeSCTransvInput_of_cube ggF4ThreeSCCubeInput_holds)
      hS.1.1 hS.1.2.2.2.1 hM hN
  obtain ⟨t, rk, n⟩ := lab
  dsimp only at hn htag
  subst hn
  obtain rfl : t = .F4 := htag
  obtain ⟨K, _, _, hK, -, -, θ₀, -⟩ := hraw
  have hK2 : Nat.card K = 2 := by simpa using hK
  have : CharP K 2 := charP_two_of_card (m := 1) (by rw [hK2, pow_one])
  let θF : L ⧸ Subgroup.center L ≃* adjointGroup .F4 K :=
    θ₀.trans (TableBF4.recipeEquiv K)
  have hA : IsElemAbelian 3 (ggBeta L θF hN).range :=
    isElemAbelian_range_ggBeta θF hS.1.1.2.1.2.1 hN
  have hAcard : 3 ^ 4 ≤ Nat.card (ggBeta L θF hN).range := by
    rw [QTwoCav.beta_card hperf θF hN, ← QTwoCav.gamma_card hN]
    exact hγ
  exact actionThree_ggBeta_congr θ θF hN (actionThree_adjointF4Two hK2 hA hAcard)

end CFSG.StandardType.GGQ2CentPort

end
