module

public import CFSG.RankThree.PartTwo.Sec14.Item1413Res5ProofNonsolv
import CFSG.RankThree.PartTwo.Sec12.Item128Bar

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.PartTwo.Late
  CFSG.GH74.GLS

theorem item1411_3NHJR_of_F (h422 : Sec4.Item4_22) (h45 : Sec4.Item4_5) (h146 : Item146S14)
    (hbot : Item145BotS14) (hcent : Claim1411NonsolvXCentFR) (h1421 : Step1421R)
    (h1422 : Step1422R) : Item1411_3NHJR := by
  intro G _ _ A c L hR _ hX
  have hS := hR.toSec14Std
  have hD := hS.toSec13Data
  by_contra hno
  have hfail : Fail1411 A (lB A) := ⟨hX, fun Y hYΔ hY hO hres => by
    by_contra hT
    exact hno ⟨Y, hYΔ, hY, hO, hres, hT⟩⟩
  have h2 : Item1411_2 A (lB A) :=
    rank3II_14_11_2_of_cent hS (h146 G A c L hS) (hbot G A c L hS) (hcent G A c L hR hfail)
  obtain ⟨F, hFΓ⟩ := rank3II_14_12_nonempty hS.isE27 h2 hX
  obtain ⟨-, -, c', rfl, -⟩ := hFΓ.1
  have hc'A : c' ∈ A := (zpowers_mem_omegaA_iff.mp hFΓ.1).1
  have hAc' : A ≤ Subgroup.centralizer ({c'} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hD.commute hx hc'A)
  obtain ⟨L₀, hL₀⟩ := Sec12.exists_mem_lA422 h422 h45 hD.toPartTwoStanding hD.mem_partTwoF
    hD.card_eq hFΓ.1
  have hL' := Sec12.mem_lA_of_mem_lA422 hAc' hL₀
  obtain ⟨e⟩ := h1421 G A c L hR hfail c' hFΓ L₀ hL'
  exact (h1422 G A c L hR hfail c' hFΓ L₀ hL').false e

end CFSG.RankThree.PartTwo.Sec14
