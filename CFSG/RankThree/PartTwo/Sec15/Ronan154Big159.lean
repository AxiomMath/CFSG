module

public import CFSG.RankThree.PartTwo.Sec15.Ronan153BigDefs
public import CFSG.RankThree.PartTwo.Sec15.Item158Res2Proof159
import CFSG.RankThree.PartTwo.Sec13.Item131Facts
import CFSG.RankThree.PartTwo.Sec13.Item13Sporadic
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
public import CFSG.RankThree.PartTwo.Sec15.Item1513ProofTools
public import CFSG.RankThree.PartTwo.Sec15.Ronan154BigDefs

public section

namespace CFSG.RankThree.PartTwo.Sec15.Ronan154Big

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.GH74.GLS
open CFSG.RankThree.PartTwo.Sec15.Proof159

variable {G : Type} [Group G] [Finite G]

theorem false_of_ctx159_big (hY0 : Step159Y0) (hW : Step159W) (hclaim : Step159Claim)
    (hS : Step159S) {A L : Subgroup G} {c : G} (ctx : Ctx159 G A c L)
    (h149 : Item149 A (lB A)) (h153 : Ronan153Big.Item153Big A (lB A))
    (h1411 : Item1411_1 A (lB A)) (hbig : Y4BigNHJR) : False := by
  have h := ctx.toSec15R
  obtain ⟨Y₀, hY₀⟩ := hY0 G A c L ctx
  obtain ⟨Y, -, hY⟩ := Finite.exists_le_maximal (p := (· ∈ scriptY0 A (lB A))) hY₀
  have hYb : Big152 Y := hbig G A c L h (not_allPointsHJ_of_ctx159 ctx) Y hY.prop.1
  obtain ⟨w, hw, hV⟩ := hW G A c L ctx
  have hcl := hclaim G A c L ctx
  obtain ⟨S, hSG, hwS⟩ := hS G A c L ctx w hw (hcl w hw) hV
  set X := oPrimeResidualOf 3 (delta A (lB A) (Subgroup.normalizer (Y : Set G))) with hXdef
  have hbot : (⊥ : Subgroup G) ∈
      scriptQPi A (lB A) (Subgroup.normalizer (X : Set G)) (piOf 2) := by
    refine ⟨⟨⟨bot_mem_invariantPiSubgroups ⊤ A (piCompl 3), fun B _ => ?_⟩, bot_le⟩,
      (bot_mem_invariantPiSubgroups ⊤ A (piOf 2)).2.1⟩
    rw [bot_inf_eq]
    exact bot_le
  obtain ⟨SY, -, hSY⟩ := Finite.exists_le_maximal
    (p := (· ∈ scriptQPi A (lB A) (Subgroup.normalizer (X : Set G)) (piOf 2))) hbot
  obtain ⟨hM1, hS2, -⟩ := h153 Y hY hYb
  obtain ⟨hSYG, hSYN⟩ := hS2 SY hSY
  obtain ⟨x, hx, hxS⟩ := h1411 S hSG SY hSYG
  have hxW : x ∈ Subgroup.normalizer (A : Set G) := hx.1
  have hw' : IsW159 A L (x * w * x⁻¹) := isW159_conj ctx.normalizer_le_inf hw hxW
  have hw'S : x * w * x⁻¹ ∈ Subgroup.normalizer (SY : Set G) := by
    rw [hxS]
    exact mem_normalizer_map_conj hwS x
  have hw'X : x * w * x⁻¹ ∈ Subgroup.normalizer (X : Set G) :=
    hSYN (Proof1513.mem_normalizer_sup hw'.1 hw'S)
  obtain ⟨hV3, hYV⟩ := delta_mem_scriptY3 h.toSec14Std h149 hY hM1
  have hw'V : x * w * x⁻¹ ∈ Subgroup.normalizer
      ((delta A (lB A) (Subgroup.normalizer (X : Set G)) : Subgroup G) : Set G) :=
    mem_normalizer_delta hw'.1 (Subgroup.le_normalizer hw'X)
  have h0 := hcl _ hw' _ hV3 hw'V
  exact ne_bot_of_mem_scriptY0 hY.prop (le_bot_iff.mp (h0 ▸ hYV))

section Certificates


theorem rank3II_15_9_of_big (h131 : Item131) (h133 : Item133) (hY0 : Step159Y0)
    (hW : Step159W) (hclaim : Step159Claim) (hS : Step159S) {A L : Subgroup G} {c : G}
    (h : Sec15R G A c L) (h149 : Item149 A (lB A)) (h153 : Ronan153Big.Item153Big A (lB A))
    (h1411 : Item1411_1 A (lB A)) (hbig : Y4BigNHJR) : Item159 A c L := by
  intro hirr h9
  have hD := h.toSec13Data
  have hcL : c ∉ L := h.hypS.2.2 c h.zpowers_mem_omegaA L h.mem_lA
  obtain ⟨hprod, htypes⟩ := Proof1513.cases_of_irreducible h131 h h9 hirr
  rcases h133 G A c L hD h.hypS_or_hypT with hWH | ⟨hW4, ⟨e7⟩, h3, htr, -⟩ |
      ⟨-, hBW, hO3, hO9, hWst, hΩ3, hn9, hprod', htypes'⟩ | hPGL | ⟨⟨e12⟩⟩ | ⟨⟨eJ⟩⟩
  · exact Or.inl hWH
  ·
    obtain ⟨hS7, hZ7⟩ := isPerfect_center_alt7
    obtain ⟨-, -, -, ⟨ψ⟩⟩ := facts_of_prod hD hS7 hZ7 e7
    exact Or.inr (Or.inl ⟨⟨ψ⟩, hW4, h3, htr⟩)
  ·
    refine Or.inr (Or.inr ?_)
    by_contra hn3
    exact false_of_ctx159_big hY0 hW hclaim hS
      { h with
        irreducible := hirr
        card_inf := h9
        normalizer_le_inf := hBW
        isElemAbelian_oThree := hO3
        card_oThree := hO9
        wStar_eq := hWst
        omegaA_eq := hΩ3
        ncard_omegaA := hn9
        prod := hprod'
        types := htypes'
        not_three := hn3 }
      h149 h153 h1411 hbig
  · exact (Proof1514.false_of_prod_of_isZ3PGLThreePi hD hcL hprod hPGL).elim
  ·
    exfalso
    obtain ⟨-, ⟨hM12p, hM12z⟩, -⟩ := sporadicModels131
    obtain ⟨-, -, -, ⟨ψ⟩⟩ := facts_of_prod hD hM12p hM12z e12
    rcases htypes with ⟨p, e, hp, -, hL3⟩ | ⟨⟨χ⟩⟩ | ⟨⟨χ⟩⟩
    · exact KFacts.KS14.not_isoLThreePi_M12 p e (Proof1511.isoLThreePi_of_mulEquiv ψ hL3)
    · exact (Proof1514.isEmpty_mulEquiv_M12_of_A7 χ).false ψ
    · exact (Proof1514.isEmpty_mulEquiv_M12_of_M22 χ).false ψ
  ·
    exfalso
    obtain ⟨-, -, ⟨hJ2p, hJ2z⟩⟩ := sporadicModels131
    obtain ⟨-, -, -, ⟨ψ⟩⟩ := facts_of_prod hD hJ2p hJ2z eJ
    obtain ⟨hJL, hJA, hJM⟩ := KFacts.KS14.ks17J2NotList
    rcases htypes with ⟨p, e, hp, -, hL3⟩ | ⟨⟨χ⟩⟩ | ⟨⟨χ⟩⟩
    · exact hJL p e (Proof1511.isoLThreePi_of_mulEquiv ψ hL3)
    · exact hJA.false (ψ.symm.trans χ)
    · exact hJM.false (ψ.symm.trans χ)

theorem item159R_of_big (h131 : Item131) (h133 : Item133) (h149 : Sec16.Item149S14)
    (h153 : Ronan153Big.Item153BigR) (h1411 : Item1411_1R) (hY0 : Step159Y0) (hW : Step159W)
    (hclaim : Step159Claim) (hS : Step159S) (hbig : Y4BigNHJR) : Item159R :=
  fun G _ _ A c L h => rank3II_15_9_of_big h131 h133 hY0 hW hclaim hS h
    (h149 G A c L h.toSec14Std) (h153 G A c L h) (h1411 G A c L h) hbig

theorem item159R_of_res2_big (h131 : Item131) (h133 : Item133) (h149 : Sec16.Item149S14)
    (h153 : Ronan153Big.Item153BigR) (h1411 : Item1411_1R) (h146 : Item146R)
    (hY0 : Step159Y0) (hW : Step159WT) (hclaim : Step159ClaimK) (hbig : Y4BigNHJR) :
    Item159R :=
  item159R_of_big h131 h133 h149 h153 h1411 hY0 (step159W_of hW) (step159Claim_of hclaim)
    (step159S_of h146) hbig

end Certificates

end CFSG.RankThree.PartTwo.Sec15.Ronan154Big
