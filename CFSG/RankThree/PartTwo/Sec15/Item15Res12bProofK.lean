module

public import CFSG.RankThree.PartTwo.Sec15.Item15Res12bProofDefs
import CFSG.RankThree.PartTwo.Sec15.Item1515ResProofCover
import CFSG.RankThree.PartTwo.Sec14.Item14Tools
public import CFSG.RankThree.PartTwo.Sec17.RouteForms

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

theorem step1523KY4R_of_read (h143 : Concl143S14) (hK : Step1523KReadY4) : Step1523KY4R := by
  intro G _ _ A c L h _ hJ Y hY hm
  obtain ⟨d, hdA, hd1, hdc, hdΩ, hK4, hKtype, hYK, hYtype⟩ := hK G A c L h hJ Y hY hm
  have hY4 : Y ∈ scriptY4 A (lB A) := hY.prop.1
  have hZY : oPrimeResidualOf 3 (Y ⊓ k1523 A d) ≤ Y :=
    (oPrimeResidualOf_le_self 3 _).trans inf_le_left
  have hcov : Y ≤ oPrimeResidualOf 3 (Y ⊓ k1523 A d) ⊔ CFSG.Open.pCoreOf 2 Y :=
    Proof1515Res.le_oRes3_sup hY4.2.1 inf_le_left (CFSG.LieType.BorelTits.pCoreOf_le 2 Y)
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y) hYK.le
  have hAK : A ≤ Subgroup.normalizer ((k1523 A d : Subgroup G) : Set G) := hK4.1.2
  have hAZ : A ≤ Subgroup.normalizer ((oPrimeResidualOf 3 (Y ⊓ k1523 A d) : Subgroup G) :
      Set G) :=
    Proof1515Res.le_normalizer_oRes3 (Late.le_normalizer_inf hY4.1.2 hAK)
  have hKΔ : k1523 A d ≤ delta A (lB A) (Subgroup.centralizer {d}) :=
    oPrimeResidualOf_le_self 3 _
  have hmem : ∀ R : Subgroup G, R ≤ oPrimeResidualOf 3 (Y ⊓ k1523 A d) → ¬ 3 ∣ Nat.card R →
      A ≤ Subgroup.normalizer (R : Set G) → R ∈ scriptQ A (lB A) := by
    intro R hRZ hR3 hAR
    have hRΔ : R ≤ delta A (lB A) (Subgroup.centralizer {d}) :=
      hRZ.trans ((oPrimeResidualOf_le_self 3 _).trans (inf_le_right.trans hKΔ))
    have hRinv : R ∈ invariantPiSubgroups (delta A (lB A) (Subgroup.centralizer {d})) A
        (piCompl 3) := ⟨hRΔ, (isPiSubgroup_piCompl_iff Nat.prime_three R).mpr hR3, hAR⟩
    obtain ⟨Q, hQ, hRQ⟩ := exists_le_mem_maxInvariantPiSubgroups hRinv
    exact mem_scriptQ_of_le (h143 G A c L h.toSec14Std d hdA hd1 hdΩ Q hQ).1 hRQ hAR
  have hX4 : oPrimeResidualOf 3 (Y ⊓ k1523 A d) ∈ scriptY4 A (lB A) :=
    Proof1515Res.mem_scriptY4_of_le_cover hY4 hZY hcov hAZ
      (Proof1515Res.oRes3_idem _).symm hmem
  exact ⟨d,
    { mem_d := hdA
      ne_d := hd1
      central_d := hdc
      mem_k := hK4
      type_k := hKtype
      mem_x := hX4
      eq_y := le_antisymm hcov (sup_le hZY (CFSG.LieType.BorelTits.pCoreOf_le 2 Y))
      type_y := hYtype }⟩

end CFSG.RankThree.PartTwo.Sec15
