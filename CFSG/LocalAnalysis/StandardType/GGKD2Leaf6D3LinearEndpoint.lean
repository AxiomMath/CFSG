module

public import CFSG.LocalAnalysis.StandardType.GGKD2Leaf6D3Contracts
public import CFSG.LocalAnalysis.StandardType.GGKD2LinearLemmas1615

public section

namespace S2MathAs3_1624

noncomputable section

theorem linearA1EightImpossible_of_component (h : LinearComponentContract) :
    LinearA1EightImpossible := by
  intro K _ _ _ d hd S κ hnc _hcube hSnorm J hJ hlabel
  obtain ⟨m, E, hEfield, hEalg, hEfin, hm, _hd3m, hcubic, hQ⟩ :=
    h K d hd S κ hnc _hcube hSnorm J hJ
  letI : Field E := hEfield
  letI : Algebra K E := hEalg
  letI : Finite E := hEfin
  have h2E : (2 : E) = 0 := by
    have hmap : algebraMap K E (2 : K) = (2 : E) := map_natCast (algebraMap K E) 2
    have h2K : (2 : K) = 0 := CharP.cast_eq_zero K 2
    calc (2 : E) = algebraMap K E (2 : K) := hmap.symm
      _ = algebraMap K E 0 := congrArg (algebraMap K E) h2K
      _ = 0 := map_zero _
  obtain ⟨eStated⟩ :=
    CFSG.LieType.SemisimpleCentralizers.Held.nonempty_quotientCenter_equiv_statedProj
      (MulEquiv.subgroupCongr (CFSG.Assembly.largeEvenSLGroup_eq_statedSL (K := E) m))
  obtain ⟨eQ⟩ := hQ
  have φ : (↥J ⧸ Subgroup.center ↥J) ≃*
      CFSG.Open.StatedProj (CFSG.Open.StatedSL m E) := eQ.trans eStated
  obtain ⟨_hm2, hE8⟩ :=
    CFSG.StandardType.KD2Pieces1615.kd2Lin_numerology h2E hm φ hlabel
  have hKpow : Nat.card K ^ 3 = 8 := by
    rw [← hcubic.2.2, hE8]
  have hK2 : Nat.card K = 2 := by
    have h : Nat.card K ^ 3 = 2 ^ 3 := by
      rw [hKpow]
      norm_num
    exact (Nat.pow_left_inj (by norm_num : (3 : ℕ) ≠ 0)).mp h
  have hKunits : Nat.card Kˣ = 1 := by
    rw [Nat.card_units, hK2]
  haveI : Subsingleton Kˣ :=
    Finite.card_le_one_iff_subsingleton.mp (by rw [hKunits])
  have hκ1 : κ = 1 := Subsingleton.elim κ 1
  exact hnc 1 (by rw [one_pow, hκ1])

end

end S2MathAs3_1624

end
