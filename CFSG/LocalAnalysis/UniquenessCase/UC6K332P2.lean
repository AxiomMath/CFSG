module

import CFSG.RankThree.PartTwo.Sec4.RonanK432RowSp4Even
import CFSG.RankThree.PartOne.FOC.SpOuter
import CFSG.RankThree.PartOne.S11c.Sec66Sp4
public import CFSG.Assembly.GL83LieDefs
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.Orders.Basic
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4Order
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogQuadraticDescent
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartOne.KC.LinearSubfieldInclusion
public import CFSG.RankThree.PartOne.S11c.Sec66TDefs
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.RankThree.PartTwo.Sec4.RonanK432Defs

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK432

open CFSG.Assembly.RankThreeEven (projSp)
open CFSG.Assembly.LowTwoRank (StatedProj StatedSp)
open CFSG.RankThree.PartOne.Sec66T (fixSub)
open CFSG.ComponentClassification.UnbalancedCatalog (descentField)

theorem outerRow_statedProj_sp_two_odd {K : Type} [Field K] [Finite K] {p e : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) (he : 1 ≤ e) (hK : Nat.card K = p ^ e) :
    OuterRow (StatedProj (StatedSp 2 K)) := by
  have hp5 : 5 ≤ p := by
    have h2 := hp.two_le
    by_contra h
    interval_cases p
    · exact hp2 rfl
    · exact hp3 rfl
    · exact absurd hp (by norm_num)
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    exact le_trans (by omega) (Nat.le_self_pow (by omega) p)
  refine outerRow_of_fixed_card_dvd (CFSG.RankThree.PartOne.Sec66T.sp4_center_eq_bot hK4)
    fun β hβ hout => ?_
  obtain ⟨σ, hσ, ⟨eF⟩⟩ := CFSG.RankThree.PartOne.FOC.fixedGroup_equiv hp he hK le_rfl
    Nat.prime_three (by norm_num) hβ hout
  refine ⟨fixSub β, Nat.card (StatedProj (StatedSp 2 (descentField σ))), fun x => Iff.rfl,
    (Nat.card_congr eF.toEquiv).dvd, ?_⟩
  obtain ⟨hdvd, hkcard⟩ :=
    CFSG.RankThree.PartOne.card_semilinearFixedSubfield hp he hK (rfl : orderOf σ = orderOf σ)
  have hk : Nat.card (descentField σ) = p ^ (e / orderOf σ) := hkcard
  have hT := CFSG.ComponentClassification.CatFactsSp4.two_mul_card_P
    (CFSG.ClassicalInvolution.two_ne_zero_of_card_eq_prime_pow hp hp2 hK)
  have hA := CFSG.ComponentClassification.CatFactsSp4.two_mul_card_P
    (CFSG.ClassicalInvolution.two_ne_zero_of_card_eq_prime_pow hp hp2 hk)
  rcases (Nat.dvd_prime Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hσ) with h1 | h3
  ·
    exfalso
    rw [h1, Nat.div_one, ← hK] at hk
    rw [hk, ← hT] at hA
    have htop : fixSub β = ⊤ := Subgroup.eq_top_of_card_eq _ (by
      rw [Nat.card_congr eF.toEquiv]
      omega)
    apply hout
    refine ⟨1, MulEquiv.ext fun x => ?_⟩
    have hx : x ∈ fixSub β := htop ▸ Subgroup.mem_top x
    rw [map_one, MulAut.one_apply]
    exact hx.symm
  · rw [h3] at hk hdvd
    rw [hk] at hA
    have hKe : Nat.card K = (p ^ (e / 3)) ^ 3 := by
      rw [hK, ← pow_mul, Nat.div_mul_cancel hdvd]
    rw [hKe] at hT
    have hq : ¬ 3 ∣ p ^ (e / 3) := fun h =>
      hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp
        (Nat.prime_three.dvd_of_dvd_pow h)).symm
    have h6 := evenSp4_three_mul_dvd _ hq
    rw [← hA, ← hT] at h6
    exact Nat.dvd_of_mul_dvd_mul_right (by norm_num : 0 < 2) (by
      rw [mul_assoc]
      exact h6)

end CFSG.RankThree.PartTwo.Sec4.RonanK432
