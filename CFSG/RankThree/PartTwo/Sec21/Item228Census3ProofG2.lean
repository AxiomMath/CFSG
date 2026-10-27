module

public import CFSG.RankThree.PartTwo.Sec21.Item228CensusProofSplit
public import CFSG.RankThree.PartTwo.Sec21.Item228Census2ProofOddTools
public import CFSG.RankThree.PartTwo.Sec21.Item228Census3ProofTools
public import CFSG.RankThree.PartTwo.Sec11.KS11Lie4ProofTwist
public import CFSG.RankThree.PartTwo.Sec21.Item228CensusProofCharThree

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof

namespace Item228Census3Proof

theorem finite_adjointGroupG2 {K : Type} [Field K] [Finite K] :
    Finite (adjointGroup .G2 K) := by
  have : Finite (ModGL .G2 K) := finite_modGL
  exact Subtype.finite

theorem noL2Config228_threeA {K : Type} [Field K] [Finite K]
    {z : adjointGroup .G2 K}
    (h : ∃ N : Subgroup (adjointGroup .G2 K),
        N ≤ Subgroup.centralizer ({z} : Set (adjointGroup .G2 K)) ∧
        (∀ x ∈ Subgroup.centralizer ({z} : Set (adjointGroup .G2 K)),
          ∀ y ∈ Subgroup.centralizer ({z} : Set (adjointGroup .G2 K)),
            x * y * x⁻¹ * y⁻¹ ∈ N) ∧
        CFSG.IsQuasisimple N ∧
        ∃ x ∈ N, (∀ n ∈ N, x * n = n * x) ∧ x ≠ 1 ∧ x ^ 3 = 1) :
    NoL2Config228
      (inSubgroup perfectResidual (Subgroup.centralizer ({z} : Set (adjointGroup .G2 K)))) := by
  have : Finite (adjointGroup .G2 K) := finite_adjointGroupG2
  obtain ⟨N, hNC, hcomm, hq, x, hxN, hxc, hx1, -⟩ := h
  have hN : ⁅N, N⁆ = N := Subgroup.isPerfect_iff.mp hq.1
  have heq := inSubgroup_perfectResidual_eq_of_commutator hNC hN hcomm
  refine Item228Census2Proof.noL2Config228_of_mulEquiv (MulEquiv.subgroupCongr heq) ?_
  refine Item228Census2Proof.noL2Config228_of_quasisimple hq.1 hq.2.1 fun hbot => ?_
  have hxZ : (⟨x, hxN⟩ : N) ∈ Subgroup.center N :=
    Subgroup.mem_center_iff.mpr fun n => Subtype.ext (hxc n n.2).symm
  rw [hbot, Subgroup.mem_bot] at hxZ
  exact hx1 (congrArg Subtype.val hxZ)

section G2


variable {K : Type} [Field K] [Finite K]

theorem noL2Config228_threeB (hB : G2ThreeBCent) (hK3 : ringChar K ≠ 3)
    (hK4 : 4 ≤ Nat.card K) (h2 : (2 : K) ≠ 0) {z : adjointGroup .G2 K} (hzM : z ∈ g2LongSL2 K)
    (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1) :
    NoL2Config228
      (inSubgroup perfectResidual (Subgroup.centralizer ({z} : Set (adjointGroup .G2 K)))) := by
  have hSC : g2ShortSL2 K ≤ Subgroup.centralizer ({z} : Set (adjointGroup .G2 K)) := by
    intro s hs
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact g2Short_commute_g2Long hs hzM
  have hS : ⁅g2ShortSL2 K, g2ShortSL2 K⁆ = g2ShortSL2 K :=
    Subgroup.isPerfect_iff.mp (isQuasisimple_g2ShortSL2 hK4).1
  have heq := inSubgroup_perfectResidual_eq_of_commutator hSC hS (hB K hK3 hK4 z hzM hz3 hz1).1
  obtain ⟨e⟩ := nonempty_mulEquiv_g2ShortSL2 (K := K)
  exact Item228Census2Proof.noL2Config228_of_mulEquiv ((MulEquiv.subgroupCongr heq).trans e.symm)
    (Item228Census2Proof.noL2Config228_SL2 h2)

theorem noL2Normal228_adjointG2
    (hC : G2ThreeConjSL2) (hA : G2ThreeACent) (hK3 : ringChar K ≠ 3) (hK4 : 4 ≤ Nat.card K)
    (h2 : (2 : K) ≠ 0) : NoL2Normal228 (adjointGroup .G2 K) := by
  have : Finite (adjointGroup .G2 K) := finite_adjointGroupG2
  refine Item228Census2Proof.noL2Normal228_of_noL2Config center_adjointGroup_eq_bot
    fun y hy => ?_
  have hy3 : y ^ 3 = 1 := hy ▸ pow_orderOf_eq_one y
  have hy1 : y ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hy
    norm_num at hy
  obtain ⟨g, hg⟩ := hC K hK3 hK4 y hy3 hy1
  set z := MulAut.conj g y with hz
  have hzg : z = g * y * g⁻¹ := rfl
  have hz3 : z ^ 3 = 1 := by rw [← map_pow, hy3, map_one]
  have hz1 : z ≠ 1 := fun h1 => hy1 ((MulAut.conj g).injective (h1.trans (map_one _).symm))
  refine Item228Census2Proof.noL2Config228_of_mulEquiv (perfectResidualCentralizerEquiv
    (MulAut.conj g) y) ?_
  rw [← hz]
  rcases hg with hS | hM
  · rw [← hzg] at hS
    exact noL2Config228_threeA (hA K hK3 hK4 z hS hz3 hz1)
  · rw [← hzg] at hM
    exact noL2Config228_threeB g2ThreeBCent_holds hK3 hK4 h2 hM hz3 hz1

end G2

end Item228Census3Proof

open Item228Census3Proof

section Census


theorem census228G2Odd_of_minus (hC : G2ThreeConjSL2Minus) (hA : G2ThreeACentMinus) :
    Census228G2Odd := by
  intro p _ hp Y _ _ hY
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hY
  have hp' : p.Prime := Fact.out
  have : Fintype K := Fintype.ofFinite K
  have hKp : Fintype.card K = p := by rw [Fintype.card_eq_nat_card, hK, pow_one]
  have : CharP K p := charP_of_card_eq_prime hKp
  have hchar : ringChar K = p := ringChar.eq K p
  have hK3 : ringChar K ≠ 3 := by omega
  have hK4 : 4 ≤ Nat.card K := by rw [hK, pow_one]; omega
  have h2 : (2 : K) ≠ 0 := by
    intro h0
    have h2' : ((2 : ℕ) : K) = 0 := by exact_mod_cast h0
    rw [CharP.cast_eq_zero_iff K p] at h2'
    have := Nat.le_of_dvd (by norm_num) h2'
    omega
  let e' : Y ≃* adjointGroup .G2 K := e.trans ((QuotientGroup.quotientMulEquivOfEq
    center_adjointGroup_eq_bot).trans QuotientGroup.quotientBot)
  exact Or.inr (Item228CensusProof.noL2Normal228_of_mulEquiv e'
    (noL2Normal228_adjointG2 (g2ThreeConjSL2_of_minus hC) (g2ThreeACent_of_minus hA) hK3 hK4 h2))

end Census

end CFSG.RankThree.PartTwo.Sec21
