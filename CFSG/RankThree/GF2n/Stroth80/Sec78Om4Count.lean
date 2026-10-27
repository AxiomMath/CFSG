module

public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphOmegaMinusPiecesOrders
public import CFSG.RankThree.GF2n.Stroth80.Sec83Card

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Open.StatedAPI CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem sec7ctr_card_eq_mul_range {R N : Subgroup G} {H : Type*} [Group H] (hNR : N ≤ R)
    (φ : ↥R →* H) (hker : φ.ker = N.subgroupOf R) :
    Nat.card ↥R = Nat.card ↥N * Nat.card ↥φ.range := by
  have h := Subgroup.card_ker_mul_card_range φ
  rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNR).toEquiv] at h
  exact h.symm

theorem sec7ctr_card_om4 {R N : Subgroup G} (hNR : N ≤ R) {K : Type} [Field K] [Finite K]
    [CharP K 2] {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (φ : ↥R →* GL (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) K)
    (hrange : φ.range = StatedOmega (StatedQuadMinus 2 K b c)) (hker : φ.ker = N.subgroupOf R) :
    Nat.card ↥R = Nat.card ↥N * (Nat.card K ^ 2 * ((Nat.card K ^ 2) ^ 2 - 1)) := by
  rw [sec7ctr_card_eq_mul_range hNR φ hker, hrange,
    CFSG.SeitzReduction.F4Pilot.natCard_statedOmega_quadMinus_two hirr,
    CFSG.SeitzReduction.F4Pilot.ordSL_two]

theorem sec7ctr_conj_B_sup_Z {V : Subgroup G} (hBV : B ≤ V) {ν : G}
    (hν : ∀ v ∈ V, ⁅ν, v⁆ ∈ Z) : conjSubgroup ν B ⊔ Z = B ⊔ Z := by
  apply le_antisymm
  · refine sup_le ?_ le_sup_right
    intro x hx
    rw [mem_conjSubgroup] at hx
    have e : x = ⁅ν, ν⁻¹ * x * ν⁆ * (ν⁻¹ * x * ν) := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact (B ⊔ Z).mul_mem (Subgroup.mem_sup_right (hν _ (hBV hx))) (Subgroup.mem_sup_left hx)
  · refine sup_le ?_ le_sup_right
    intro b hb
    have hz : ⁅ν, b⁆ ∈ Z := hν b (hBV hb)
    have e : b = ⁅ν, b⁆⁻¹ * (ν * b * ν⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact (conjSubgroup ν B ⊔ Z).mul_mem (Subgroup.mem_sup_right (Z.inv_mem hz))
      (Subgroup.mem_sup_left (mem_conjSubgroup.mpr (by
        have e : ν⁻¹ * (ν * b * ν⁻¹) * ν = b := by group
        rw [e]
        exact hb)))

theorem sec7ctr_pin {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K] [Finite K]
    {X : Subgroup (GL ι K)} {R V N : Subgroup G} (h : NaturalRep K X R V Z N)
    (hK : Nat.card K = Nat.card Z) (hZV : Z ≤ V) (hq : 2 ≤ Nat.card Z) {k : ℕ}
    (hV : Nat.card ↥V = Nat.card ↥Z * Nat.card ↥Z ^ k) : Fintype.card ι = k := by
  have h1 := card_of_naturalRep h hZV hK
  rw [h1] at hV
  exact Nat.pow_right_injective hq (Nat.eq_of_mul_eq_mul_left (by omega) hV)

end CFSG.RankThree.GF2n.Stroth80
