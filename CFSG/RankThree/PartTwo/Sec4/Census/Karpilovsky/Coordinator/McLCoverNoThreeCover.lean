module

public import CFSG.Sporadic.Recognition.LyonsAmalgamExtOutMcL
public import CFSG.Quasithin.Vol2.Ch11SecJ4MultA

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator

open Subgroup CFSG.Quasithin.Vol2.Ch11.SecS.J4Mult CFSG.Sporadic.Recognition
open scoped commutatorElement

theorem mem_center_of_perfect_central_ext {K Q : Type*} [Group K] [Group Q] [Group.IsPerfect K]
    (π : K →* Q) (hker : π.ker ≤ center K) {z : K} (hz : π z ∈ center Q) : z ∈ center K := by
  have hc : ∀ g : K, ⁅z, g⁆ ∈ center K := fun g => hker (by
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact (Subgroup.mem_center_iff.1 hz (π g)).symm)
  let φ : K →* ↥(center K) :=
    { toFun := fun g => ⟨⁅z, g⁆, hc g⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by
        change ⁅z, a * b⁆ = ⁅z, a⁆ * ⁅z, b⁆
        have hb := Subgroup.mem_center_iff.1 (hc b) a
        have e : ⁅z, a * b⁆ = ⁅z, a⁆ * (a * ⁅z, b⁆ * a⁻¹) := by
          simp only [commutatorElement_def]
          group
        rw [e, hb, mul_inv_cancel_right]) }
  have hker' : commutator K ≤ φ.ker := Abelianization.commutator_subset_ker φ
  rw [Group.IsPerfect.commutator_eq_top] at hker'
  refine Subgroup.mem_center_iff.2 fun g => ?_
  have h1 : φ g = 1 := hker' (Subgroup.mem_top g)
  have h2 : ⁅z, g⁆ = 1 := congrArg Subtype.val h1
  rw [commutatorElement_eq_one_iff_mul_comm] at h2
  exact h2.symm

theorem card_eq_card_mul_card_ker' {G H : Type*} [Group G] [Group H] (f : G →* H)
    (hf : Function.Surjective f) : Nat.card G = Nat.card H * Nat.card f.ker := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv]

theorem noPerfectCentralCover_three_of_central_quotient {Q J : Type} [Group Q] [Group J]
    [Finite Q] (q : Q →* J) (hq : Function.Surjective q) (hqc : q.ker ≤ center Q)
    (hq3 : Nat.card q.ker = 3)
    (hJ : ∀ (E : Type) [Group E] [Group.IsPerfect E] (f : E →* J), Function.Surjective f →
      f.ker ≤ center E → Nat.card f.ker ∣ 3) :
    NoPerfectCentralCover 3 Q := by
  intro K _ π hπ hK hc hcard
  have : Finite π.ker := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have : Finite (K ⧸ π.ker) :=
    Finite.of_injective (QuotientGroup.kerLift π) (QuotientGroup.kerLift_injective π)
  have : Finite K := Finite.of_equiv _ (Subgroup.groupEquivQuotientProdSubgroup (s := π.ker)).symm
  have : Finite J := Finite.of_surjective q hq
  have hf : Function.Surjective (q.comp π) := hq.comp hπ
  have hfc : (q.comp π).ker ≤ center K := fun z hz =>
    mem_center_of_perfect_central_ext π hc (hqc (MonoidHom.mem_ker.1 hz))
  have h1 := card_eq_card_mul_card_ker' π hπ
  have h2 := card_eq_card_mul_card_ker' q hq
  have h3 := card_eq_card_mul_card_ker' (q.comp π) hf
  rw [hcard] at h1
  rw [hq3] at h2
  have hJpos : 0 < Nat.card J := Nat.card_pos
  have h9 : Nat.card (q.comp π).ker = 9 := by
    have : Nat.card J * Nat.card (q.comp π).ker = Nat.card J * 9 := by
      rw [← h3, h1, h2]
      ring
    exact Nat.eq_of_mul_eq_mul_left hJpos this
  have hd := hJ K (q.comp π) hf hfc
  rw [h9] at hd
  omega

theorem noPerfectCentralCover_three_mclCover :
    NoPerfectCentralCover 3 McLMultiplier.MclCover := by
  have hP := McLMultiplier.isPresentation_mclGen_of_certificate
  have hwg := McLMultiplier.lift_mclCommW_of_certificate
  have hS : Subgroup.center CFSG.Sporadic.McL.J = ⊥ :=
    LyonsSims.center_eq_bot_of_equiv_mcl CFSG.Sporadic.McL.mclEquivJ.symm
  have hfin := LyonsSims.finite_mclCover
  have hqc := CFSG.LieType.Multipliers.coverMap_ker_le_center hP hwg
  refine noPerfectCentralCover_three_of_central_quotient
    (CFSG.LieType.Multipliers.coverMap hP hwg) (CFSG.LieType.Multipliers.coverMap_surjective hP hwg)
    hqc ?_ ?_
  · rw [LyonsSims.ker_eq_center_of_central_ker _ (CFSG.LieType.Multipliers.coverMap_surjective hP hwg)
      hqc hS]
    exact LyonsSims.card_center_mclCover
  · intro E _ _ f hf hfc
    exact McLMultiplier.card_ker_dvd_three_of_certificate f hf hfc

end CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator
