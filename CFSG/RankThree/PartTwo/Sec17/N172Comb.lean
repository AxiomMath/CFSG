module

public import CFSG.RankThree.PartTwo.Sec17.Item17Res11ProofHJ
import CFSG.RankThree.PartTwo.Sec17.Item17Res9ProofLd
import CFSG.RankThree.PartTwo.Sec14.Item1417
import CFSG.RankThree.PartTwo.Sec14.Item14J2
import CFSG.RankThree.PartTwo.Sec14.Item1411HJ
import CFSG.RankThree.PartTwo.Sec14.Item14Res7ProofMemFix
import CFSG.RankThree.PartTwo.Sec4.Sporadic.Item415
import CFSG.RankThree.PartTwo.Sec13.Item134Sylow
import CFSG.RankThree.PartTwo.Sec13.Item134Holds
import CFSG.RankThree.PartTwo.Sec13.Item13Sporadic
import CFSG.RankThree.PartTwo.Sec6.Item68
import CFSG.RankThree.PartTwo.Sec6.Item65Tools
import CFSG.RankThree.PartTwo.Sec17.Item176StepsProof172
import CFSG.RankThree.PartTwo.Sec4.Census.Lift46
import CFSG.Sporadic.J2
import CFSG.RankThree.PartTwo.Sec17.Item17Res11ProofSec
import CFSG.RankThree.Coprime.ThompsonElementaryComplement
import CFSG.RankThree.PartTwo.Sec14.Item14Tools
import CFSG.RankThree.GroupTheory.SteinbergBYHyperplaneResidual
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.Sec14.Item1411
import CFSG.RankThree.PartTwo.Sec14.Concl142NHJInner
import CFSG.RankThree.PartTwo.Sec5.Tools
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHermitianIsometry
import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
import CFSG.Quasithin.Background.Basic
import CFSG.RankThree.PartTwo.Sec14.Item142ResProofHJ
import CFSG.RankThree.PartTwo.Sec17.Item1711Proof
import CFSG.RankThree.PartTwo.Sec17.Item171StepsProofKM
import CFSG.RankThree.PartTwo.Sec17.Item17Res6ProofKMd
import CFSG.RankThree.PartTwo.Sec4.Census.Interface
import CFSG.RankThree.PartTwo.Sec4.Census.Interface46
import CFSG.RankThree.PartTwo.Sec6.Item612
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard

public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16 CFSG.RankThree.PartTwo.Late CFSG.GH74.GLS
open scoped commutatorElement

open scoped Pointwise

variable {G : Type} [Group G]

private theorem n172_closure_pair_eq_sup {c d : G} :
    Subgroup.closure ({c, d} : Set G) = Subgroup.zpowers c ⊔ Subgroup.zpowers d := by
  rw [Set.insert_eq, Subgroup.closure_union, ← Subgroup.zpowers_eq_closure,
    ← Subgroup.zpowers_eq_closure]

private theorem n172_coe_sup_eq_mul {c d : G} (hcd : Commute c d) :
    ((Subgroup.zpowers c ⊔ Subgroup.zpowers d : Subgroup G) : Set G) =
      (Subgroup.zpowers c : Set G) * (Subgroup.zpowers d : Set G) := by
  have hle : Subgroup.zpowers c ≤ Subgroup.normalizer (Subgroup.zpowers d : Set G) :=
    Subgroup.zpowers_le.mpr
      (CFSG.RankThree.PartTwo.Sec14.centralizer_singleton_le_normalizer_zpowers d
        (Subgroup.mem_centralizer_singleton_iff.mpr hcd.eq))
  exact Subgroup.coe_mul_of_left_le_normalizer_right _ _ hle

private theorem n172_mem_sup_pair {c d b : G} (hcd : Commute c d)
    (hb : b ∈ Subgroup.zpowers c ⊔ Subgroup.zpowers d) :
    ∃ x ∈ Subgroup.zpowers c, ∃ y ∈ Subgroup.zpowers d, x * y = b := by
  have hb' : b ∈ ((Subgroup.zpowers c ⊔ Subgroup.zpowers d : Subgroup G) : Set G) := hb
  rw [n172_coe_sup_eq_mul hcd] at hb'
  exact Set.mem_mul.mp hb'

private theorem n172_eq_one_of_mem_of_not_mem {L : Subgroup G} {c : G} (hc3 : orderOf c = 3)
    (hcL : c ∉ L) {x : G} (hxL : x ∈ L) (hx : x ∈ Subgroup.zpowers c) : x = 1 := by
  have hcard : Nat.card (Subgroup.zpowers c) = 3 := by rw [Nat.card_zpowers, hc3]
  have : Fact (Nat.card (Subgroup.zpowers c)).Prime := ⟨by rw [hcard]; exact Nat.prime_three⟩
  rcases Subgroup.eq_bot_or_eq_top_of_prime_card (L.subgroupOf (Subgroup.zpowers c)) with h | h
  · have hx' : (⟨x, hx⟩ : Subgroup.zpowers c) ∈ L.subgroupOf (Subgroup.zpowers c) :=
      Subgroup.mem_subgroupOf.mpr hxL
    rw [h] at hx'
    exact congrArg Subtype.val (Subgroup.mem_bot.mp hx')
  · exfalso
    apply hcL
    have hc' : (⟨c, Subgroup.mem_zpowers c⟩ : Subgroup.zpowers c) ∈
        L.subgroupOf (Subgroup.zpowers c) := by
      rw [h]
      exact Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.mp hc'

private theorem n172_zpowers_eq_of_mem_zpowers {b d : G} (hd3 : orderOf d = 3)
    (hb : b ∈ Subgroup.zpowers d) (hb1 : b ≠ 1) : Subgroup.zpowers b = Subgroup.zpowers d := by
  have hdiv : orderOf b ∣ orderOf d := orderOf_dvd_of_mem_zpowers hb
  rw [hd3] at hdiv
  have hb3 : orderOf b = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hdiv with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hb1
    · exact h
  have hfin : Finite ↥(Subgroup.zpowers d) :=
    Nat.finite_of_card_ne_zero (by rw [Nat.card_zpowers, hd3]; norm_num)
  apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hb)
  exact le_of_eq (by rw [Nat.card_zpowers, Nat.card_zpowers, hb3, hd3])

theorem card_sup_zpowers_of_not_mem {x y : G} (hxy : Commute x y) (hx3 : orderOf x = 3)
    (hy3 : orderOf y = 3) (hy : y ∉ Subgroup.zpowers x) :
    Nat.card ↥(Subgroup.zpowers x ⊔ Subgroup.zpowers y) = 9 := by
  have hset := n172_coe_sup_eq_mul hxy
  have hbij : Function.Bijective (fun p : ↥(Subgroup.zpowers x) × ↥(Subgroup.zpowers y) =>
      (⟨(p.1 : G) * (p.2 : G),
        mul_mem (Subgroup.mem_sup_left p.1.2) (Subgroup.mem_sup_right p.2.2)⟩ :
          ↥(Subgroup.zpowers x ⊔ Subgroup.zpowers y))) := by
    refine ⟨?_, ?_⟩
    · rintro ⟨a, b⟩ ⟨a', b'⟩ h
      have h' : (a : G) * (b : G) = (a' : G) * (b' : G) := congrArg Subtype.val h
      have hzy : (a' : G)⁻¹ * (a : G) = (b' : G) * (b : G)⁻¹ := by
        calc (a' : G)⁻¹ * (a : G) = (a' : G)⁻¹ * ((a : G) * (b : G)) * (b : G)⁻¹ := by group
          _ = (a' : G)⁻¹ * ((a' : G) * (b' : G)) * (b : G)⁻¹ := by rw [h']
          _ = (b' : G) * (b : G)⁻¹ := by group
      have hzY : (a' : G)⁻¹ * (a : G) ∈ Subgroup.zpowers y := by
        rw [hzy]
        exact mul_mem b'.2 (inv_mem b.2)
      have hz1 : (a' : G)⁻¹ * (a : G) = 1 :=
        n172_eq_one_of_mem_of_not_mem hy3 hy (mul_mem (inv_mem a'.2) a.2) hzY
      have hab : (a : G) = (a' : G) := (inv_mul_eq_one.mp hz1).symm
      rw [hab] at h'
      have hbb : (b : G) = (b' : G) := mul_left_cancel h'
      exact Prod.ext (Subtype.ext hab) (Subtype.ext hbb)
    · rintro ⟨w, hw⟩
      have hw' : w ∈ ((Subgroup.zpowers x ⊔ Subgroup.zpowers y : Subgroup G) : Set G) := hw
      rw [hset] at hw'
      obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_mul.mp hw'
      exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), Subtype.ext hab⟩
  calc Nat.card ↥(Subgroup.zpowers x ⊔ Subgroup.zpowers y)
      = Nat.card (↥(Subgroup.zpowers x) × ↥(Subgroup.zpowers y)) :=
        Nat.card_congr (Equiv.ofBijective _ hbij).symm
    _ = 9 := by rw [Nat.card_prod, Nat.card_zpowers, Nat.card_zpowers, hx3, hy3]

theorem isHyperplane_closure_pair {A : Subgroup G} {c d : G} (hA : Late.IsE27 A) (hcA : c ∈ A)
    (hdA : d ∈ A) (hc1 : c ≠ 1) (hd : d ∉ Subgroup.zpowers c) :
    IsHyperplane A (Subgroup.closure {c, d}) := by
  have hAcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hA.1.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hc3 : orderOf c = 3 := orderOf_eq_prime (hA.1.2 c hcA) hc1
  have hd1 : d ≠ 1 := by
    rintro rfl
    exact hd (Subgroup.one_mem _)
  have hd3 : orderOf d = 3 := orderOf_eq_prime (hA.1.2 d hdA) hd1
  have hcd : Commute c d := hAcomm c hcA d hdA
  have hcard : Nat.card ↥(Subgroup.zpowers c ⊔ Subgroup.zpowers d) = 9 :=
    card_sup_zpowers_of_not_mem hcd hc3 hd3 hd
  unfold IsHyperplane
  rw [n172_closure_pair_eq_sup]
  refine ⟨sup_le (Subgroup.zpowers_le.mpr hcA) (Subgroup.zpowers_le.mpr hdA), ?_⟩
  rw [hcard, hA.2]

theorem mem_zpowers_of_mem_closure_pair {L : Subgroup G} {c d b : G} (hc3 : orderOf c = 3)
    (hcL : c ∉ L) (hdL : d ∈ L) (hcd : Commute c d) (hb : b ∈ Subgroup.closure {c, d})
    (hbL : b ∈ L) : b ∈ Subgroup.zpowers d := by
  rw [n172_closure_pair_eq_sup] at hb
  obtain ⟨x, hx, y, hy, hxy⟩ := n172_mem_sup_pair hcd hb
  have hyL : y ∈ L := (Subgroup.zpowers_le.mpr hdL) hy
  have hxL : x ∈ L := by
    have hxeq : x = b * y⁻¹ := by rw [← hxy, mul_inv_cancel_right]
    rw [hxeq]
    exact mul_mem hbL (inv_mem hyL)
  have hx1 : x = 1 := n172_eq_one_of_mem_of_not_mem hc3 hcL hxL hx
  rw [← hxy, hx1, one_mul]
  exact hy

theorem zpowers_eq_of_mem_zpowers {b d : G} (hd3 : orderOf d = 3) (hb : b ∈ Subgroup.zpowers d)
    (hb1 : b ≠ 1) : Subgroup.zpowers b = Subgroup.zpowers d :=
  n172_zpowers_eq_of_mem_zpowers hd3 hb hb1

end CFSG.RankThree.PartTwo.Sec17
