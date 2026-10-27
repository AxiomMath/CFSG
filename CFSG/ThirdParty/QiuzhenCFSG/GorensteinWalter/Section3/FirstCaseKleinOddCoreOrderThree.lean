module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinIntersectionOddCoreRelIndex
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinRestrictionFive
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section1
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

noncomputable section

open scoped Pointwise

namespace CFSG.GorensteinWalter

universe u

/-!
An odd-core fibre in restriction (6) contains an element of order three.
The quotient map by `D ∩ VU` is injective on the inverted fibre by
restriction (5); the quotient has order three by the relative-index lemma.
-/

public theorem firstCase_klein_oddCore_inverted_order_three
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (hfirst : FirstCase c)
    (hklein : IsKleinFour (pCore 2 c.Hhat))
    {y : G} (hy : IsInvolution y) (hyH : y ∉ c.Hhat)
    (hindex :
      let D := c.Hhat ⊓ conjugateSubgroup c.Hhat y
      let N := D ⊓ (twoCoreOf c.Hhat ⊔ c.U)
      (N.subgroupOf D).index = 6)
    (hI :
      Nat.card {x : G // x ∈ invertedElements
        (oddCoreOf (c.Hhat ⊓ conjugateSubgroup c.Hhat y : Subgroup G)) y} ≠ 1) :
    ∃ x : G, x ∈ oddCoreOf (c.Hhat ⊓ conjugateSubgroup c.Hhat y : Subgroup G) ∧
      x ≠ 1 ∧ orderOf x = 3 ∧
      x ∈ invertedElements
        (oddCoreOf (c.Hhat ⊓ conjugateSubgroup c.Hhat y : Subgroup G)) y := by
  classical
  let D : Subgroup G := c.Hhat ⊓ conjugateSubgroup c.Hhat y
  let B : Subgroup G := twoCoreOf c.Hhat ⊔ c.U
  let N : Subgroup G := D ⊓ B
  let O : Subgroup G := oddCoreOf D
  have hNleD : N ≤ D := inf_le_left
  have hBnorm : IsNormalIn B c.Hhat := firstCase_klein_VU_normal_in_Hhat hmin c
  have hDle : D ≤ c.Hhat := inf_le_left
  have hNnormal : (N.subgroupOf D).Normal := by
    apply (Subgroup.normal_subgroupOf_iff hNleD).2
    intro n d hn hd
    refine ⟨?_, ?_⟩
    · exact D.mul_mem (D.mul_mem hd (hNleD hn)) (D.inv_mem hd)
    · exact hBnorm.2 d (hDle hd) n ((show N ≤ B from inf_le_right) hn)
  let : (N.subgroupOf D).Normal := hNnormal
  have hindex' : (N.subgroupOf D).index = 6 := by simpa [D, N] using hindex
  have hNodd : Nat.Coprime 2 (Nat.card N) := by
    exact firstCase_klein_intersection_odd_of_index_six
      hmin c hfirst hklein hy hyH hindex
  have hNsubodd : Nat.Coprime 2 (Nat.card (N.subgroupOf D)) := by
    have hcard : Nat.card (N.subgroupOf D) = Nat.card N := by
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNleD).toEquiv
    rw [hcard]
    exact hNodd
  have hNsub_le_core : N.subgroupOf D ≤ pPrimeCore 2 (↥D) :=
    le_sSup ⟨hNnormal, hNsubodd⟩
  have hmapN : (N.subgroupOf D).map D.subtype = N :=
    Subgroup.map_subgroupOf_eq_of_le hNleD
  have hNleO : N ≤ O := by
    dsimp [O, oddCoreOf]
    rw [← hmapN]
    exact Subgroup.map_mono hNsub_le_core
  have hOleD : O ≤ D := by
    dsimp [O, oddCoreOf]
    exact Subgroup.map_subtype_le (pPrimeCore 2 (↥D))
  have hOindex : (N.subgroupOf O).index = 3 := by
    change N.relIndex O = 3
    simpa [D, N, O] using
      firstCase_klein_intersection_oddCore_relIndex_three
        hmin c hfirst hklein hy hyH hindex
  have hNO_normal : (N.subgroupOf O).Normal := by
    apply Subgroup.normal_subgroupOf_of_le_normalizer
    rw [Subgroup.le_normalizer_iff]
    intro o ho n hn
    have hconjD : o * n * o⁻¹ ∈ D :=
      D.mul_mem (D.mul_mem (hOleD ho) (hNleD hn)) (D.inv_mem (hOleD ho))
    have hconjB : o * n * o⁻¹ ∈ B :=
      hBnorm.2 o (hDle (hOleD ho)) n ((show N ≤ B from inf_le_right) hn)
    exact ⟨hconjD, hconjB⟩
  let : (N.subgroupOf O).Normal := hNO_normal
  let q : O →* (O ⧸ N.subgroupOf O) := QuotientGroup.mk' (N.subgroupOf O)
  have hqcard : Nat.card (O ⧸ N.subgroupOf O) = 3 := by
    rw [← (N.subgroupOf O).index_eq_card, hOindex]
  let f : {x : G // x ∈ invertedElements O y} →
      (O ⧸ N.subgroupOf O) := fun x => q ⟨x.1, x.2.1⟩
  have hf_inj : Function.Injective f := by
    intro x z hq
    apply Subtype.ext
    by_contra hne
    have hxO : x.1 ∈ O := x.2.1
    have hzO : z.1 ∈ O := z.2.1
    let xO : O := ⟨x.1, hxO⟩
    let zO : O := ⟨z.1, hzO⟩
    have hqone : q (xO * zO⁻¹) = 1 := by
      change q xO * (q zO)⁻¹ = 1
      rw [show q xO = f x by rfl, show q zO = f z by rfl, hq]
      simp
    have hmemNsub : xO * zO⁻¹ ∈ N.subgroupOf O :=
      (QuotientGroup.eq_one_iff (xO * zO⁻¹)).mp hqone
    have hmemN : x.1 * z.1⁻¹ ∈ N := by
      exact hmemNsub
    have hmemB : x.1 * z.1⁻¹ ∈ B := (show N ≤ B from inf_le_right) hmemN
    have hxTop : x.1 ∈ invertedElements (⊤ : Subgroup G) y :=
      ⟨by simp, x.2.2⟩
    have hzTop : z.1 ∈ invertedElements (⊤ : Subgroup G) y :=
      ⟨by simp, z.2.2⟩
    have hInvProd := fact_1_4_inverted_mul_inv hy hxTop hzTop
    have hzyI : IsInvolution (z.1 * y) := by
      rw [fact_1_4_involution_mul hy]
      refine ⟨?_, ?_⟩
      · intro h
        apply hyH
        rw [← h]
        exact hDle (hOleD z.2.1)
      · have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right
          (by simpa [pow_two] using hy.2)
        simpa [invertedElements, hyinv] using z.2.2
    have hzyH : z.1 * y ∉ c.Hhat := by
      intro hmem
      apply hyH
      have hyEq : y = z.1⁻¹ * (z.1 * y) := by group
      rw [hyEq]
      exact c.Hhat.mul_mem (c.Hhat.inv_mem (hDle (hOleD z.2.1))) hmem
    have h5 := firstCase_klein_restrictionFive hmin c hfirst hklein
      (z.1 * y) hzyI hzyH
    have hone : (1 : G) ∈ invertedElements B (z.1 * y) :=
      ⟨B.one_mem, by simp⟩
    have hcardone : Nat.card {w : G // w ∈ invertedElements B (z.1 * y)} = 1 :=
      h5
    obtain ⟨i0, hi0⟩ := (Nat.card_eq_one_iff_exists).mp hcardone
    have hprodsub :
        (⟨x.1 * z.1⁻¹, ⟨hmemB, hInvProd.2⟩⟩ :
          {w : G // w ∈ invertedElements B (z.1 * y)}) =
        (⟨1, hone⟩ : {w : G // w ∈ invertedElements B (z.1 * y)}) := by
      exact (hi0 _).trans (hi0 _).symm
    have hprod1 : x.1 * z.1⁻¹ = 1 := congrArg Subtype.val hprodsub
    exact hne (by
      calc
        x.1 = (x.1 * z.1⁻¹) * z.1 := by group
        _ = z.1 := by rw [hprod1]; simp)
  have honeO : (1 : G) ∈ invertedElements O y := ⟨O.one_mem, by simp⟩
  let : Nonempty {x : G // x ∈ invertedElements O y} :=
    ⟨⟨1, honeO⟩⟩
  obtain ⟨i, hi⟩ : ∃ i : {x : G // x ∈ invertedElements O y},
      i ≠ (⟨1, honeO⟩ : {x : G // x ∈ invertedElements O y}) := by
    by_contra hnone
    push_neg at hnone
    apply hI
    exact (Nat.card_eq_one_iff_exists).2 ⟨⟨1, honeO⟩, fun z => hnone z⟩
  let x : G := i.1
  have hxO : x ∈ O := i.2.1
  have hxInv : x ∈ invertedElements O y := i.2
  have hxne : x ≠ 1 := by
    intro hx1
    apply hi
    apply Subtype.ext
    simpa [x, hx1]
  have hqxne : q ⟨x, hxO⟩ ≠ 1 := by
    intro hq1
    have hfq : f i = f ⟨1, honeO⟩ := by simpa [f, hq1]
    have hi1 := hf_inj hfq
    exact hi (by simpa [x] using hi1)
  have horder_dvd : orderOf (q ⟨x, hxO⟩) ∣
      Nat.card (O ⧸ N.subgroupOf O) := orderOf_dvd_natCard _
  rw [hqcard] at horder_dvd
  have horder_ne1 : orderOf (q ⟨x, hxO⟩) ≠ 1 := by
    intro h
    exact hqxne (orderOf_eq_one_iff.mp h)
  have horder3 : orderOf (q ⟨x, hxO⟩) = 3 := by
    exact ((Nat.dvd_prime Nat.prime_three).mp horder_dvd).resolve_left horder_ne1
  have hqpow : q ⟨x, hxO⟩ ^ 3 = 1 := by
    rw [← horder3]
    exact pow_orderOf_eq_one _
  have hpow_sub : (⟨x, hxO⟩ : O) ^ 3 =
      (⟨x ^ 3, O.pow_mem hxO 3⟩ : O) := by
    apply Subtype.ext
    simp
  have hqpow' : q ((⟨x, hxO⟩ : O) ^ 3) = 1 := by
    rw [map_pow]
    exact hqpow
  have hqx3 : q (⟨x ^ 3, O.pow_mem hxO 3⟩ : O) = 1 := by
    rw [← hpow_sub]
    exact hqpow'
  have hx3Nsub : (⟨x ^ 3, O.pow_mem hxO 3⟩ : O) ∈ N.subgroupOf O :=
    (QuotientGroup.eq_one_iff _).mp hqx3
  have hx3N : x ^ 3 ∈ N := hx3Nsub
  have hx3I : x ^ 3 ∈ invertedElements O y := by
    refine ⟨O.pow_mem hxO 3, ?_⟩
    calc
      y * x ^ 3 * y⁻¹ = (y * x * y⁻¹) ^ 3 :=
        (conj_pow (a := y) (b := x) (i := 3)).symm
      _ = (x⁻¹) ^ 3 := by rw [hxInv.2]
      _ = (x ^ 3)⁻¹ := by group
  have hqx3one : q ⟨x ^ 3, hx3I.1⟩ = 1 := by
    exact (QuotientGroup.eq_one_iff _).2 hx3Nsub
  have hf3 : f ⟨x ^ 3, hx3I⟩ = f ⟨1, honeO⟩ := by
    calc
      f ⟨x ^ 3, hx3I⟩ = q ⟨x ^ 3, hx3I.1⟩ := rfl
      _ = 1 := hqx3one
      _ = q ⟨1, O.one_mem⟩ := (map_one q).symm
      _ = f ⟨1, honeO⟩ := rfl
  have hi3 := hf_inj hf3
  have hx3one : x ^ 3 = 1 := by
    have := congrArg Subtype.val hi3
    simpa [x] using this
  refine ⟨x, hxO, hxne, ?_, hxInv⟩
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact orderOf_eq_prime hx3one hxne

end CFSG.GorensteinWalter
