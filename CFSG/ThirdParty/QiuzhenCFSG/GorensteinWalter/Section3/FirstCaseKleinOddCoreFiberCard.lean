module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinOddCoreOrderThree
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinRestrictionFive
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

noncomputable section

open scoped Pointwise

namespace CFSG.GorensteinWalter

universe u

/-!
The quotient argument in restriction (6) gives not only an order-three
element but an entire fibre of cardinality three.  The upper bound is the
injectivity of the quotient map; the lower bound is supplied by the three
powers of the extracted order-three element.
-/

public theorem firstCase_klein_oddCore_inverted_card_three
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
    Nat.card {x : G // x ∈ invertedElements
      (oddCoreOf (c.Hhat ⊓ conjugateSubgroup c.Hhat y : Subgroup G)) y} = 3 := by
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
  have hNodd : Nat.Coprime 2 (Nat.card N) :=
    firstCase_klein_intersection_odd_of_index_six
      hmin c hfirst hklein hy hyH hindex
  have hNsubodd : Nat.Coprime 2 (Nat.card (N.subgroupOf D)) := by
    have hcard : Nat.card (N.subgroupOf D) = Nat.card N :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNleD).toEquiv
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
    have hmemN : x.1 * z.1⁻¹ ∈ N := hmemNsub
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
    obtain ⟨i0, hi0⟩ := (Nat.card_eq_one_iff_exists).mp h5
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
  have hupper : Nat.card {x : G // x ∈ invertedElements O y} ≤ 3 := by
    have hle := Nat.card_le_card_of_injective f hf_inj
    simpa [hqcard] using hle
  obtain ⟨x, hxO, hxne, hxord, hxinv⟩ :=
    firstCase_klein_oddCore_inverted_order_three
      hmin c hfirst hklein hy hyH hindex hI
  let R : Subgroup G := Subgroup.zpowers x
  have hRle : R ≤ O := by
    apply (Subgroup.zpowers_le).2
    exact hxO
  have hRcard : Nat.card R = 3 := by
    rw [Nat.card_zpowers, hxord]
  have hRin : ∀ z : G, z ∈ R → z ∈ invertedElements O y := by
    intro z hz
    rcases Subgroup.mem_zpowers_iff.mp hz with ⟨n, hn⟩
    rw [← hn]
    refine ⟨O.zpow_mem hxO n, ?_⟩
    calc
      y * x ^ n * y⁻¹ = (y * x * y⁻¹) ^ n := by
        exact conj_zpow.symm
      _ = (x⁻¹) ^ n := by rw [hxinv.2]
      _ = (x ^ n)⁻¹ := by simp
  have hlower : 3 ≤ Nat.card {z : G // z ∈ invertedElements O y} := by
    let e : R → {z : G // z ∈ invertedElements O y} := fun z =>
      ⟨z, hRin z z.2⟩
    have he : Function.Injective e := by
      intro a b hab
      apply Subtype.ext
      exact congrArg (fun w : {z : G // z ∈ invertedElements O y} => (w : G)) hab
    simpa [hRcard] using Nat.card_le_card_of_injective e he
  exact Nat.le_antisymm hupper hlower

end CFSG.GorensteinWalter
