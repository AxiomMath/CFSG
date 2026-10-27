module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.BrauerSuzukiWallCardTwoNormalizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.BrauerSuzukiWallCardTwoInvolutionCentralizer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Basic
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Strong embedding in the order-two branch

When `|K| = 2`, the normalizer of `H` is isomorphic to `A₄`.  Its normal
copy of the Klein four group `H` is therefore the unique Sylow `2`-subgroup.
Every normalizer involution lies in `H`, and equality of the centralizers of
two such involutions recovers any conjugator between them.
-/

open scoped Pointwise
open BenderSuzuki.PFchapter1section1

namespace CFSG.GorensteinWalter

universe u

/-- If the normalizer of `H` is proper in the `|K| = 2` branch of the
Brauer--Suzuki--Wall hypotheses, then it is strongly embedded. -/
public theorem
    BrauerSuzukiWallHypotheses.normalizer_H_isStronglyEmbedded_of_card_K_eq_two
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallHypotheses G)
    (hk : Nat.card h.K = 2)
    (hNne : Subgroup.normalizer (h.H : Set G) ≠ ⊤) :
    BenderSuzuki.IsStronglyEmbedded
      (Subgroup.normalizer (h.H : Set G)) := by
  classical
  let N : Subgroup G := Subgroup.normalizer (h.H : Set G)
  have hHleN : h.H ≤ N := Subgroup.le_normalizer
  let HN : Subgroup N := h.H.subgroupOf N
  have hHNcard : Nat.card HN = 4 := by
    calc
      Nat.card HN = Nat.card h.H :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHleN).toEquiv
      _ = 4 := (h.isKleinFour_H_of_card_K_eq_two hk).card_four
  have hNcard : Nat.card N = 12 := by
    obtain ⟨e⟩ :=
      h.normalizer_mulEquiv_alternatingGroup_four_of_card_K_eq_two hk
    calc
      Nat.card N = Nat.card (alternatingGroup (Fin 4)) :=
        Nat.card_congr e.toEquiv
      _ = 12 := alternatingGroup.card_of_card_eq_four (by simp)
  have hHNindex : HN.index = 3 := by
    have hmul := HN.card_mul_index
    rw [hHNcard, hNcard] at hmul
    omega
  have hHNp : IsPGroup 2 HN := by
    apply IsPGroup.of_card (n := 2)
    simpa using hHNcard
  let P : Sylow 2 N := hHNp.toSylow (by rw [hHNindex]; norm_num)
  have hHNnormal : HN.Normal := by
    apply (Subgroup.normal_subgroupOf_iff hHleN).2
    intro x n hxH hnN
    exact (Subgroup.mem_normalizer_iff.mp hnN x).mp hxH
  have hPnormal : (P : Subgroup N).Normal := by
    simpa [P, IsPGroup.toSylow_coe] using hHNnormal
  let : Unique (Sylow 2 N) := Sylow.unique_of_normal P hPnormal
  have hInvMemH : ∀ {x : G}, x ∈ N → IsInvolution x → x ∈ h.H := by
    intro x hxN hxI
    let xN : N := ⟨x, hxN⟩
    have hxNI : IsInvolution xN :=
      BenderSuzuki.IsInvolution.subtype hxI hxN
    have hxOrder : orderOf xN = 2 :=
      orderOf_eq_prime hxNI.2 hxNI.1
    let Z : Subgroup N := Subgroup.zpowers xN
    have hZp : IsPGroup 2 Z := by
      apply IsPGroup.of_card (n := 1)
      simp [Z, Nat.card_zpowers, hxOrder]
    obtain ⟨Q, hZQ⟩ := hZp.exists_le_sylow
    have hQP : Q = P := Subsingleton.elim Q P
    have hxP : xN ∈ (P : Subgroup N) := by
      rw [← hQP]
      exact hZQ (Subgroup.mem_zpowers xN)
    have hxHN : xN ∈ HN := by
      simpa [P, IsPGroup.toSylow_coe] using hxP
    exact hxHN
  have hKleH : h.K ≤ h.H := by
    rw [h.H_eq_join]
    exact le_sup_left
  have htH : h.t ∈ h.H := hKleH h.t_mem_K
  refine ⟨hNne, ⟨h.t, hHleN htH, h.t_involution⟩, ?_⟩
  intro g hgN x hxN hxright hxI
  have hxIroot : IsInvolution x := ⟨hxI.1, hxI.2⟩
  have hxH : x ∈ h.H := hInvMemH hxN hxIroot
  rw [rightConjugate, Subgroup.conjBy, Subgroup.mem_map] at hxright
  rcases hxright with ⟨y, hyN, hxy⟩
  have hgy : g * x * g⁻¹ = y := by
    rw [← hxy]
    change g * (g⁻¹ * y * (g⁻¹)⁻¹) * g⁻¹ = y
    group
  have hyI : IsInvolution y := by
    have hyIconj : BenderSuzuki.PFAppendixIII.IsInvolution y := by
      have hyIconj' :=
        BenderSuzuki.PFAppendixIII.isInvolution_rightConjugateElem
          (g := g⁻¹) hxI
      simpa [BenderSuzuki.PFAppendixIII.rightConjugateElem, hgy] using
        hyIconj'
    exact ⟨hyIconj.1, hyIconj.2⟩
  have hyH : y ∈ h.H := hInvMemH hyN hyI
  apply hgN
  rw [Subgroup.mem_normalizer_iff]
  intro z
  constructor
  · intro hzH
    have hzC : z ∈ Subgroup.centralizer ({x} : Set G) := by
      rw [h.centralizer_eq_H_of_mem_H_isInvolution_of_card_K_eq_two
        hk hxH hxIroot]
      exact hzH
    rw [Subgroup.mem_centralizer_singleton_iff] at hzC
    rw [← h.centralizer_eq_H_of_mem_H_isInvolution_of_card_K_eq_two
      hk hyH hyI, Subgroup.mem_centralizer_singleton_iff]
    rw [← hgy]
    calc
      (g * z * g⁻¹) * (g * x * g⁻¹) =
          g * (z * x) * g⁻¹ := by group
      _ = g * (x * z) * g⁻¹ := by rw [hzC]
      _ = (g * x * g⁻¹) * (g * z * g⁻¹) := by group
  · intro hgzH
    have hgzC : g * z * g⁻¹ ∈
        Subgroup.centralizer ({y} : Set G) := by
      rw [h.centralizer_eq_H_of_mem_H_isInvolution_of_card_K_eq_two
        hk hyH hyI]
      exact hgzH
    rw [Subgroup.mem_centralizer_singleton_iff] at hgzC
    have hzcomm : z * x = x * z := by
      have hc := congrArg (fun q : G ↦ g⁻¹ * q * g) hgzC
      rw [← hgy] at hc
      simpa [mul_assoc] using hc
    rw [← h.centralizer_eq_H_of_mem_H_isInvolution_of_card_K_eq_two
      hk hxH hxIroot]
    exact Subgroup.mem_centralizer_singleton_iff.mpr hzcomm

end CFSG.GorensteinWalter
