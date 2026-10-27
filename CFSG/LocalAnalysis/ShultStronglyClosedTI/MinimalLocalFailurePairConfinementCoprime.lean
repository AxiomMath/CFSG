module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailurePairConfinementInversion
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section7Coprime

public noncomputable section

namespace CFSG.ShultStronglyClosedTI

open CFSG.BenderSuzuki CFSG.BenderSuzuki.PFAppendixIII
open CFSG.BenderSuzuki.PFchapter1section1
open scoped Pointwise commutatorElement

universe u

variable {G : Type u} [Group G]

theorem pairConfinement_closure_commutator
    (X : Subgroup G) (hXodd : Odd (Nat.card X)) (z : G) (hz : orderOf z = 2) :
    ⁅minimalLocalFailurePairConfinementClosure X z, Subgroup.zpowers z⁆ =
      minimalLocalFailurePairConfinementClosure X z := by
  let W := minimalLocalFailurePairConfinementClosure X z
  have hzW : z ∈ Subgroup.normalizer (W : Set G) :=
    Subgroup.normalizer_le_normalizer_closure _
      (invertedHull_involution_normalizes_set X z hz)
  apply le_antisymm
  · exact Subgroup.le_normalizer_iff_commutator_le_left.mp
      (Subgroup.zpowers_le.mpr hzW)
  · apply (Subgroup.closure_le _).mpr
    intro x hx
    have hzinv : z⁻¹ = z := inv_eq_self_of_orderOf_eq_two hz
    have hxinv : z * x⁻¹ * z = x := by
      simpa only [rightConjugateElem, mul_inv_rev, inv_inv, hzinv, mul_assoc]
        using congrArg Inv.inv hx.2
    have hcomm : ⁅x, z⁆ = x ^ 2 := by
      calc
        ⁅x, z⁆ = x * (z * x⁻¹ * z) := by
          simp only [commutatorElement_def, hzinv, mul_assoc]
        _ = x * x := by rw [hxinv]
        _ = x ^ 2 := (pow_two x).symm
    have hsq : x ^ 2 ∈ ⁅W, Subgroup.zpowers z⁆ := by
      rw [← hcomm]
      exact Subgroup.commutator_mem_commutator
        (pairConfinement_closure_contains X z hx) (Subgroup.mem_zpowers z)
    have hxodd : Odd (orderOf x) := hXodd.of_dvd_nat (X.orderOf_dvd_natCard hx.1)
    have hroot : x ∈ Subgroup.zpowers (x ^ 2) :=
      mem_zpowers_pow_iff.mpr hxodd.coprime_two_left
    exact (Subgroup.zpowers_le.mpr hsq) hroot

theorem pairConfinement_actor_card_coprime
    {X W Y : Subgroup G} {z : G} (hz : orderOf z = 2)
    (hWX : W ≤ X) (hzW : z ∈ Subgroup.normalizer (W : Set G))
    (hcop : Nat.Coprime (2 * Nat.card X) (Nat.card Y)) :
    Nat.Coprime (Nat.card ↥(W ⊔ Subgroup.zpowers z)) (Nat.card Y) := by
  let A := W ⊔ Subgroup.zpowers z
  let WA := W.subgroupOf A
  let ZA := (Subgroup.zpowers z).subgroupOf A
  have hWnormal : WA.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer
      (le_sup_left : W ≤ A)).mpr
      (sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.mpr hzW))
  let : WA.Normal := hWnormal
  have htop : ZA ⊔ WA = ⊤ := by
    rw [← Subgroup.subgroupOf_sup (A := Subgroup.zpowers z) (A' := W) (B := A)
      le_sup_right le_sup_left]
    simp [A, sup_comm]
  have hidx : WA.index = WA.relIndex ZA := by
    rw [← Subgroup.relIndex_top_right, ← htop, Subgroup.relIndex_sup_right]
  have hidxdvd : WA.index ∣ 2 := by
    rw [hidx]
    have hdiv := Subgroup.relIndex_dvd_card WA ZA
    have hcard : Nat.card ZA = 2 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        (le_sup_right : Subgroup.zpowers z ≤ A)).toEquiv, Nat.card_zpowers, hz]
    rwa [hcard] at hdiv
  have hWcop : Nat.Coprime (Nat.card WA) (Nat.card Y) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_left : W ≤ A)).toEquiv]
    exact Nat.Coprime.of_dvd_left (Subgroup.card_dvd_of_le hWX) hcop.coprime_mul_left
  have hidxcop : Nat.Coprime WA.index (Nat.card Y) :=
    Nat.Coprime.of_dvd_left hidxdvd hcop.coprime_mul_right
  rw [← Subgroup.card_mul_index WA]
  exact hWcop.mul_left hidxcop

variable [Finite G]

theorem pairConfinement_odd_inverted_centralizer_escape
    (H X Y : Subgroup G) (z : G) (hz : orderOf z = 2)
    (hcentral : Subgroup.centralizer ({z} : Set G) ≤ H)
    (hXH : X ≤ H) (hXodd : Odd (Nat.card X))
    (_hzX : z ∈ Subgroup.normalizer (X : Set G))
    (hXY : X ≤ Subgroup.normalizer (Y : Set G))
    (hzY : z ∈ Subgroup.normalizer (Y : Set G))
    (hcop : Nat.Coprime (2 * Nat.card X) (Nat.card Y))
    (hescape : ¬ Y ≤ H) :
    ¬ Y ⊓ Subgroup.centralizer (minimalLocalFailureInvertedSet X z) ≤ H := by
  let W := minimalLocalFailurePairConfinementClosure X z
  have hWX : W ≤ X := pairConfinement_closure_le X z
  have hzW : z ∈ Subgroup.normalizer (W : Set G) :=
    Subgroup.normalizer_le_normalizer_closure _
      (invertedHull_involution_normalizes_set X z hz)
  have hYodd : Odd (Nat.card Y) := Nat.coprime_two_left.mp hcop.coprime_mul_right
  have hzinvolution : IsInvolution z :=
    ⟨(orderOf_eq_prime_iff.mp hz).2, (orderOf_eq_prime_iff.mp hz).1⟩
  have hgen : Lemma75II146Conclusion Y W z :=
    lemma75_II146_specialized hzinvolution hzW (hWX.trans hXY) hzY
      (pairConfinement_closure_commutator X hXodd z hz) hYodd
      (pairConfinement_actor_card_coprime hz hWX hzW hcop)
  intro hconfined
  apply hescape
  apply lemma75_le_of_II146Conclusion hgen
  · simpa only [subgroupCentralizerIn, W, minimalLocalFailurePairConfinementClosure,
      Subgroup.centralizer_closure] using hconfined
  · exact inf_le_right.trans hcentral
  · exact hWX.trans hXH

end CFSG.ShultStronglyClosedTI
