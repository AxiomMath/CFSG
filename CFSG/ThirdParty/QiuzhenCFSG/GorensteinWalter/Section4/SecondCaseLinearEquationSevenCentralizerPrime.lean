module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearEquationSevenPrime
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Section 4, equation (7): prime support of `C_U(F(U) ∩ M)`

The source's full prime-support assertion in equation (7) contains

`pi(C_U(K0 F)) = pi(F(U)) = pi(K0)`,

where `K0 F = F(U) ∩ M`.  The earlier equation-(7) module proves the
`F(U)`-to-`K0` inclusion.  This module proves the remaining centralizer
inclusion needed in the post-equation-(8) disjointness argument.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- Coprimality of an `r`-power with an integer not divisible by the prime
`r`. -/
private theorem coprime_card_of_not_dvd_pow_eq7centralizer
    {r n m : ℕ} (hr : r.Prime) (h : ¬ r ∣ m) :
    Nat.Coprime (r ^ n) m := by
  apply Nat.coprime_of_dvd
  intro p hp hpdvd hpdvdm
  have hpr : p = r := by
    have hpdvdr : p ∣ r := hp.dvd_of_dvd_pow hpdvd
    exact (Nat.prime_dvd_prime_iff_eq hp hr).mp hpdvdr
  rw [hpr] at hpdvdm
  exact h hpdvdm

/-- **Equation (7), centralizer prime support.** Every prime divisor of
`|C_U(F(U) ∩ M)|` divides `|K0|`, where
`K0 ⋁ F = F(U) ∩ M` is the equation-(3) decomposition.

Indeed, an `r`-Sylow subgroup of this centralizer for
`r ∤ |F(U)|` centralizes the self-centralizing subnormal subgroup
`F(U) ∩ M` of `F(U)`.  Fact 1.1(iv) makes it centralize all of `F(U)`,
and Fact 1.2 then puts it inside `F(U)`, a contradiction. -/
public theorem secondCase_equationSevenPrime_primeFactors_centralizerIn_FU_inter_M_subset_K0
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (Kinv K0 F : Subgroup G) (s : d.E)
    (hKinv_carrier : (Kinv : Set G) =
      invertedElements (c.U ⊓ w.M) (s : G))
    (hKinv_cyclic : IsCyclic Kinv)
    (hK0_def : K0 = fittingSubgroupOf c.U ⊓ Kinv)
    (hF_eq : F = centralizerIn (fittingSubgroupOf c.U ⊓ w.M) (s : G))
    (hjoin : K0 ⊔ F = fittingSubgroupOf c.U ⊓ w.M)
    (hFcentE : F ≤ Subgroup.centralizer (d.E : Set G))
    (hLayer : ∀ X : Subgroup G, X ≠ ⊥ → X ≤ F →
      componentLayerOf (Subgroup.normalizer (X : Set G)) = d.E)
    {r : ℕ} (hr : r.Prime)
    (hrdvd : r ∣ Nat.card ↥
      (c.U ⊓ Subgroup.centralizer
        ((fittingSubgroupOf c.U ⊓ w.M : Subgroup G) : Set G))) :
    r ∣ Nat.card K0 := by
  classical
  let Y : Subgroup G := fittingSubgroupOf c.U ⊓ w.M
  let C : Subgroup G := c.U ⊓ Subgroup.centralizer (Y : Set G)
  have hK0leKinv : K0 ≤ Kinv := by
    rw [hK0_def]
    exact inf_le_right
  obtain ⟨_hFnormalM, _hFnormalY, _hFne, hNFeq, _hTI, _hFcyc,
      _hFcardle, _hK0ne, _hO2⟩ :=
    secondCase_fitting_equation5_7_of_component_centralization
      hmin c w d Kinv K0 F s hKinv_cyclic hK0leKinv hF_eq hjoin hFcentE hLayer
  by_contra hrnK0
  have hrnFU : ¬ r ∣ Nat.card c.FU := by
    intro hrFU
    exact hrnK0
      (secondCase_equationSevenPrime_primeFactors_FU_subset_K0
        hmin c w d Kinv K0 F s hKinv_carrier hKinv_cyclic hK0_def hF_eq
          hjoin hFcentE hLayer hr (by simpa [CentralizerSetup.FU] using hrFU))
  let : Fact r.Prime := ⟨hr⟩
  let R : Sylow r (↥C) := Classical.choice Sylow.nonempty
  let RG : Subgroup G := (R : Subgroup (↥C)).map C.subtype
  have hRGleC : RG ≤ C := Subgroup.map_subtype_le (R : Subgroup (↥C))
  have hRGleU : RG ≤ c.U := hRGleC.trans inf_le_left
  have hRGcard : Nat.card RG = Nat.card (R : Subgroup (↥C)) :=
    Subgroup.card_map_of_injective (K := (R : Subgroup (↥C)))
      (f := C.subtype) C.subtype_injective
  have hRne : (R : Subgroup (↥C)) ≠ ⊥ :=
    R.ne_bot_of_dvd_card (by simpa [C, Y] using hrdvd)
  have hRGne : RG ≠ ⊥ := by
    intro hbot
    exact hRne ((Subgroup.map_eq_bot_iff_of_injective
      (H := (R : Subgroup (↥C))) (f := C.subtype)
      (hf := C.subtype_injective)).mp hbot)
  have hRGcentY : RG ≤ Subgroup.centralizer (Y : Set G) := by
    intro x hx
    exact (hRGleC hx).2
  have hYleFU : Y ≤ c.FU := inf_le_left
  have hYsub : (Y.subgroupOf c.FU).IsSubnormal :=
    isSubnormal_of_nilpotent (fittingSubgroupOf_isNilpotent c.U) Y hYleFU
  have hFleY : F ≤ Y := by
    intro f hf
    change f ∈ fittingSubgroupOf c.U ⊓ w.M
    rw [← hjoin]
    exact (le_sup_right : F ≤ K0 ⊔ F) hf
  have hYself : c.FU ⊓ Subgroup.centralizer (Y : Set G) ≤ Y := by
    intro x hx
    have hxCentF : x ∈ Subgroup.centralizer (F : Set G) :=
      (Subgroup.centralizer_le (SetLike.coe_mono hFleY)) hx.2
    have hxN : x ∈ Subgroup.normalizer (F : Set G) :=
      Subgroup.centralizer_le_normalizer (F : Set G) hxCentF
    have hxM : x ∈ w.M := hNFeq ▸ hxN
    exact ⟨hx.1, hxM⟩
  have hcop : Nat.Coprime (Nat.card RG) (Nat.card c.FU) := by
    rcases R.isPGroup'.exists_card_eq with ⟨n, hn⟩
    have hcop' : Nat.Coprime (r ^ n) (Nat.card c.FU) :=
      coprime_card_of_not_dvd_pow_eq7centralizer (n := n) hr hrnFU
    rwa [← hn, ← hRGcard] at hcop'
  have hRGnormFU : RG ≤ Subgroup.normalizer (c.FU : Set G) :=
    hRGleU.trans
      (le_normalizer_of_isNormalIn (fittingSubgroupOf_isNormalIn c.U))
  have hRGcentFU : RG ≤ Subgroup.centralizer (c.FU : Set G) := by
    let : Group.IsNilpotent (↥c.FU) := fittingSubgroupOf_isNilpotent c.U
    exact centralizes_of_subnormal_selfCentralizing_coprime
      RG c.FU Y hRGnormFU hYleFU hYsub hRGcentY hYself hcop
        (inferInstance : Group.IsSolvable c.FU)
  have hUsolv : Group.IsSolvable c.U := odd_order_theorem c.U (by
    change Odd (Nat.card (oddCoreOf c.H))
    exact odd_card_oddCoreOf c.H)
  have hFUself : c.U ⊓ Subgroup.centralizer (c.FU : Set G) ≤ c.FU :=
    fact_1_2_centralizer_fitting_le_fitting c.U hUsolv
  have hRGleFU : RG ≤ c.FU := by
    intro x hx
    exact hFUself ⟨hRGleU hx, hRGcentFU hx⟩
  have hrdvdFU : r ∣ Nat.card c.FU := by
    have hrdvdR : r ∣ Nat.card (R : Subgroup (↥C)) := by
      have hfact : (Nat.card (↥C)).factorization r ≠ 0 :=
        (hr.factorization_pos_of_dvd Nat.card_pos.ne'
          (by simpa [C, Y] using hrdvd)).ne'
      rw [R.card_eq_multiplicity]
      exact dvd_pow_self r hfact
    have hRGdvdFU : Nat.card RG ∣ Nat.card c.FU :=
      Subgroup.card_dvd_of_le hRGleFU
    exact hrdvdR.trans (by simpa [hRGcard] using hRGdvdFU)
  exact hrnFU hrdvdFU

end CFSG.GorensteinWalter
