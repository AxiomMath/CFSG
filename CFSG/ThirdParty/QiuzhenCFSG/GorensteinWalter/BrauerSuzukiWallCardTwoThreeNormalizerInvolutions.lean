module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.BrauerSuzukiWallCardTwoCentralizer
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Involutions normalizing the order-three intersection

For `T = N_G(H) ∩ N_G(H)^u`, right multiplication by the chosen outside
involution `u` identifies `T` with the involutions of `N_G(T)`.  Thus exactly
three involutions normalize `T`.
-/

open scoped Pointwise
open BenderSuzuki.PFchapter1section1
open BenderSuzuki.PFAppendixIII

namespace CFSG.GorensteinWalter

universe u

/-- In the `|K| = 2` branch, exactly three involutions normalize the
order-three intersection attached to an outside involution. -/
public theorem
    BrauerSuzukiWallHypotheses.involutions_normalizing_inf_rightConjugate_card_eq_three_of_card_K_eq_two
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallHypotheses G)
    (hk : Nat.card h.K = 2) {u : G}
    (huI : IsInvolution u)
    (huN : u ∉ Subgroup.normalizer (h.H : Set G)) :
    let N : Subgroup G := Subgroup.normalizer (h.H : Set G)
    let T : Subgroup G := N ⊓ rightConjugate N u
    Nat.card {v : G // IsInvolution v ∧
      v ∈ Subgroup.normalizer (T : Set G)} = 3 := by
  classical
  let N : Subgroup G := Subgroup.normalizer (h.H : Set G)
  let T : Subgroup G := N ⊓ rightConjugate N u
  let InvNorm := {v : G // IsInvolution v ∧
    v ∈ Subgroup.normalizer (T : Set G)}
  obtain ⟨hTcard, huNorm, huInv⟩ :=
    h.normalizer_inf_rightConjugate_card_eq_three_and_inverted_of_card_K_eq_two
      hk huI huN
  have hNne : N ≠ ⊤ := by
    intro htop
    apply huN
    change u ∈ N
    rw [htop]
    trivial
  have hstrong : BenderSuzuki.IsStronglyEmbedded N :=
    h.normalizer_H_isStronglyEmbedded_of_card_K_eq_two hk hNne
  have hTleN : T ≤ N := inf_le_left
  let TN : Subgroup N := T.subgroupOf N
  have hTNcard : Nat.card TN = 3 := by
    calc
      Nat.card TN = Nat.card T :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTleN).toEquiv
      _ = 3 := hTcard
  have hNiso : Nonempty (N ≃* alternatingGroup (Fin 4)) :=
    h.normalizer_mulEquiv_alternatingGroup_four_of_card_K_eq_two hk
  have hTNnorm : Subgroup.normalizer (TN : Set N) = TN :=
    normalizer_eq_self_of_card_eq_three_of_mulEquiv_alternatingGroup_four
      TN hTNcard hNiso
  have hCent : Subgroup.centralizer (T : Set G) = T :=
    h.centralizer_inf_rightConjugate_eq_of_card_K_eq_two hk huI huN
  have huu : u * u = 1 := by
    simpa [pow_two] using huI.2
  have huInvSelf : u⁻¹ = u := inv_eq_of_mul_eq_one_right huu
  have hxuI : ∀ x : T, IsInvolution ((x : G) * u) := by
    intro x
    constructor
    · intro hxu
      apply huN
      have huEq : u = (x : G)⁻¹ := eq_inv_of_mul_eq_one_right hxu
      rw [huEq]
      exact hTleN (T.inv_mem x.property)
    · rw [pow_two]
      calc
        ((x : G) * u) * ((x : G) * u) =
            (x : G) * (u * (x : G) * u⁻¹) := by
          rw [huInvSelf]
          group
        _ = (x : G) * (x : G)⁻¹ := by rw [huInv (x : G) x.property]
        _ = 1 := by simp
  have hxuNorm : ∀ x : T,
      (x : G) * u ∈ Subgroup.normalizer (T : Set G) := by
    intro x
    exact (Subgroup.normalizer (T : Set G)).mul_mem
      (Subgroup.le_normalizer x.property) huNorm
  let toFun : T → InvNorm := fun x ↦
    ⟨(x : G) * u, hxuI x, hxuNorm x⟩
  have htoFunInjective : Function.Injective toFun := by
    intro x y hxy
    apply Subtype.ext
    have hxy' := congrArg Subtype.val hxy
    change (x : G) * u = (y : G) * u at hxy'
    exact mul_right_cancel hxy'
  have htoFunSurjective : Function.Surjective toFun := by
    intro v
    have hvI : IsInvolution (v : G) := v.property.1
    have hvNorm : (v : G) ∈ Subgroup.normalizer (T : Set G) := v.property.2
    have hvN : (v : G) ∉ N := by
      intro hvN
      let vN : N := ⟨(v : G), hvN⟩
      have hvSub : vN ∈ (Subgroup.normalizer (T : Set G)).subgroupOf N :=
        hvNorm
      rw [Subgroup.subgroupOf_normalizer_eq hTleN] at hvSub
      have hvTN : vN ∈ TN := by
        rw [← hTNnorm]
        exact hvSub
      have hvT : (v : G) ∈ T := hvTN
      exact hstrong.inf_rightConjugate_involutionFree huN hvT
        ⟨hvI.1, hvI.2⟩
    let Tv : Subgroup G := N ⊓ rightConjugate N (v : G)
    obtain ⟨hTvcard0, _hvNormTv, hvInvTv0⟩ :=
      h.normalizer_inf_rightConjugate_card_eq_three_and_inverted_of_card_K_eq_two
        hk hvI (by simpa [N] using hvN)
    have hTvcard : Nat.card Tv = 3 := by
      simpa [Tv, N] using hTvcard0
    have hvInvTv :
        ∀ x : G, x ∈ Tv → (v : G) * x * (v : G)⁻¹ = x⁻¹ := by
      simpa [Tv, N] using hvInvTv0
    have hTleTv : T ≤ Tv := by
      intro x hxT
      refine ⟨hxT.1, ?_⟩
      have hconjT : (v : G) * x * (v : G)⁻¹ ∈ T :=
        (Subgroup.mem_normalizer_iff.mp hvNorm x).mp hxT
      have hmem :=
        BenderSuzuki.rightConjugateElem_mem_rightConjugate
          (M := N) (g := (v : G)) (hTleN hconjT)
      simpa [rightConjugateElem, mul_assoc] using hmem
    have hTvEq : Tv = T :=
      (Subgroup.eq_of_le_of_card_ge hTleTv (by
        rw [hTvcard, hTcard])).symm
    have hvInvT :
        ∀ x : G, x ∈ T → (v : G) * x * (v : G)⁻¹ = x⁻¹ := by
      intro x hxT
      exact hvInvTv x (by rw [hTvEq]; exact hxT)
    have hvuC : (v : G) * u ∈ Subgroup.centralizer (T : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hxT
      have hvInvInv : (v : G) * x⁻¹ * (v : G)⁻¹ = x := by
        have hc := congrArg Inv.inv (hvInvT x hxT)
        simpa [mul_inv_rev, mul_assoc] using hc
      have hfix :
          ((v : G) * u) * x * ((v : G) * u)⁻¹ = x := by
        calc
          ((v : G) * u) * x * ((v : G) * u)⁻¹ =
              (v : G) * (u * x * u⁻¹) * (v : G)⁻¹ := by group
          _ = (v : G) * x⁻¹ * (v : G)⁻¹ := by
            rw [huInv x hxT]
          _ = x := hvInvInv
      have hmul := congrArg (fun z : G ↦ z * ((v : G) * u)) hfix
      have hvux : ((v : G) * u) * x = x * ((v : G) * u) := by
        simpa [mul_assoc] using hmul
      exact hvux.symm
    have hvuT : (v : G) * u ∈ T := by
      exact hCent.le hvuC
    let xT : T := ⟨(v : G) * u, hvuT⟩
    refine ⟨xT, ?_⟩
    apply Subtype.ext
    change ((v : G) * u) * u = (v : G)
    rw [mul_assoc, huu, mul_one]
  have hcard :=
    Nat.card_congr (Equiv.ofBijective toFun
      ⟨htoFunInjective, htoFunSurjective⟩)
  change Nat.card InvNorm = 3
  calc
    Nat.card InvNorm = Nat.card T := hcard.symm
    _ = 3 := hTcard

end CFSG.GorensteinWalter
