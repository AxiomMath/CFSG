module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970API
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970_18
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970_16
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.ControlCore
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma27FittingDecomposition
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.SubnormalPSubgroupLeQCore
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# The `[M, ⟨t⟩] ≤ F_{πᶜ}(M)` step of Lemma 2.7

Once `t` centralizes `F_π(M)` and inverts `F_{πᶜ}(M)`, every commutator
`[m,t]` centralizes `F(M)`.  If `[m,t]` itself lies in the nilpotent
Fitting subgroup and `O₂(M) = 1`, the fact that `t` inverts `[m,t]` forces
the `π`-part of the commutator to be trivial; hence the whole commutator
lies in `F_{πᶜ}(M)`.
-/

noncomputable section

open scoped Pointwise commutatorElement

namespace CFSG.GorensteinWalter

universe u

/-- A subgroup which lies in `M`, centralizes `F(M)`, and centralizes under
`E(M) = 1` is contained in `F(M)`. -/
public theorem le_fittingSubgroupOf_of_le_centralizer_fittingSubgroupOf_of_componentLayer_eq_bot
    {G : Type u} [Group G] [Finite G]
    (M K : Subgroup G) (hKleM : K ≤ M)
    (hCent : K ≤ Subgroup.centralizer
      ((fittingSubgroupOf M : Subgroup G) : Set G))
    (hE : componentLayerOf M = ⊥) :
    K ≤ fittingSubgroupOf M := by
  have hFstar : generalizedFittingSubgroupOf M = fittingSubgroupOf M := by
    simp [generalizedFittingSubgroupOf, hE]
  intro x hx
  have hxC : x ∈ Subgroup.centralizer
      ((generalizedFittingSubgroupOf M : Subgroup G) : Set G) := by
    rw [hFstar]
    exact hCent hx
  have hx' := centralizer_intersection_fstar_le_fstar M ⟨hxC, hKleM hx⟩
  simpa [hFstar] using hx'

/-- The automorphism step of Lemma 2.7: under centralization of the `π`-part,
inversion of the `πᶜ`-part, and `O₂(M) = 1`, every commutator with `t`
lies in `F_{πᶜ}(M)` provided it lies in and centralizes `F(M)`. -/
public theorem commutator_le_piCoreOf_compl_of_centralizes_fitting_of_twoCore_bot
    {G : Type u} [Group G] [Finite G]
    (M : Subgroup G) (t : G) (ht : IsInvolution t) (π : Set ℕ)
    (hF : ⁅M, Subgroup.zpowers t⁆ ≤ fittingSubgroupOf M)
    (hCent : ⁅M, Subgroup.zpowers t⁆ ≤
       Subgroup.centralizer ((fittingSubgroupOf M : Subgroup G) : Set G))
    (hO2 : twoCoreOf M = ⊥)
    (hAcent : t ∈ Subgroup.centralizer
      ((piCoreOf (fittingSubgroupOf M) π : Subgroup G) : Set G))
    (hBinv : ∀ x : G,
      x ∈ (piCoreOf (fittingSubgroupOf M) πᶜ : Set G) → t * x * t⁻¹ = x⁻¹) :
    ⁅M, Subgroup.zpowers t⁆ ≤ piCoreOf (fittingSubgroupOf M) πᶜ := by
  classical
  let F : Subgroup G := fittingSubgroupOf M
  let A : Subgroup G := piCoreOf F π
  let B : Subgroup G := piCoreOf F πᶜ
  let A0 : Subgroup (↥F) := piCore π (↥F)
  let B0 : Subgroup (↥F) := piCore πᶜ (↥F)
  have hFnil : Group.IsNilpotent (↥F) := by
    dsimp [F]
    exact fittingSubgroupOf_isNilpotent M
  have : Group.IsNilpotent (↥F) := hFnil
  have : A0.Normal := by dsimp [A0]; exact piCore_normal_local π
  have : B0.Normal := by dsimp [B0]; exact piCore_normal_local πᶜ
  have hFtop : A0 ⊔ B0 = (⊤ : Subgroup (↥F)) :=
    piCore_sup_piCore_compl_eq_top_of_isNilpotent hFnil π
  have ht_sq : t * t = 1 := by simpa [pow_two] using ht.2
  have ht_inv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht_sq
  have hsq : t ^ (2 : ℤ) = 1 := by simpa [zpow_ofNat] using ht.2
  have ht_zpow : ∀ n : ℤ, t ^ n = 1 ∨ t ^ n = t := by
    intro n
    rcases Int.even_or_odd n with h | h
    · left
      rcases h with ⟨k, hk⟩
      rw [hk, ← two_mul, zpow_mul, hsq]
      simp
    · right
      rcases h with ⟨k, hk⟩
      rw [hk, zpow_add, zpow_mul, hsq]
      simp
  have hAcentElem : ∀ y : G, y ∈ A → t * y * t = y := by
    intro y hy
    have hcomm : y * t = t * y :=
      (Subgroup.mem_centralizer_iff (g := t) (s := (A : Set G))).1 hAcent y hy
    calc
      t * y * t = y * t * t := by rw [hcomm]
      _ = y * (t * t) := by rw [mul_assoc]
      _ = y := by rw [ht_sq]; simp
  have hBinvElem : ∀ y : G, y ∈ B → t * y * t = y⁻¹ := by
    intro y hy
    simpa [ht_inv] using hBinv y hy
  rw [Subgroup.commutator_le]
  intro m hm z hz
  rcases Subgroup.mem_zpowers_iff.mp hz with ⟨n, rfl⟩
  rcases ht_zpow n with h1 | htpow
  · rw [h1]
    simp [commutatorElement_def]
  · rw [htpow]
    let c : G := ⁅m, t⁆
    change c ∈ piCoreOf (fittingSubgroupOf M) πᶜ
    have hcF : c ∈ F := by
      exact hF (Subgroup.commutator_mem_commutator hm (Subgroup.mem_zpowers t))
    have hcC : c ∈ Subgroup.centralizer (F : Set G) := by
      exact hCent (Subgroup.commutator_mem_commutator hm (Subgroup.mem_zpowers t))
    let cF : ↥F := ⟨c, hcF⟩
    have hcprod0 : cF ∈ A0 ⊔ B0 := by
      rw [hFtop]
      exact Subgroup.mem_top cF
    have hprod : ((A0 ⊔ B0 : Subgroup (↥F)) : Set (↥F)) =
        (A0 : Set (↥F)) * (B0 : Set (↥F)) :=
      Subgroup.mul_normal A0 B0
    have hcprod : cF ∈ (A0 : Set (↥F)) * (B0 : Set (↥F)) := by
      rwa [← hprod]
    rcases (Set.mem_mul).1 hcprod with ⟨a0, ha0, b0, hb0, hab0⟩
    let a : G := (a0 : ↥F)
    let b : G := (b0 : ↥F)
    have haA : a ∈ A := by
      dsimp [a, A, A0, piCoreOf]
      exact Subgroup.mem_map.mpr ⟨a0, ha0, rfl⟩
    have hbB : b ∈ B := by
      dsimp [b, B, B0, piCoreOf]
      exact Subgroup.mem_map.mpr ⟨b0, hb0, rfl⟩
    have hab : a * b = c := by
      have h := congrArg Subtype.val hab0
      simpa [a, b, cF] using h
    have hcommAB : ⁅A, B⁆ = ⊥ :=
      piCoreOf_commutator_piCoreOf_compl_eq_bot M π
    have hAcentB : A ≤ Subgroup.centralizer (B : Set G) :=
      (Subgroup.commutator_eq_bot_iff_le_centralizer (H₁ := A) (H₂ := B)).1 hcommAB
    have hba : b * a = a * b :=
      (Subgroup.mem_centralizer_iff (g := a) (s := (B : Set G))).1 (hAcentB haA) b hbB
    have hba_inv : b⁻¹ * a⁻¹ = a⁻¹ * b⁻¹ := by
      have hsame : (b * a)⁻¹ = (a * b)⁻¹ := by rw [hba]
      have hs := by simpa [mul_inv_rev] using hsame
      exact hs.symm
    have htc : t * c * t⁻¹ = c⁻¹ := by
      have hcdef : c = m * t * m⁻¹ * t := by
        simp [c, commutatorElement_def, ht_inv]
      calc
        t * c * t⁻¹ = t * (m * t * m⁻¹ * t) * t := by rw [hcdef, ht_inv]
        _ = t * m * t * m⁻¹ := by
          calc
            t * (m * t * m⁻¹ * t) * t = t * m * (t * m⁻¹ * (t * t)) := by group
            _ = t * m * (t * m⁻¹ * 1) := by rw [ht_sq]
            _ = t * m * t * m⁻¹ := by group
        _ = (m * t * m⁻¹ * t)⁻¹ := by
          group
          simp [ht_inv]
        _ = c⁻¹ := by rw [hcdef]
    have htct : t * c * t⁻¹ = a * b⁻¹ := by
      calc
        t * c * t⁻¹ = t * (a * b) * t⁻¹ := by rw [hab]
        _ = (t * a * t⁻¹) * (t * b * t⁻¹) := by group
        _ = (t * a * t) * (t * b * t) := by simp [ht_inv]
        _ = a * b⁻¹ := by rw [hAcentElem a haA, hBinvElem b hbB]
    have hcinv : c⁻¹ = a⁻¹ * b⁻¹ := by
      calc
        c⁻¹ = (a * b)⁻¹ := by rw [hab]
        _ = b⁻¹ * a⁻¹ := by simp [mul_inv_rev]
        _ = a⁻¹ * b⁻¹ := hba_inv
    have hEqb : a * b⁻¹ = a⁻¹ * b⁻¹ := by
      calc
        a * b⁻¹ = t * c * t⁻¹ := htct.symm
        _ = c⁻¹ := htc
        _ = a⁻¹ * b⁻¹ := hcinv
    have ha_inv : a = a⁻¹ := by
      have h := congrArg (fun x : G => x * b) hEqb
      simpa [mul_assoc] using h
    have ha2 : a ^ 2 = 1 := by
      calc
        a ^ 2 = a * a := by rw [pow_two]
        _ = a * a⁻¹ := by nth_rw 2 [ha_inv]
        _ = 1 := mul_inv_cancel a
    have ha1 : a = 1 := by
      by_contra hane
      have hord : orderOf a = 2 := orderOf_eq_prime ha2 hane
      have hzleF : Subgroup.zpowers a ≤ F :=
        Subgroup.zpowers_le.mpr ((piCoreOf_le F π) haA)
      have hsubF : ((Subgroup.zpowers a).subgroupOf F).IsSubnormal :=
        isSubnormal_of_nilpotent hFnil (Subgroup.zpowers a) hzleF
      have hFM : F ≤ M := by
        simpa [F] using (fittingSubgroupOf_isNormalIn M).1
      have hFnormM : IsNormalIn F M := by
        simpa [F] using fittingSubgroupOf_isNormalIn M
      have hsubM : ((Subgroup.zpowers a).subgroupOf M).IsSubnormal :=
        isSubnormal_of_isNormalIn_subgroup hFM hFnormM hzleF hsubF
      have hzleM : Subgroup.zpowers a ≤ M := hzleF.trans hFM
      have hzp : IsPGroup 2 (Subgroup.zpowers a) := by
        have hcard : Nat.card (Subgroup.zpowers a) = 2 := by
          rw [Nat.card_zpowers]
          exact hord
        refine IsPGroup.of_card (n := 1) ?_
        simpa [hcard]
      have hzQ : Subgroup.zpowers a ≤ qCoreOf M 2 :=
        le_qCoreOf_of_isSubnormal_isPGroup M (Subgroup.zpowers a) 2 hzleM hsubM hzp
      have hO2q : qCoreOf M 2 = ⊥ := by
        have hq : qCoreOf M 2 = twoCoreOf M := by
          rw [twoCoreOf_eq_piCoreOf_2, qCoreOf_eq_piCoreOf_singleton M 2 Nat.prime_two]
        rw [hq, hO2]
      have haQ : a ∈ qCoreOf M 2 := hzQ (Subgroup.mem_zpowers a)
      have haO2 : a ∈ (⊥ : Subgroup G) := by simpa [hO2q] using haQ
      exact hane (Subgroup.mem_bot.mp haO2)
    have hcb : c = b := by
      rw [← hab, ha1, one_mul]
    rw [hcb]
    exact hbB

end CFSG.GorensteinWalter
