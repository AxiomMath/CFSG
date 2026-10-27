module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import CFSG.LocalAnalysis.ZStar.BrauerCoefficientFormula
public import Mathlib.GroupTheory.Nilpotent

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG

namespace ZStar.PrincipalRegularPower

open ZStar.Helpers ZStar
  ZStar.BrauerProjection ZStar.BrauerPrincipal
  ZStar.BrauerBlockLift ZStar.BrauerCoefficientFormula

universe u

noncomputable section

variable {G : Type u} [Group G] [Fintype G]

noncomputable local instance subgroupFintype (H : Subgroup G) : Fintype H :=
  Fintype.ofFinite H

@[expose] noncomputable def twoRegularSum (X : Type*) [Group X] [Fintype X] :
    GroupAlgebraTwo X := by
  classical
  exact ∑ x : X, if Odd (orderOf x) then MonoidAlgebra.single x 1 else 0

@[simp]
theorem twoRegularSum_coeff (X : Type*) [Group X] [Fintype X] (x : X) :
    (twoRegularSum X).coeff x = if Odd (orderOf x) then 1 else 0 := by
  classical
  unfold twoRegularSum
  rw [MonoidAlgebra.coeff_sum, Finset.sum_apply']
  calc
    (∑ k : X,
        (if Odd (orderOf k) then
          MonoidAlgebra.single k (1 : ZMod 2) else 0).coeff x) =
        (if Odd (orderOf x) then
          MonoidAlgebra.single x (1 : ZMod 2) else 0).coeff x := by
      apply Finset.sum_eq_single
      · intro b _ hbx
        by_cases hb : Odd (orderOf b) <;> simp [hb, hbx]
      · simp
    _ = if Odd (orderOf x) then 1 else 0 := by
      by_cases hx : Odd (orderOf x) <;> simp [hx]

theorem twoRegularSum_central (X : Type*) [Group X] [Fintype X] :
    IsGroupCentral X (twoRegularSum X) := by
  intro g
  ext x
  simp only [MonoidAlgebra.coeff_single_mul_apply,
    MonoidAlgebra.coeff_mul_single_apply, one_mul, mul_one,
    twoRegularSum_coeff]
  have hconj : g * (g⁻¹ * x) * g⁻¹ = x * g⁻¹ := by group
  have hiff : Odd (orderOf (g⁻¹ * x)) ↔ Odd (orderOf (x * g⁻¹)) := by
    rw [← hconj, orderOf_conj_eq]
  by_cases h : Odd (orderOf (g⁻¹ * x))
  · rw [ite_eq_left h, ite_eq_left (hiff.mp h)]
  · rw [ite_eq_right h, ite_eq_right (fun hx => h (hiff.mpr hx))]

theorem augmentation_twoRegularSum (X : Type*) [Group X] [Fintype X] :
    augmentationHom X (twoRegularSum X) = 1 := by
  classical
  let s : Finset X :=
    (Finset.univ.filter fun x : X => Odd (orderOf x)).erase 1
  have hs : (∑ x ∈ s, (1 : ZMod 2)) = 0 := by
    apply Finset.sum_involution (fun x _ => x⁻¹)
    · intro x hx
      exact CharTwo.add_self_eq_zero 1
    · intro x hx _ hfix
      have hxne : x ≠ 1 := by
        exact (Finset.mem_erase.mp hx).1
      have hx2 : x * x = 1 := by
        have h := congrArg (fun y : X => x * y) hfix.symm
        simpa only [mul_inv_cancel] using h
      have hord : orderOf x = 2 :=
        orderOf_eq_prime (by simpa [pow_two] using hx2) hxne
      have hodd : Odd (orderOf x) :=
        (Finset.mem_filter.mp (Finset.mem_erase.mp hx).2).2
      rw [hord] at hodd
      obtain ⟨k, hk⟩ := hodd
      omega
    · intro x hx
      exact inv_inv x
    · intro x hx
      rw [Finset.mem_erase] at hx ⊢
      refine ⟨?_, ?_⟩
      · intro h
        apply hx.1
        exact inv_eq_one.mp h
      · rw [Finset.mem_filter] at hx ⊢
        refine ⟨Finset.mem_univ _, ?_⟩
        simpa using hx.2.2
  rw [augmentationHom_apply]
  unfold augmentationTwo
  simp only [twoRegularSum_coeff]
  have hone : Odd (orderOf (1 : X)) := by simp
  calc
    (∑ x : X, if Odd (orderOf x) then (1 : ZMod 2) else 0) =
        ∑ x ∈ (Finset.univ.filter fun x : X => Odd (orderOf x)),
          (1 : ZMod 2) := by
      rw [Finset.sum_filter]
    _ = 1 + ∑ x ∈ s, (1 : ZMod 2) := by
      rw [show (Finset.univ.filter fun x : X => Odd (orderOf x)) =
          insert 1 s by
        ext x
        simp only [s, Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_insert, Finset.mem_erase]
        constructor
        · intro hx
          by_cases h : x = 1
          · exact Or.inl h
          · exact Or.inr ⟨h, by simpa using hx⟩
        · rintro (rfl | ⟨_, hx⟩)
          · exact hone
          · exact hx]
      rw [Finset.sum_insert]
      simp [s]
    _ = 1 := by rw [hs, add_zero]

def TwoRegularSumInPrincipalBlock
    (X : Type*) [Group X] [Fintype X] : Prop :=
  principalBlockCandidate X * twoRegularSum X = twoRegularSum X

private theorem isGroupCentral_sub
    (X : Type*) [Group X] {a b : GroupAlgebraTwo X}
    (ha : IsGroupCentral X a) (hb : IsGroupCentral X b) :
    IsGroupCentral X (a - b) := by
  intro g
  rw [mul_sub, sub_mul, ha g, hb g]

private theorem principalBlockCandidate_mul_sub_self
    (hsection : TwoRegularSumInPrincipalBlock G) :
    principalBlockCandidate G *
        (principalBlockCandidate G - twoRegularSum G) =
      principalBlockCandidate G - twoRegularSum G := by
  rw [mul_sub, principalBlockCandidate_idempotent, hsection]

private theorem exists_twoPower_twoRegularSum_eq_principal
    (hsection : TwoRegularSumInPrincipalBlock G) :
    ∃ n : ℕ, (twoRegularSum G) ^ (2 ^ n) = principalBlockCandidate G := by
  classical
  let e : GroupAlgebraTwo G := principalBlockCandidate G
  let r : GroupAlgebraTwo G := twoRegularSum G
  let x : GroupAlgebraTwo G := e - r
  have hecentral : IsGroupCentral G e := principalBlockCandidate_central G
  have hrcentral : IsGroupCentral G r := twoRegularSum_central G
  have hxcentral : IsGroupCentral G x :=
    isGroupCentral_sub G hecentral hrcentral
  have hex : e * x = x := by
    simpa only [e, r, x] using
      principalBlockCandidate_mul_sub_self hsection
  have hxaug : augmentationHom G x = 0 := by
    dsimp only [x, e, r]
    rw [map_sub, augmentationHom_apply,
      principalBlockCandidate_augmentation,
      augmentation_twoRegularSum, sub_self]
  let : Fintype (GroupAlgebraTwo G) :=
    Fintype.ofEquiv (G →₀ ZMod 2) MonoidAlgebra.coeffEquiv.symm
  obtain ⟨n, hnpos, hnidem⟩ := exists_positive_idempotent_power x
  have hxpowcentral : IsGroupCentral G (x ^ n) :=
    isGroupCentral_pow x hxcentral n
  have hexpow : e * x ^ n = x ^ n := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hnpos
    calc
      e * x ^ (k + 1) = e * (x * x ^ k) := by rw [pow_succ']
      _ = (e * x) * x ^ k := by rw [mul_assoc]
      _ = x ^ (k + 1) := by rw [hex, pow_succ']
  have hxpowzero : x ^ n = 0 := by
    rcases principalBlockCandidate_primitive G (x ^ n) hxpowcentral
        hnidem (by simpa only [e] using hexpow) with hzero | heq
    · exact hzero
    · have haugpow : augmentationHom G (x ^ n) = 0 := by
        rw [map_pow, hxaug, zero_pow hnpos]
      have hauge : augmentationHom G e = 1 := by
        dsimp only [e]
        rw [augmentationHom_apply, principalBlockCandidate_augmentation]
      rw [heq, hauge] at haugpow
      exact (one_ne_zero haugpow).elim
  have hnle : n ≤ 2 ^ n := by
    simpa using Nat.choose_le_two_pow n 1
  have hxfrob : x ^ (2 ^ n) = 0 :=
    pow_eq_zero_of_le hnle hxpowzero
  have hepow : e ^ (2 ^ n) = e := by
    exact IsIdempotentElem.pow_eq (principalBlockCandidate_idempotent G)
      (by positivity)
  have hcomm : Commute e r := hecentral.commute G r
  let : CharP (GroupAlgebraTwo G) 2 :=
    CharP.of_ringHom_of_ne_zero
      (algebraMap (ZMod 2) (GroupAlgebraTwo G)) 2 (by omega)
  have hsubpow := sub_pow_char_pow_of_commute 2 n hcomm
  change x ^ (2 ^ n) = e ^ (2 ^ n) - r ^ (2 ^ n) at hsubpow
  refine ⟨n, ?_⟩
  rw [hxfrob, hepow] at hsubpow
  exact (sub_eq_zero.mp hsubpow.symm).symm

theorem brauerProjection_twoRegularSum (w : G) :
    brauerProjection w (twoRegularSum G) =
      twoRegularSum (involutionCentralizer w) := by
  ext x
  rw [brauerProjection_coeff, twoRegularSum_coeff, twoRegularSum_coeff]
  have horder : orderOf (x : G) = orderOf x := Subgroup.orderOf_coe x
  by_cases h : Odd (orderOf (x : G))
  · rw [ite_eq_left h, ite_eq_left (horder ▸ h)]
  · rw [ite_eq_right h, ite_eq_right (fun hx => h (horder.symm ▸ hx))]

theorem projectedPrincipalBlock_eq_principal_of_twoRegularSection
    (w : G) (hw2 : w * w = 1)
    (hsectionG : TwoRegularSumInPrincipalBlock G)
    (hsectionC : TwoRegularSumInPrincipalBlock (involutionCentralizer w)) :
    projectedPrincipalBlock w =
      principalBlockCandidate (involutionCentralizer w) := by
  obtain ⟨m, hm⟩ :=
    exists_twoPower_twoRegularSum_eq_principal hsectionG
  obtain ⟨n, hn⟩ :=
    exists_twoPower_twoRegularSum_eq_principal hsectionC
  have hm' : (twoRegularSum G) ^ (2 ^ (m + n)) =
      principalBlockCandidate G := by
    rw [pow_add, pow_mul]
    rw [hm]
    exact IsIdempotentElem.pow_eq (principalBlockCandidate_idempotent G)
      (by positivity)
  have hn' :
      (twoRegularSum (involutionCentralizer w)) ^ (2 ^ (m + n)) =
        principalBlockCandidate (involutionCentralizer w) := by
    rw [pow_add, Nat.mul_comm, pow_mul]
    rw [hn]
    exact IsIdempotentElem.pow_eq
      (principalBlockCandidate_idempotent (involutionCentralizer w))
      (by positivity)
  calc
    projectedPrincipalBlock w =
        brauerProjection w ((twoRegularSum G) ^ (2 ^ (m + n))) := by
      rw [hm']
      rfl
    _ = (brauerProjection w (twoRegularSum G)) ^ (2 ^ (m + n)) :=
      brauerProjection_pow w hw2 (twoRegularSum G)
        (twoRegularSum_central G) _
    _ = (twoRegularSum (involutionCentralizer w)) ^ (2 ^ (m + n)) := by
      rw [brauerProjection_twoRegularSum]
    _ = principalBlockCandidate (involutionCentralizer w) := hn'

end

end ZStar.PrincipalRegularPower

end CFSG
