module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970API
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970_18
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.PiCoreCharacteristic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.FStarCommute
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma27FittingDecomposition
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# `[M, ⟨t⟩]` centralizes `F(M)` under the π/πᶜ action hypotheses

This is the automorphism computation of the paper's Lemma 2.7:
`t` centralizes `F_π(M)` and inverts `F_{πᶜ}(M)`; the Fitting subgroup
splits as the commuting join of those two Hall parts, so every commutator
`[m,t]` acts trivially on `F(M)`.  The result is stated as
`⁅M, ⟨t⟩⁆ ≤ C_G(F(M))`; combining it with solvability
(`C_M(F(M)) ≤ F(M)`) yields `[M,t] ≤ F(M)`.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

open scoped Pointwise commutatorElement

/-- If `t` centralizes the `π`-part of `F(M)` and inverts its `πᶜ`-part,
then every commutator `[m,t]` centralizes `F(M)`. -/
public theorem commutator_centralizes_fittingSubgroupOf_of_centralizes_inverts
    {G : Type u} [Group G] [Finite G]
    (M : Subgroup G) (t : G) (htM : t ∈ M) (ht : IsInvolution t)
    (π : Set ℕ)
    (hAcent : t ∈ Subgroup.centralizer (piCoreOf (fittingSubgroupOf M) π : Set G))
    (hBinv : ∀ x : G, x ∈ (piCoreOf (fittingSubgroupOf M) πᶜ : Set G) →
      t * x * t⁻¹ = x⁻¹) :
    ⁅M, Subgroup.zpowers t⁆ ≤
      Subgroup.centralizer ((fittingSubgroupOf M : Subgroup G) : Set G) := by
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
  have hFtop : piCore π (↥F) ⊔ piCore πᶜ (↥F) = ⊤ :=
    piCore_sup_piCore_compl_eq_top_of_isNilpotent hFnil π
  have hA_norm_M : IsNormalIn A M := by
    have h := fstar_characteristic_subgroupOf_map_normal_in
      (A := M) (F := F) (K := piCore π (↥F))
      (piCore_characteristic π)
      (by simpa [F] using fittingSubgroupOf_isNormalIn M)
    simpa [A, piCoreOf] using h
  have hB_norm_M : IsNormalIn B M := by
    have h := fstar_characteristic_subgroupOf_map_normal_in
      (A := M) (F := F) (K := piCore πᶜ (↥F))
      (piCore_characteristic πᶜ)
      (by simpa [F] using fittingSubgroupOf_isNormalIn M)
    simpa [B, piCoreOf] using h
  have hM_normA : M ≤ Subgroup.normalizer (A : Set G) :=
    le_normalizer_of_isNormalIn hA_norm_M
  have hM_normB : M ≤ Subgroup.normalizer (B : Set G) :=
    le_normalizer_of_isNormalIn hB_norm_M
  have ht_sq : t * t = 1 := by simpa [pow_two] using ht.2
  have ht_inv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht_sq
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
  have hsq : t ^ (2 : ℤ) = 1 := by
    simpa [zpow_ofNat] using ht.2
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
  rcases ht_zpow n with h1 | htpow
  · rw [h1]
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    simp [commutatorElement_def]
  · rw [htpow]
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    let xF : ↥F := ⟨x, hx⟩
    have hxFjoin : xF ∈ piCore π (↥F) ⊔ piCore πᶜ (↥F) := by
      rw [hFtop]
      exact Subgroup.mem_top xF
    have hprod : ((A0 ⊔ B0 : Subgroup (↥F)) : Set (↥F)) =
        (A0 : Set (↥F)) * (B0 : Set (↥F)) :=
      Subgroup.mul_normal A0 B0
    have hxprod : xF ∈ (A0 : Set (↥F)) * (B0 : Set (↥F)) := by
      rw [← hprod]
      exact hxFjoin
    rcases (Set.mem_mul).1 hxprod with ⟨a0, ha0, b0, hb0, hab0⟩
    let a : G := (a0 : ↥F)
    let b : G := (b0 : ↥F)
    have haA : a ∈ A := by
      dsimp [a, A, A0, piCoreOf]
      exact Subgroup.mem_map.mpr ⟨a0, ha0, rfl⟩
    have hbB : b ∈ B := by
      dsimp [b, B, B0, piCoreOf]
      exact Subgroup.mem_map.mpr ⟨b0, hb0, rfl⟩
    have hab : a * b = x := by
      have h := congrArg Subtype.val hab0
      simpa [a, b, xF] using h
    have ha' : m⁻¹ * a * m ∈ A := by
      simpa using (Subgroup.mem_normalizer_iff.mp (hM_normA (M.inv_mem hm)) a).mp haA
    have hb' : m⁻¹ * b * m ∈ B := by
      simpa using (Subgroup.mem_normalizer_iff.mp (hM_normB (M.inv_mem hm)) b).mp hbB
    have hta_comm : t * a = a * t := by
      have hcomm := (Subgroup.mem_centralizer_iff (g := t) (s := (A : Set G))).1 hAcent a haA
      exact hcomm.symm
    have htabt : t * a * b * t = a * b⁻¹ := by
      calc
        t * a * b * t = a * (t * b * t) := by
          rw [hta_comm]
          group
        _ = a * b⁻¹ := by rw [hBinvElem b hbB]
    have hsplit : ∀ X Y : G, (t * X * t) * (t * Y * t) = t * (X * Y) * t := by
      intro X Y
      calc
        (t * X * t) * (t * Y * t) = t * X * (t * t) * Y * t := by group
        _ = t * X * Y * t := by rw [ht_sq]; simp
        _ = t * (X * Y) * t := by group
    have hmain : ⁅m, t⁆ * x * (⁅m, t⁆)⁻¹ = a * b := by
      calc
        ⁅m, t⁆ * x * (⁅m, t⁆)⁻¹
            = (m * t * m⁻¹ * t) * (a * b) * (t * m * t * m⁻¹) := by
                simp [commutatorElement_def, hab, ht_inv]
                group
        _ = m * (t * m⁻¹ * (t * a * b * t) * m * t) * m⁻¹ := by group
        _ = m * (t * (m⁻¹ * (t * a * b * t) * m) * t) * m⁻¹ := by group
        _ = m * (t * (m⁻¹ * (a * b⁻¹) * m) * t) * m⁻¹ := by rw [htabt]
        _ = m * (t * ((m⁻¹ * a * m) * (m⁻¹ * b⁻¹ * m)) * t) * m⁻¹ := by group
        _ = m * (t * ((m⁻¹ * a * m) * (m⁻¹ * b * m)⁻¹) * t) * m⁻¹ := by
              rw [show (m⁻¹ * b⁻¹ * m) = (m⁻¹ * b * m)⁻¹ by group]
        _ = m * ((t * (m⁻¹ * a * m) * t) *
            (t * (m⁻¹ * b * m)⁻¹ * t)) * m⁻¹ := by
              rw [← hsplit (m⁻¹ * a * m) (m⁻¹ * b * m)⁻¹]
        _ = m * ((m⁻¹ * a * m) * (t * (m⁻¹ * b * m)⁻¹ * t)) * m⁻¹ := by
              rw [show t * (m⁻¹ * a * m) * t = m⁻¹ * a * m by
                exact hAcentElem (m⁻¹ * a * m) ha']
        _ = m * ((m⁻¹ * a * m) * (m⁻¹ * b * m)) * m⁻¹ := by
              rw [show t * (m⁻¹ * b * m)⁻¹ * t = m⁻¹ * b * m by
                simpa using hBinvElem (m⁻¹ * b * m)⁻¹ (B.inv_mem hb')]
        _ = a * b := by group
    have hxcomm : x * ⁅m, t⁆ = ⁅m, t⁆ * x := by
      calc
        x * ⁅m, t⁆ = (⁅m, t⁆ * x * (⁅m, t⁆)⁻¹) * ⁅m, t⁆ := by
          rw [hmain]
          rw [hab]
        _ = ⁅m, t⁆ * x := by group
    exact hxcomm

end CFSG.GorensteinWalter
