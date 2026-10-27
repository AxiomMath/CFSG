module

public import CFSG.RankThree.PartOne.KE8F.PairEmbed
public import CFSG.RankThree.PartOne.KE8F.E8Lang
public import CFSG.RankThree.PartOne.KE8F.BaseCase
public import CFSG.RankThree.PartOne.CTP.LinearCore

public noncomputable section

namespace CFSG.RankThree.PartOne.KE8F

open Matrix CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LieType.Steinberg.Adjoint CFSG.RankThree.Lattice
open CFSG.RankThree.Chevalley CFSG.RankThree.Classical
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.PartOne.KE
open scoped MatrixGroups Matrix Pointwise

set_option linter.unusedSectionVars false


section Roots

@[expose] def qr : Fin 4 → List ℤ :=
  ![[2, 3, 4, 6, 5, 4, 3, 2], [1, 2, 3, 4, 3, 2, 1, 0], [1, 1, 1, 1, 1, 1, 1, 0],
    [1, 0, 1, 1, 0, 0, 0, 0]]

@[expose] def qs : Fin 4 → List ℤ :=
  ![[2, 3, 4, 6, 5, 4, 3, 1], [2, 3, 4, 6, 5, 4, 3, 1], [2, 3, 4, 6, 5, 4, 3, 1],
    [2, 3, 4, 6, 4, 3, 2, 1]]

@[expose] def qv (j : Fin 4) : Fin Tag.E8.rank → ℤ := toVec Tag.E8.rank (qr j)

@[expose] def qw (j : Fin 4) : Fin Tag.E8.rank → ℤ := toVec Tag.E8.rank (qs j)

theorem qr_mem : ∀ j, qr j ∈ Tag.E8.artifactRoots := by decide +kernel

theorem qs_mem : ∀ j, qs j ∈ Tag.E8.artifactRoots := by decide +kernel

theorem qv_orth_list : ∀ j k : Fin 4, j ≠ k →
    toVec Tag.E8.rank (qr j) ⬝ᵥ (Tag.E8.symmetrizedCartan *ᵥ toVec Tag.E8.rank (qr k)) = 0 ∧
    toVec Tag.E8.rank (qr j) ⬝ᵥ (Tag.E8.symmetrizedCartan *ᵥ
      toVec Tag.E8.rank (lmulVec Tag.E8.rank e8P4VList (qr k))) = 0 ∧
    toVec Tag.E8.rank (lmulVec Tag.E8.rank e8P4VList (qr j)) ⬝ᵥ
      (Tag.E8.symmetrizedCartan *ᵥ toVec Tag.E8.rank (qr k)) = 0 ∧
    toVec Tag.E8.rank (lmulVec Tag.E8.rank e8P4VList (qr j)) ⬝ᵥ
      (Tag.E8.symmetrizedCartan *ᵥ toVec Tag.E8.rank (lmulVec Tag.E8.rank e8P4VList (qr k))) =
        0 := by
  decide +kernel

theorem qv_norm_list : ∀ j : Fin 4,
    iform (toVec Tag.E8.rank (qr j)) (toVec Tag.E8.rank (qr j)) = 2 ∧
    iform (toVec Tag.E8.rank (lmulVec Tag.E8.rank e8P4VList (qr j)))
      (toVec Tag.E8.rank (lmulVec Tag.E8.rank e8P4VList (qr j))) = 2 := by
  decide +kernel

theorem qv_parity_list : ∀ j : Fin 4,
    ¬ 2 ∣ iform (toVec Tag.E8.rank (qr j)) (toVec Tag.E8.rank (qs j)) ∧
    2 ∣ iform (toVec Tag.E8.rank (lmulVec Tag.E8.rank e8P4VList (qr j)))
      (toVec Tag.E8.rank (qs j)) := by
  decide +kernel

end Roots

theorem commute_four {G : Type*} [Group G] {a b c d : G} (c1 : Commute a c) (c2 : Commute a d)
    (c3 : Commute b c) (c4 : Commute b d) : a * b * (c * d) = c * d * (a * b) :=
  ((c1.mul_right c2).mul_left (c3.mul_right c4)).eq

section Main

variable {K L : Type} [Field K] [Finite K] [Field L] [Algebra K L] [IsAlgClosed L] {ℓ f : ℕ}
  [Fact ℓ.Prime] [CharP L ℓ]

theorem exists_four_commuting_SL2 (D : E8P4Frame0 K L ℓ f) (hℓ2 : ℓ ≠ 2) (hf : 1 ≤ f)
    {k₂ : Type} [Field k₂] [Finite k₂] [Algebra k₂ L] (hk₂ : Nat.card k₂ = ℓ ^ (2 * f)) :
    ∃ ι : Fin 4 → SL(2, k₂) →* adjointGroup .E8 K, (∀ j, Function.Injective (ι j)) ∧
      ∀ j k, j ≠ k → ∀ A B, ι j A * ι k B = ι k B * ι j A := by
  classical
  have hℓ : ℓ.Prime := Fact.out
  have hk4 : 4 ≤ Nat.card k₂ := by
    rw [hk₂]
    calc 4 ≤ 2 ^ 2 := by norm_num
      _ ≤ ℓ ^ 2 := Nat.pow_le_pow_left hℓ.two_le 2
      _ ≤ ℓ ^ (2 * f) := Nat.pow_le_pow_right hℓ.pos (by omega)
  have hperf : ⁅(⊤ : Subgroup SL(2, k₂)), (⊤ : Subgroup SL(2, k₂))⁆ = ⊤ :=
    Group.isPerfect_def.1 (CFSG.RankThree.PartOne.CTP.isPerfect_sl2 hk4)
  have hroot : ∀ j, IsRoot .E8 (qv j) := fun j => isRoot_toVec (qr_mem j)
  have hvroot : ∀ j, IsRoot .E8 (e8P4V *ᵥ qv j) := fun j => by
    have := IsRoot.smul (hroot j) ((coxeterSystem .E8).wordProd e8P4WW)
    rwa [e8P4_weylImage] at this
  have hw1 : ∀ j, weylQuotientHom .E8 L ⟨D.n, D.hnm⟩ • qv j = e8P4V *ᵥ qv j := fun j => by
    rw [D.hnW]
    exact e8P4_weylImage _
  have hw2 : ∀ j, weylQuotientHom .E8 L ⟨D.n, D.hnm⟩ • (e8P4V *ᵥ qv j) = -qv j := fun j => by
    rw [D.hnW, e8P4_weylImage, e8P4V_mulVec_mulVec]
  have hmv : ∀ j, e8P4V *ᵥ qv j = toVec Tag.E8.rank (lmulVec Tag.E8.rank e8P4VList (qr j)) :=
    fun j => by
    rw [toVec_lmulVec, ← e8P4V_eq]
    rfl
  have hemb : ∀ j, ∃ e : SL(2, k₂) →* ModGL .E8 L, Function.Injective e ∧
      (∀ A, ∃ X Y : SL2 L, e A = rootSL2 .E8 L (qv j) X * rootSL2 .E8 L (e8P4V *ᵥ qv j) Y) ∧
      (∀ A, e A ∈ adjointGroup .E8 L) ∧
      (∀ A, D.n * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) (e A) * D.n⁻¹ = e A) :=
    fun j => pair_A1_embedding hℓ2 D.hnm (hroot j) (hvroot j) (hw1 j) (hw2 j)
      (e8P4_orth (hroot j)) hk₂ (by simpa [qv] using (qv_norm_list j).1)
      (by rw [hmv]; exact (qv_norm_list j).2) (σ := qw j) (isRoot_toVec (qs_mem j))
      (by simpa [qv, qw] using (qv_parity_list j).1)
      (by rw [hmv]; simpa [qw] using (qv_parity_list j).2)
  choose e he_inj he_form he_adj he_fix using hemb
  have hlift : ∀ j, ∃ ι : SL(2, k₂) →* adjointGroup .E8 K,
      ∀ A, adjEmb .E8 K L (ι A) = D.g0 * e j A * D.g0⁻¹ := fun j =>
    exists_hom_to_C D hperf (e j) (he_adj j) (he_fix j)
  choose ι hι using hlift
  refine ⟨ι, fun j A B hAB => ?_, fun j k hjk A B => ?_⟩
  · apply he_inj j
    have h1 := congrArg (adjEmb .E8 K L) hAB
    rw [hι j A, hι j B] at h1
    have h2 := mul_left_cancel (mul_right_cancel h1)
    exact h2
  · apply adjEmb_injective (τ := .E8) (K := K) (L := L)
    rw [map_mul, map_mul, hι j A, hι k B]
    obtain ⟨X, Y, hXY⟩ := he_form j A
    obtain ⟨X', Y', hXY'⟩ := he_form k B
    obtain ⟨o1, o2, o3, o4⟩ := qv_orth_list j k hjk
    rw [← hmv k] at o2
    rw [← hmv j] at o3
    rw [← hmv j, ← hmv k] at o4
    have c1 := e8_rootSL2_commute_of_orth (L := L) (hroot j) (hroot k) o1 X X'
    have c2 := e8_rootSL2_commute_of_orth (L := L) (hroot j) (hvroot k) o2 X Y'
    have c3 := e8_rootSL2_commute_of_orth (L := L) (hvroot j) (hroot k) o3 Y X'
    have c4 := e8_rootSL2_commute_of_orth (L := L) (hvroot j) (hvroot k) o4 Y Y'
    have hc : e j A * e k B = e k B * e j A := by
      rw [hXY, hXY']
      exact commute_four c1 c2 c3 c4
    calc D.g0 * e j A * D.g0⁻¹ * (D.g0 * e k B * D.g0⁻¹) = D.g0 * (e j A * e k B) * D.g0⁻¹ := by
          group
      _ = D.g0 * (e k B * e j A) * D.g0⁻¹ := by rw [hc]
      _ = D.g0 * e k B * D.g0⁻¹ * (D.g0 * e j A * D.g0⁻¹) := by group

end Main

end CFSG.RankThree.PartOne.KE8F
