module

public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Subgroup

theorem s16c1_G47_perfect_trivial {P W : Type*} [Group P] [Group W] [Finite W]
    [Group.IsPerfect P] (hW : Nat.card W ≤ 4) (ρ : P →* MulAut W) (g : P) : ρ g = 1 := by
  set φ : P →* Equiv.Perm W := (MulAut.toPerm W).comp ρ with hφ
  haveI : Group.IsSolvable (Equiv.Perm W) := Equiv.Perm.isSolvable hW
  haveI : Group.IsPerfect φ.range := Group.IsPerfect.range φ
  haveI : Group.IsSolvable φ.range := inferInstance
  have hsub : Subsingleton φ.range := by
    by_contra hns
    haveI : Nontrivial φ.range := not_subsingleton_iff_nontrivial.mp hns
    exact Group.IsPerfect.not_isSolvable (G := φ.range) inferInstance
  have h1 : φ g = 1 := by
    have := Subsingleton.elim (⟨φ g, g, rfl⟩ : φ.range) 1
    simpa using congrArg Subtype.val this
  ext x
  have := congrArg (fun σ : Equiv.Perm W => σ x) h1
  exact this

theorem s16c1_G47_perfect_comm {Γ : Type*} [Group Γ] {X W : Subgroup Γ} [Finite W]
    (hX : Group.IsPerfect X) (hXW : X ≤ normalizer (W : Set Γ)) (hW : Nat.card W ≤ 4) :
    ∀ x ∈ X, ∀ w ∈ W, x * w * x⁻¹ = w := by
  intro x hx w hw
  let ρ : X →* MulAut W :=
    (MulDistribMulAction.toMulAut (normalizer (W : Set Γ)) W).comp (Subgroup.inclusion hXW)
  have h := s16c1_G47_perfect_trivial (P := X) (W := W) hW ρ ⟨x, hx⟩
  have h2 := congrArg (fun σ : MulAut W => (σ ⟨w, hw⟩ : W).val) h
  exact h2

theorem s16c1_G47_cent_trivial {Hs : Type} [Group Hs] {Ys B Vs : Subgroup Hs}
    (hO2 : CFSG.pCore 2 Hs = ⊥) (hY : Ys.Normal)
    (hHs : ∀ h : Hs, ∃ y ∈ Ys, ∃ b ∈ B, h = y * b)
    (hVB : ∀ b ∈ B, ∀ v ∈ Vs, b * v * b⁻¹ ∈ Vs) (hV2 : IsPGroup 2 Vs) :
    ∀ v ∈ Vs, (∀ y ∈ Ys, v * y = y * v) → v = 1 := by
  set C : Subgroup Hs := Vs ⊓ centralizer (Ys : Set Hs) with hC
  have hconj : ∀ n ∈ C, ∀ g : Hs, g * n * g⁻¹ ∈ C := by
    intro n hn g
    obtain ⟨y, hy, b, hb, rfl⟩ := hHs g
    obtain ⟨hnV, hnc⟩ := Subgroup.mem_inf.1 hn
    have hbn : b * n * b⁻¹ ∈ C := by
      refine Subgroup.mem_inf.2 ⟨hVB b hb n hnV, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro y' hy'
      have hy'' : b⁻¹ * y' * b ∈ Ys := by
        have := hY.conj_mem y' hy' b⁻¹
        simpa using this
      have h1 := Subgroup.mem_centralizer_iff.1 hnc (b⁻¹ * y' * b) hy''
      calc y' * (b * n * b⁻¹) = b * ((b⁻¹ * y' * b) * n) * b⁻¹ := by group
        _ = b * (n * (b⁻¹ * y' * b)) * b⁻¹ := by rw [h1]
        _ = b * n * b⁻¹ * y' := by group
    have : y * b * n * (y * b)⁻¹ = y * (b * n * b⁻¹) * y⁻¹ := by group
    rw [this]
    have h2 : y * (b * n * b⁻¹) * y⁻¹ = b * n * b⁻¹ := by
      have := (Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hbn).2) y hy
      calc y * (b * n * b⁻¹) * y⁻¹ = (b * n * b⁻¹) * y * y⁻¹ := by rw [← this]
        _ = b * n * b⁻¹ := by group
    rw [h2]
    exact hbn
  haveI hCn : C.Normal := ⟨fun n hn g => hconj n hn g⟩
  have hCp : IsPGroup 2 C := hV2.to_le inf_le_left
  have hCle : C ≤ CFSG.pCore 2 Hs := le_sSup ⟨hCn, hCp⟩
  rw [hO2] at hCle
  intro v hv hvc
  have hvC : v ∈ C :=
    Subgroup.mem_inf.2 ⟨hv, Subgroup.mem_centralizer_iff.2 (fun y hy => (hvc y hy).symm)⟩
  exact Subgroup.mem_bot.1 (hCle hvC)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
