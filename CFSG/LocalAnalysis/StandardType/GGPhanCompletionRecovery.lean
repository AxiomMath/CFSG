module

public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanCharTwoDefs
public import CFSG.ClassicalInvolution.Phan.AmalgamMaps
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2OddCenter
public import CFSG.ClassicalInvolution.Models.LinearPairs
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanEDefs

public noncomputable section

namespace CFSG.ClassicalInvolution.Phan

open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.StandardType

variable {F : Type} [Field F] [Finite F] {f : ℕ} [CharP F 2]

theorem PhanEInput2.universalCompletion_E6 (hE : PhanEInput2)
    (hF : Nat.card F = (2 ^ f) ^ 2) (hq : 4 ≤ 2 ^ f)
    (U : Fin 6 → Subgroup (lieUniversal .twistedE6 0 2 f Nat.prime_two).K)
    (W : Fin 6 → Fin 6 → Subgroup (lieUniversal .twistedE6 0 2 f Nat.prime_two).K)
    (hW : WeakPhanSL F 2 f CoxeterMatrix.E₆ U W) :
    IsUniversalCompletion (PhanPresentation.family U) := by
  have hf : 1 ≤ f := Nat.one_le_iff_ne_zero.mpr (fun hf => by simp [hf] at hq)
  have : Finite (lieUniversal .twistedE6 0 2 f Nat.prime_two).K :=
    CFSG.StandardType.LieKnownR2.OddCenter.finite_ggU (t := .twistedE6)
      (by simp) ⟨Nat.prime_two, hf, rfl⟩
  apply PhanPresentation.isUniversalCompletion_of_recognition U hW
  intro X _ V Z hV
  obtain ⟨θ, hθ, -⟩ := (hE F f hF hq).1 V Z hV
  exact ⟨θ, hθ⟩

theorem PhanEInput2.universalCompletion_E7 (hE : PhanEInput2)
    (hF : Nat.card F = (2 ^ f) ^ 2) (hq : 4 ≤ 2 ^ f)
    (U : Fin 7 → Subgroup (lieUniversal .E7 0 2 f Nat.prime_two).K)
    (W : Fin 7 → Fin 7 → Subgroup (lieUniversal .E7 0 2 f Nat.prime_two).K)
    (hW : WeakPhanSL F 2 f CoxeterMatrix.E₇ U W) :
    IsUniversalCompletion (PhanPresentation.family U) := by
  have hf : 1 ≤ f := Nat.one_le_iff_ne_zero.mpr (fun hf => by simp [hf] at hq)
  have : Finite (lieUniversal .E7 0 2 f Nat.prime_two).K :=
    CFSG.StandardType.LieKnownR2.OddCenter.finite_ggU (t := .E7)
      (by simp) ⟨Nat.prime_two, hf, rfl⟩
  apply PhanPresentation.isUniversalCompletion_of_recognition U hW
  intro X _ V Z hV
  obtain ⟨θ, hθ, -⟩ := (hE F f hF hq).2.1 V Z hV
  exact ⟨θ, hθ⟩

theorem PhanEInput2.universalCompletion_E8 (hE : PhanEInput2)
    (hF : Nat.card F = (2 ^ f) ^ 2) (hq : 4 ≤ 2 ^ f)
    (U : Fin 8 → Subgroup (lieUniversal .E8 0 2 f Nat.prime_two).K)
    (W : Fin 8 → Fin 8 → Subgroup (lieUniversal .E8 0 2 f Nat.prime_two).K)
    (hW : WeakPhanSL F 2 f CoxeterMatrix.E₈ U W) :
    IsUniversalCompletion (PhanPresentation.family U) := by
  have hf : 1 ≤ f := Nat.one_le_iff_ne_zero.mpr (fun hf => by simp [hf] at hq)
  have : Finite (lieUniversal .E8 0 2 f Nat.prime_two).K :=
    CFSG.StandardType.LieKnownR2.OddCenter.finite_ggU (t := .E8)
      (by simp) ⟨Nat.prime_two, hf, rfl⟩
  apply PhanPresentation.isUniversalCompletion_of_recognition U hW
  intro X _ V Z hV
  obtain ⟨θ, hθ, -⟩ := (hE F f hF hq).2.2 V Z hV
  exact ⟨θ, hθ⟩

namespace PhanE

theorem PhanEInput2.isUniversal_E6 (hE : PhanEInput2)
    (hF : Nat.card F = (2 ^ f) ^ 2) (hq : 4 ≤ 2 ^ f)
    (S : PhanFamilyE F 2 f (CoxeterMatrix.E₆) (lieUniversal .twistedE6 0 2 f Nat.prime_two).K)
    (hS : S.Good)
    (W : Fin 6 → Fin 6 → Subgroup (lieUniversal .twistedE6 0 2 f Nat.prime_two).K)
    (hW : WeakPhanSL F 2 f (CoxeterMatrix.E₆) (fun i => (S.ι i).range) W) :
    S.IsUniversal := by
  apply PhanFamilyE.Good.isUniversal_of_isUniversalCompletion hF hq hS
  exact hE.universalCompletion_E6 hF hq  (fun i => (S.ι i).range) W hW

theorem PhanEInput2.isUniversal_E7 (hE : PhanEInput2)
    (hF : Nat.card F = (2 ^ f) ^ 2) (hq : 4 ≤ 2 ^ f)
    (S : PhanFamilyE F 2 f (CoxeterMatrix.E₇) (lieUniversal .E7 0 2 f Nat.prime_two).K)
    (hS : S.Good)
    (W : Fin 7 → Fin 7 → Subgroup (lieUniversal .E7 0 2 f Nat.prime_two).K)
    (hW : WeakPhanSL F 2 f (CoxeterMatrix.E₇) (fun i => (S.ι i).range) W) :
    S.IsUniversal := by
  apply PhanFamilyE.Good.isUniversal_of_isUniversalCompletion hF hq hS
  exact hE.universalCompletion_E7 hF hq  (fun i => (S.ι i).range) W hW

theorem PhanEInput2.isUniversal_E8 (hE : PhanEInput2)
    (hF : Nat.card F = (2 ^ f) ^ 2) (hq : 4 ≤ 2 ^ f)
    (S : PhanFamilyE F 2 f (CoxeterMatrix.E₈) (lieUniversal .E8 0 2 f Nat.prime_two).K)
    (hS : S.Good)
    (W : Fin 8 → Fin 8 → Subgroup (lieUniversal .E8 0 2 f Nat.prime_two).K)
    (hW : WeakPhanSL F 2 f (CoxeterMatrix.E₈) (fun i => (S.ι i).range) W) :
    S.IsUniversal := by
  apply PhanFamilyE.Good.isUniversal_of_isUniversalCompletion hF hq hS
  exact hE.universalCompletion_E8 hF hq  (fun i => (S.ι i).range) W hW

end PhanE

end CFSG.ClassicalInvolution.Phan
