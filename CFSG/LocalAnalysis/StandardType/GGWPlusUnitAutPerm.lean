module

public import CFSG.LocalAnalysis.StandardType.GGTableBUnitDvdNbr
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitTvRat
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitActCore
public import CFSG.LocalAnalysis.StandardType.GGTypeANbrTableBPermAut

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

namespace UnitTB

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial CFSG.StandardType.LineU

private theorem permSU_eq_one_of_conj_comm_of_pairVec {d n p : ℕ} {K : Type} [Field K] [Finite K]
    {L' : Type} [Group L'] {φ : ↥(unitarySU 2 n K d) →* L'} (hM : Model φ)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ n + 1) (hd : 3 ≤ d)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (hsep : ∀ {τ : Equiv.Perm (Fin d)},
      (∀ k l : Fin d, k ≠ l → ∃ c : K,
        ∀ m, TypeA.ggPairVec k l ζ (τ m) = c * TypeA.ggPairVec k l ζ m) → τ = 1)
    {A : Subgroup (MulAut L')} (hsc : GGTorusSelfCent p A)
    (hdiag : ∀ a ∈ A, ∃ t : Fin d → K, ActsDiagU φ a t) {σ : Equiv.Perm (Fin d)}
    (hσ : ∀ b ∈ A, MulAut.conj (φ (permSU hM.field σ)) * b *
      (MulAut.conj (φ (permSU hM.field σ)))⁻¹ = b) :
    σ = 1 := by
  refine inv_eq_one.mp (hsep (τ := σ.symm) fun k l _ => ?_)
  let t : Fin d → K := TypeA.ggPairVec k l ζ
  let t' : Fin d → K := fun m => t (σ.symm m)
  obtain ⟨h, hhA, hht⟩ := UnitTv.exists_heart hM hp hpq hsc hdiag hζ k l
  have hht_t : ActsDiagU φ h t := hht
  have hCA : σ.permMatrix K * σ⁻¹.permMatrix K = 1 := by
    rw [← coe_permGL_inv_matrix σ, ← coe_permGL_matrix σ, ← Units.val_mul, inv_mul_cancel,
      Units.val_one]
  have hmem : σ⁻¹.permMatrix K * diagonal t = diagonal t' * σ⁻¹.permMatrix K := by
    have h := permMatrix_conj_diag σ t
    change σ⁻¹.permMatrix K * diagonal t * σ.permMatrix K = diagonal t' at h
    calc σ⁻¹.permMatrix K * diagonal t
        = σ⁻¹.permMatrix K * diagonal t * 1 := (mul_one _).symm
      _ = σ⁻¹.permMatrix K * diagonal t * (σ.permMatrix K * σ⁻¹.permMatrix K) := by rw [hCA]
      _ = (σ⁻¹.permMatrix K * diagonal t * σ.permMatrix K) * σ⁻¹.permMatrix K := by group
      _ = diagonal t' * σ⁻¹.permMatrix K := by rw [h]
  have hst : ((permSU hM.field σ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) * diagonal t =
      diagonal t' * ((permSU hM.field σ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) := by
    rw [coe_permSU hM.field σ, coe_permGL_matrix σ]
    exact hmem
  have hact := UnitTv.actsDiagU_conj_elt hht_t (permSU hM.field σ) hst
  have hfix : MulAut.conj (φ (permSU hM.field σ)) * h *
      (MulAut.conj (φ (permSU hM.field σ)))⁻¹ = h := hσ h hhA
  have hht'_t' : ActsDiagU φ h t' := by
    rw [← hfix]
    exact hact
  have hk' : t' k ≠ 0 := hht'_t'.ne_zero k
  refine ⟨t' k * (t k)⁻¹, fun m => ?_⟩
  have hratio := ActsDiagU.ratio_eq hM.field (by omega : 3 ≤ d) hM.ker hht_t hht'_t' m k
  have key : t' m = t m * ((t k)⁻¹ * t' k) := by
    have h2 := congrArg (fun x => x * t' k) hratio
    rw [mul_assoc, mul_assoc, inv_mul_cancel₀ hk', mul_one] at h2
    exact h2.symm
  show t' m = (t' k * (t k)⁻¹) * t m
  calc t' m = t m * ((t k)⁻¹ * t' k) := key
    _ = (t' k * (t k)⁻¹) * t m := by ring

theorem permSU_eq_one_of_conj_comm {d n p : ℕ} {K : Type} [Field K] [Finite K]
    {L' : Type} [Group L'] {φ : ↥(unitarySU 2 n K d) →* L'} (hM : Model φ)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ n + 1) (hd : 4 ≤ d)
    {A : Subgroup (MulAut L')} (hsc : GGTorusSelfCent p A)
    (hdiag : ∀ a ∈ A, ∃ t : Fin d → K, ActsDiagU φ a t) {σ : Equiv.Perm (Fin d)}
    (hσ : ∀ b ∈ A, MulAut.conj (φ (permSU hM.field σ)) * b *
      (MulAut.conj (φ (permSU hM.field σ)))⁻¹ = b) :
    σ = 1 := by
  obtain ⟨ζ, hζ⟩ := CFSG.RankThree.PartOne.KFU.exists_isPrimitiveRoot hM.field hp hpq
  exact permSU_eq_one_of_conj_comm_of_pairVec hM hp hp2 hpq (by omega) hζ
    (TypeANbrDvd.perm_eq_one_of_pairVec hd (hζ.ne_one hp.one_lt)
      (TypeA.ne_inv_of_isPrimitiveRoot hζ hp hp2)) hsc hdiag hσ

theorem permSU_eq_one_of_conj_comm_of_coprime {d n p : ℕ} {K : Type} [Field K] [Finite K]
    {L' : Type} [Group L'] {φ : ↥(unitarySU 2 n K d) →* L'} (hM : Model φ)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ n + 1) (hd : 3 ≤ d) (hcp : Nat.Coprime d p)
    {A : Subgroup (MulAut L')} (hsc : GGTorusSelfCent p A)
    (hdiag : ∀ a ∈ A, ∃ t : Fin d → K, ActsDiagU φ a t) {σ : Equiv.Perm (Fin d)}
    (hσ : ∀ b ∈ A, MulAut.conj (φ (permSU hM.field σ)) * b *
      (MulAut.conj (φ (permSU hM.field σ)))⁻¹ = b) :
    σ = 1 := by
  obtain ⟨ζ, hζ⟩ := CFSG.RankThree.PartOne.KFU.exists_isPrimitiveRoot hM.field hp hpq
  exact permSU_eq_one_of_conj_comm_of_pairVec hM hp hp2 hpq hd hζ
    (TypeANbrDvd.perm_eq_one_of_pairVec_of_coprime hd hcp hζ hp hp2) hsc hdiag hσ

end UnitTB

end CFSG.StandardType
