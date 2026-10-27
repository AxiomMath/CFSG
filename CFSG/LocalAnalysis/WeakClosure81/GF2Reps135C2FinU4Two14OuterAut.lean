module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2FinU4Two14Defs
public import CFSG.LocalAnalysis.RankThreeUC.AGL81U4FFDefs
import CFSG.HardMathSupport.U4FF.Outer
public import CFSG.LocalAnalysis.EvenBN.U4.Model.OuterInvolution

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open scoped Matrix

open CFSG.LocalAnalysis.RankThreeUC
open CFSG.HardMathSupport.U4FF
  (SU4 exists_equiv_gramSU sup_inf_centralizer_eq_bot mem_of_fieldFactor_eq_one)
open CFSG.LocalAnalysis.EvenBN.U4
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut coe_glAut)
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_apply)
open CFSG.LieType.Universal.Unitary (SU conjTr antidiag mem_SU)
open CFSG.Quasithin (IsElemAbelian2)
open CFSG.ClassicalGroups.UnitaryFlag (gramSU mem_gramSU)

theorem finU4_outer_normal_form {S : Type} [CommGroup S] [Finite S] [Fact (∀ s : S, s * s = 1)]
    {L : Subgroup (MulAut S)} (hL : IsU4Group 1 L) (hirr : IsIrrOn L) {σ : MulAut S}
    (hσN : σ ∈ Subgroup.normalizer (L : Set (MulAut S))) (hσ2 : σ * σ = 1) (hσL : σ ∉ L) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2) (_ : Nat.card K = (2 ^ 1) ^ 2)
      (η : ↥L ≃* SU4 K 1) (Z : Matrix (Fin 4) (Fin 4) K) (τ : MulAut S), τ ∈ L ∧
      (Z = 1 ∨ Z = finU4ZMat K) ∧
      ∀ x y : ↥L, (y : MulAut S) = (τ * σ * τ⁻¹) * x * (τ * σ * τ⁻¹)⁻¹ →
        FinU4FrobPair Z (η x) (η y) := by
  classical
  have hS : ∀ s : S, s * s = 1 := Fact.out
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hA : IsElemAbelian2 (Subgroup.zpowers σ) := by
    have hσ2pow : σ ^ 2 = 1 := by simpa [sq] using hσ2
    refine ⟨?_, ?_⟩
    · intro a ha b hb
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp ha
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hb
      calc a * b = σ ^ m * σ ^ n := by rw [← hm, ← hn]
        _ = σ ^ (m + n) := (zpow_add σ m n).symm
        _ = σ ^ (n + m) := by rw [add_comm]
        _ = σ ^ n * σ ^ m := zpow_add σ n m
        _ = b * a := by rw [hm, hn]
    · intro a ha
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp ha
      have h2 : σ ^ (2 : ℤ) = 1 := by
        rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast]
        exact hσ2pow
      rw [← hk, pow_two, ← zpow_add, show k + k = 2 * k by ring, zpow_mul, h2, one_zpow]
  have hAN : Subgroup.zpowers σ ≤ Subgroup.normalizer (L : Set (MulAut S)) :=
    Subgroup.zpowers_le.mpr hσN
  have hirrLA : IsIrrOn (L ⊔ Subgroup.zpowers σ) := fun W hW =>
    hirr W (fun x hx => hW x (Subgroup.mem_sup_left hx))
  obtain ⟨K, hKfield, h, ⟨η⟩⟩ := exists_equiv_gramSU hL
  haveI : Finite K := h.finite
  haveI : CharP K 2 := h.charP
  have hbar : ∀ c : K, h.bar c = unitaryInvolution K 2 1 c := by
    intro c
    rw [CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData.bar_apply, unitaryInvolution_apply]
  have hbar2 : ∀ c : K, miyamotoBarEquiv h c = c ^ 2 := by
    intro c
    rw [miyamotoBarEquiv_apply, CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData.bar_apply]
    rfl
  let xN : Subgroup.normalizer (L : Set (MulAut S)) := ⟨σ, hAN (Subgroup.mem_zpowers σ)⟩
  have hα2 : miyamotoAct h L η xN * miyamotoAct h L η xN = 1 := by
    rw [← map_mul]
    have hxx : xN * xN = 1 := Subtype.ext hσ2
    rw [hxx, map_one]
  have hα1 : miyamotoAct h L η xN ≠ 1 := by
    intro he
    have hcent := (miyamotoAct_eq_one_iff h L η xN).1 he
    have hmem : σ ∈ (L ⊔ Subgroup.zpowers σ) ⊓ Subgroup.centralizer (L : Set (MulAut S)) :=
      ⟨Subgroup.mem_sup_right (Subgroup.mem_zpowers σ), hcent⟩
    rw [sup_inf_centralizer_eq_bot hS hL hA hAN hirrLA, Subgroup.mem_bot] at hmem
    exact hσL (hmem ▸ L.one_mem)
  have hord : orderOf (miyamotoAct h L η xN) = 2 :=
    orderOf_eq_prime (by rw [sq]; exact hα2) hα1
  have hff : miyamotoFieldFactor h (miyamotoAct h L η xN) ≠ 1 := fun he =>
    hσL (mem_of_fieldFactor_eq_one hS hL hA hAN hirrLA h η (Subgroup.mem_zpowers σ) he)
  obtain ⟨t, ht⟩ := exists_conj_eq_u_or_uz1 h hord hff
  set τ : MulAut S := (η.symm t : MulAut S) with hτdef
  have hτ : τ ∈ L := by rw [hτdef]; exact (η.symm t).2
  have hconj : miyamotoAct h L η ⟨η.symm t, Subgroup.le_normalizer (η.symm t).2⟩ =
      MulAut.conj t := by
    have h := miyamotoAct_mem h L η (η.symm t)
    rwa [MulEquiv.apply_symm_apply] at h
  have hmem : τ * σ * τ⁻¹ ∈ Subgroup.normalizer (L : Set (MulAut S)) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.le_normalizer hτ) hσN)
      (Subgroup.inv_mem _ (Subgroup.le_normalizer hτ))
  have hbeta : MulAut.conj t * miyamotoAct h L η xN * (MulAut.conj t)⁻¹ =
      miyamotoAct h L η ⟨τ * σ * τ⁻¹, hmem⟩ := by
    rw [← hconj]
    simp only [← map_mul, ← map_inv]
    rfl
  have hβx : ∀ x y : ↥L, (y : MulAut S) = τ * σ * τ⁻¹ * x * (τ * σ * τ⁻¹)⁻¹ →
      (MulAut.conj t * miyamotoAct h L η xN * (MulAut.conj t)⁻¹) (η x) = η y := by
    intro x y hxy
    rw [hbeta, miyamotoAct_apply_eq]
    exact congrArg η (Subtype.ext hxy.symm)
  have hJ : miyamotoJ4 K = antidiag 4 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [miyamotoJ4, antidiag, Fin.rev]
  have hmap : ∀ M : Matrix (Fin 4) (Fin 4) K,
      M.map h.bar = M.map (unitaryInvolution K 2 1) := by
    intro M
    ext i j
    simp only [Matrix.map_apply]
    exact hbar (M i j)
  have hEq : gramSU h (miyamotoJ4 K) = SU (unitaryInvolution K 2 1) 4 := by
    ext g
    rw [mem_gramSU, mem_SU]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h2, ?_⟩
      change ((g : Matrix (Fin 4) (Fin 4) K).map (unitaryInvolution K 2 1))ᵀ * antidiag 4 *
        (g : Matrix (Fin 4) (Fin 4) K) = antidiag 4
      rw [← hmap (g : Matrix (Fin 4) (Fin 4) K), ← hJ]
      exact h1
    · rintro ⟨h1, h2⟩
      refine ⟨?_, h1⟩
      have h2' : ((g : Matrix (Fin 4) (Fin 4) K).map (unitaryInvolution K 2 1))ᵀ * antidiag 4 *
          (g : Matrix (Fin 4) (Fin 4) K) = antidiag 4 := h2
      rw [← hmap (g : Matrix (Fin 4) (Fin 4) K), ← hJ] at h2'
      exact h2'
  let η' : ↥L ≃* SU4 K 1 := η.trans (MulEquiv.subgroupCongr hEq)
  have hcongr : ∀ z : ↥L, (η' z : GL (Fin 4) K) = (η z : GL (Fin 4) K) := fun z => rfl
  have hmapphi : ∀ M : Matrix (Fin 4) (Fin 4) K,
      M.map (miyamotoBarEquiv h) = M.map (fun c => c ^ 2) := by
    intro M
    ext i j
    simp only [Matrix.map_apply]
    exact hbar2 (M i j)
  have hz1sq : miyamotoXGL h 0 0 0 1 * miyamotoXGL h 0 0 0 1 = 1 := by
    rw [miyamotoXGL_mul_A1 h (b := 0) (c := 0) (d := 1) (b' := 0) (c' := 0) (d' := 1)
      (by simp : h.bar (0 : K) = 0)]
    have h2 : (1 : K) + 1 = 0 := CharTwo.add_self_eq_zero (R := K) 1
    have h0 : (0 : K) + 0 = 0 := add_zero 0
    rw [h2, h0, miyamotoXGL_zero]
  have hz1eq : ((miyamotoZ1S h : gramSU h (miyamotoJ4 K)) : GL (Fin 4) K) =
      miyamotoXGL h 0 0 0 1 := rfl
  have hz1invGL : (((miyamotoZ1S h : gramSU h (miyamotoJ4 K)) : GL (Fin 4) K))⁻¹ =
      ((miyamotoZ1S h : gramSU h (miyamotoJ4 K)) : GL (Fin 4) K) := by
    rw [hz1eq]
    exact inv_eq_of_mul_eq_one_right hz1sq
  have hz1GLmat : (((miyamotoZ1S h : gramSU h (miyamotoJ4 K)) : GL (Fin 4) K) :
      Matrix (Fin 4) (Fin 4) K) = finU4ZMat K := by
    rw [hz1eq, coe_miyamotoXGL]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [miyamotoX, finU4ZMat]
  rcases ht with ht | ht
  ·
    refine ⟨K, hKfield, h.finite, h.charP, ?_, η', 1, τ, hτ, Or.inl rfl, ?_⟩
    · rw [h.card]; norm_num
    · intro x y hxy
      have hηy : η y = miyamotoFieldAut h (miyamotoBarEquiv h) (η x) := by
        rw [← hβx x y hxy, ht]
      have hm : ((η y : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
          ((η x : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map (fun c => c ^ 2) := by
        rw [hηy, coe_miyamotoFieldAut_apply, coe_glAut, hmapphi]
      rw [FinU4FrobPair, hcongr y, hcongr x, one_mul, mul_one]
      exact hm
  ·
    refine ⟨K, hKfield, h.finite, h.charP, ?_, η', finU4ZMat K, τ, hτ, Or.inr rfl, ?_⟩
    · rw [h.card]; norm_num
    · intro x y hxy
      have hηy : η y = (MulAut.conj (miyamotoZ1S h) *
          miyamotoFieldAut h (miyamotoBarEquiv h)) (η x) := by
        rw [← hβx x y hxy, ht]
      have hgl : (η y : GL (Fin 4) K) = (miyamotoZ1S h : GL (Fin 4) K) *
          glAut (miyamotoBarEquiv h) (η x : GL (Fin 4) K) *
            (miyamotoZ1S h : GL (Fin 4) K)⁻¹ := by
        rw [hηy, MulAut.mul_apply, MulAut.conj_apply]
        rfl
      have hm : ((η y : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = finU4ZMat K *
          ((η x : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map (fun c => c ^ 2) *
            finU4ZMat K := by
        rw [hgl, hz1invGL, Units.val_mul, Units.val_mul, hz1GLmat, coe_glAut, hmapphi]
      rw [FinU4FrobPair, hcongr y, hcongr x]
      exact hm

end CFSG.LocalAnalysis.WeakClosure81
