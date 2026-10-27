module

public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54UMaxG2Pair
public import CFSG.GH74.GLS.IVK.Proofs2.GHInvExcShape
import CFSG.GH74.Generic.BProg.B2.GenLocG2OuterShape
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54UMaxG2Count
import CFSG.ClassicalInvolution.Asc77.AscT3CIISl2
import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1S73Sq

public section

namespace CFSG.LocalAnalysis.WeakClosure81.Asch80G2

open Subgroup
open CFSG.Blueprint (LieModel)

open CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab (Shape)
open CFSG.GH74.Generic.BProg.B2.GenLocG2OuterShape (mem_E_or cent_E sq_cases₁ sq_cases₂
  two_ne_zero₁ two_ne_zero₂)

open scoped MatrixGroups

variable {Y : Type} [Group Y]

private theorem g2Frame_map_le_sqCent {K : Type} [Group K] {F : Type} [Field F] [Finite F]
    (hodd : Odd (Nat.card F)) {I : Subgroup K} (e : ↥I ≃* SL(2, F)) {E : Subgroup Y} {z : Y}
    (φ : K →* Y) (hφE : ∀ k, φ k ∈ E) (hcomm : ∀ k ∈ I, φ k * z = z * φ k) :
    I.map φ ≤ sqCent E z := by
  have hle : closure {x : SL(2, F) | ∃ y, y * y = x} ≤
      (sqCent E z).comap (φ.comp (I.subtype.comp e.symm.toMonoidHom)) := by
    rw [closure_le]
    rintro _ ⟨y, rfl⟩
    show φ ((e.symm (y * y) : ↥I) : K) ∈ sqCent E z
    rw [map_mul, Subgroup.coe_mul, map_mul]
    exact sq_mem_sqCent (hφE _) (hcomm _ (e.symm y).2)
  rw [CFSG.ComponentClassification.HarrisLit.T1.closure_mul_self_sl2 hodd] at hle
  rintro _ ⟨a, ha, rfl⟩
  have h : φ ((e.symm (e ⟨a, ha⟩) : ↥I) : K) ∈ sqCent E z := hle (mem_top (e ⟨a, ha⟩))
  rw [MulEquiv.symm_apply_apply] at h
  exact h

private theorem g2Frame_card_sq {K : Type} [Group K] {F : Type} [Field F] [Finite F]
    (h2 : (2 : F) ≠ 0) {I : Subgroup K} (e : ↥I ≃* SL(2, F)) {φ : K →* Y}
    (hφinj : Function.Injective φ) {z₀ : K} (hz₀ : z₀ ∈ I) (he : e ⟨z₀, hz₀⟩ = -1) :
    Nat.card {a : Y // a ∈ I.map φ ∧ a * a = φ z₀} % 4 = 2 := by
  have hz : φ z₀ ∈ I.map φ := mem_map_of_mem φ hz₀
  rw [card_sq_eq_of_equiv_sl2 ((I.equivMapOfInjective φ hφinj).symm.trans e) hz ?_]
  · exact card_sl2_sq_eq_neg_one_mod_four h2
  · rw [MulEquiv.trans_apply, ← he]
    congr 1
    apply (I.equivMapOfInjective φ hφinj).injective
    rw [MulEquiv.apply_symm_apply]
    apply Subtype.ext
    rw [Subgroup.coe_equivMapOfInjective_apply]

theorem sl2Pair_of_shape {K : Type} [Group K] {F₁ F₂ : Type} [Field F₁] [Field F₂] [Finite F₁]
    [Finite F₂] (hodd₁ : Odd (Nat.card F₁)) (hodd₂ : Odd (Nat.card F₂)) (S : Shape K F₁ F₂)
    {E : Subgroup Y} {z : Y} (φ : K →* Y) (hφinj : Function.Injective φ) (hφz : φ S.z = z)
    (hφE : ∀ k, φ k ∈ E) (hφC : ∀ g ∈ E, g * z = z * g → ∃ k, φ k = g) :
    SL2Pair E z (S.I₁.map φ) (S.I₂.map φ) := by
  have hcomm₁ : ∀ k ∈ S.I₁, φ k * z = z * φ k := fun k hk => by
    rw [← hφz, ← map_mul, ← map_mul, S.comm k hk S.z S.z_mem₂]
  have hcomm₂ : ∀ k ∈ S.I₂, φ k * z = z * φ k := fun k hk => by
    rw [← hφz, ← map_mul, ← map_mul, S.comm S.z S.z_mem₁ k hk]
  have hsqk : ∀ k : K, k * k ∈ S.I₁ ⊔ S.I₂ := by
    intro k
    have := S.normal₁
    have := S.normal₂
    rcases mem_E_or S k with h | h
    · exact mul_mem h h
    · have h2 := (Subgroup.sup_normal S.I₁ S.I₂).conj_mem _ h S.t⁻¹
      have e : k * k = k * S.t * (S.t⁻¹ * (k * S.t) * S.t⁻¹⁻¹) * (S.t * S.t)⁻¹ := by group
      rw [e, S.t_sq, inv_one, mul_one]
      exact mul_mem h h2
  have hsq : sqCent E z = (S.I₁ ⊔ S.I₂).map φ := by
    apply le_antisymm
    · refine (closure_le _).2 ?_
      rintro _ ⟨g, hgE, hgz, rfl⟩
      obtain ⟨k, rfl⟩ := hφC g hgE hgz
      rw [SetLike.mem_coe, ← map_mul]
      exact mem_map_of_mem φ (hsqk k)
    · rw [Subgroup.map_sup]
      exact sup_le (g2Frame_map_le_sqCent hodd₁ S.e₁ φ hφE hcomm₁)
        (g2Frame_map_le_sqCent hodd₂ S.e₂ φ hφE hcomm₂)
  have hcommJ : ∀ a ∈ S.I₁.map φ, ∀ b ∈ S.I₂.map φ, a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, S.comm a ha b hb]
  have hinter : S.I₁.map φ ⊓ S.I₂.map φ = zpowers z := by
    rw [← Subgroup.map_inf_eq _ _ φ hφinj, S.inter, MonoidHom.map_zpowers, hφz]
  have hinv₁ : ∀ a ∈ S.I₁.map φ, a * a = 1 → a ∈ zpowers z := by
    rintro _ ⟨a, ha, rfl⟩ h1
    have haa : a * a = 1 := hφinj (by rw [map_mul, h1, map_one])
    rw [← hφz, ← MonoidHom.map_zpowers]
    exact mem_map_of_mem φ (sq_cases₁ S ha haa)
  have hinv₂ : ∀ b ∈ S.I₂.map φ, b * b = 1 → b ∈ zpowers z := by
    rintro _ ⟨b, hb, rfl⟩ h1
    have hbb : b * b = 1 := hφinj (by rw [map_mul, h1, map_one])
    rw [← hφz, ← MonoidHom.map_zpowers]
    exact mem_map_of_mem φ (sq_cases₂ S hb hbb)
  have hconj₁ : ∀ a ∈ S.I₁.map φ, ∀ a' ∈ S.I₁.map φ, a * a = z → a' * a' = z →
      ∃ c ∈ S.I₁.map φ, c * a * c⁻¹ = a' := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨a', ha', rfl⟩ h1 h1'
    have haa : a * a = S.z := hφinj (by rw [map_mul, h1, hφz])
    have haa' : a' * a' = S.z := hφinj (by rw [map_mul, h1', hφz])
    obtain ⟨c, hc⟩ := CFSG.ClassicalInvolution.Asc77.T3CII.exists_conj_of_sq_eq_of_equiv_sl2
      hodd₁ S.e₁ S.e₁_z (k := ⟨a, ha⟩) (h := ⟨a', ha'⟩) (Subtype.ext haa) (Subtype.ext haa')
    refine ⟨φ c, mem_map_of_mem φ c.2, ?_⟩
    rw [← map_inv, ← map_mul, ← map_mul]
    exact congrArg (fun x : ↥S.I₁ => φ (x : K)) hc
  have hcard₁ : Nat.card {a : Y // a ∈ S.I₁.map φ ∧ a * a = z} % 4 = 2 := by
    rw [← hφz]
    exact g2Frame_card_sq (two_ne_zero₁ S) S.e₁ hφinj S.z_mem₁ S.e₁_z
  have hcard₂ : Nat.card {b : Y // b ∈ S.I₂.map φ ∧ b * b = z} % 4 = 2 := by
    rw [← hφz]
    exact g2Frame_card_sq (two_ne_zero₂ S) S.e₂ hφinj S.z_mem₂ S.e₂_z
  have hcent : ∀ w ∈ E, w * z = z * w → (∀ x ∈ sqCent E z, w * x = x * w) → w ∈ zpowers z := by
    intro w hwE hwz hw
    obtain ⟨k, rfl⟩ := hφC w hwE hwz
    have hk : ∀ x ∈ S.I₁ ⊔ S.I₂, k * x = x * k := by
      intro x hx
      apply hφinj
      rw [map_mul, map_mul]
      exact hw (φ x) (by rw [hsq]; exact mem_map_of_mem φ hx)
    rw [← hφz, ← MonoidHom.map_zpowers]
    exact mem_map_of_mem φ (cent_E S hk)
  exact ⟨by rw [← hφz, ← map_mul, S.z_sq, map_one],
    fun h => S.z_ne (hφinj (by rw [hφz, h, map_one])), hcommJ, hinter,
    by rw [hsq, Subgroup.map_sup], hinv₁, hinv₂, hconj₁, hcard₁, hcard₂, hcent⟩

theorem exists_sl2Pair {E : Subgroup Y} {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hE : LieModel ↥E .G2 0 p f) {z : Y} (hzE : z ∈ E) (hz2 : z * z = 1) (hz1 : z ≠ 1) :
    ∃ J₁ J₂ : Subgroup Y, SL2Pair E z J₁ J₂ := by
  have hoz : orderOf (⟨z, hzE⟩ : ↥E) = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine orderOf_eq_prime ?_ ?_
    · rw [pow_two]
      exact Subtype.ext hz2
    · intro h
      exact hz1 (congrArg Subtype.val h)
  obtain ⟨F, _, _, S, hcard, hSz⟩ := CFSG.GH74.GLS.IVK.GHInv.exists_shape_G2 hp hp2 hE _ hoz
  have hodd : Odd (Nat.card F) := by
    rw [hcard]
    exact (hp.odd_of_ne_two hp2).pow
  refine ⟨_, _, sl2Pair_of_shape hodd hodd S
    (E.subtype.comp (centralizer ({(⟨z, hzE⟩ : ↥E)} : Set ↥E)).subtype)
    (E.subtype_injective.comp (Subgroup.subtype_injective _)) (congrArg Subtype.val hSz)
    (fun k => (k : ↥E).2) ?_⟩
  intro g hgE hgz
  refine ⟨⟨⟨g, hgE⟩, ?_⟩, rfl⟩
  rw [mem_centralizer_singleton_iff]
  exact Subtype.ext hgz

end CFSG.LocalAnalysis.WeakClosure81.Asch80G2

end
