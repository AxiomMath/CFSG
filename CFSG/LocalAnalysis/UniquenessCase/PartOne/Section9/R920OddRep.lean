module

public import CFSG.CharacterTheory.PSL2Table.Basic
import CFSG.GroupTheory.CoprimeCentralizerTransport
import CFSG.GroupTheory.SteinbergBKLinearFixedVector
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddInv
import CFSG.LocalAnalysis.UniquenessCase.UC6Mod
public import Mathlib.RepresentationTheory.Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9

open Subgroup
open scoped MatrixGroups

theorem apply_eq_neg_of_mk_eq {Γ k V : Type*} {F : Type} [Group Γ] [CommRing k]
    [AddCommGroup V] [Module k V] [Field F] (ρ : Representation k Γ V)
    (hirr : ∀ U : Submodule k V, (∀ g : Γ, ∀ v ∈ U, ρ g v ∈ U) → U = ⊥ ∨ U = ⊤)
    (e : Γ ⧸ ρ.ker ≃* SL(2, F)) (h2 : (2 : F) ≠ 0) {t : Γ}
    (ht : (t : Γ ⧸ ρ.ker) = e.symm (-1)) : (∀ v, ρ t v = -v) ∧ ρ t ≠ 1 := by
  have hρ : ∀ a b : Γ, (a : Γ ⧸ ρ.ker) = b → ρ a = ρ b := fun a b h => by
    have h1 := MonoidHom.mem_ker.mp (QuotientGroup.eq.mp h)
    rw [← mul_inv_cancel_left a b, map_mul, h1, mul_one]
  have hz : ∀ y : Γ ⧸ ρ.ker, e.symm (-1) * y = y * e.symm (-1) := fun y => e.injective (by
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact (Subgroup.mem_center_iff.mp CFSG.PSL2Table.neg_one_mem_center (e y)).symm)
  have hne : ρ t ≠ 1 := fun h => CFSG.PSL2Table.neg_one_ne_one_SL h2 (by
    have h1 : (t : Γ ⧸ ρ.ker) = 1 := (QuotientGroup.eq_one_iff t).mpr (MonoidHom.mem_ker.mpr h)
    rw [ht] at h1
    simpa using congrArg e h1)
  refine ⟨apply_eq_neg_of_mul_self ρ hirr (fun g => hρ _ _ ?_)
    ((hρ (t * t) 1 ?_).trans (map_one ρ)) hne, hne⟩
  · rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, ht, hz]
  · rw [QuotientGroup.mk_mul, ht, ← map_mul, neg_mul_neg, mul_one, map_one, QuotientGroup.mk_one]

theorem ne_two_of_apply_eq_neg {Γ V : Type*} [Group Γ] {p : ℕ} [AddCommGroup V]
    [Module (ZMod p) V] (ρ : Representation (ZMod p) Γ V) {t : Γ} (ht : ∀ v, ρ t v = -v)
    (hne : ρ t ≠ 1) : p ≠ 2 := by
  rintro rfl
  exact hne (LinearMap.ext fun v => by rw [ht, ZModModule.neg_eq_self, Module.End.one_apply])

theorem exists_commute_of_apply_eq_neg {Γ k V : Type*} [Group Γ] [Finite Γ] [CommRing k]
    [AddCommGroup V] [Module k V] (ρ : Representation k Γ V) (hker : IsPGroup 2 ρ.ker)
    {x t₀ : Γ} (hx : (orderOf x).Prime) (hx2 : orderOf x ≠ 2) (ht₀ : ∀ v, ρ t₀ v = -v) :
    ∃ t : Γ, x * t = t * x ∧ ∀ v, ρ t v = -v := by
  haveI : Fact (orderOf x).Prime := ⟨hx⟩
  have hct : ∀ y : Γ, ρ (y * t₀) = ρ (t₀ * y) := fun y => LinearMap.ext fun v => by
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, ht₀, ht₀, map_neg]
  have hk : ¬ orderOf x ∣ Nat.card ρ.ker := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hker
    rw [hn]
    exact fun h => hx2 ((Nat.prime_dvd_prime_iff_eq hx Nat.prime_two).mp (hx.dvd_of_dvd_pow h))
  obtain ⟨t, ht, htx⟩ := UC6.exists_fixed_in_coset_uc6 (p := orderOf x) (zpowers x) ρ.ker
    (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, pow_one])) hk
    (fun y _ f hf => (MonoidHom.normal_ker ρ).conj_mem f hf y) t₀ (fun y _ => by
      rw [MonoidHom.mem_ker, show t₀⁻¹ * (y * t₀ * y⁻¹) = t₀⁻¹ * (y * t₀) * y⁻¹ by group,
        map_mul, map_mul, hct, ← map_mul, ← map_mul, inv_mul_cancel_left, mul_inv_cancel,
        map_one])
  have hρt : ρ t = ρ t₀ := by
    rw [← mul_inv_cancel_left t₀ t, map_mul, MonoidHom.mem_ker.mp ht, mul_one]
  exact ⟨t, mul_inv_eq_iff_eq_mul.mp (htx x (mem_zpowers x)), fun v => by rw [hρt, ht₀]⟩

theorem exists_sl2_rep_of_quot {Γ k V : Type*} {F : Type} [Group Γ] [Finite Γ] [CommRing k]
    [AddCommGroup V] [Module k V] [Field F] (ρ : Representation k Γ V)
    (hker : IsPGroup 2 ρ.ker) (e : Γ ⧸ ρ.ker ≃* SL(2, F)) {t₀ : Γ}
    (ht₀ : (t₀ : Γ ⧸ ρ.ker) = e.symm (-1)) (hneg : ∀ v, ρ t₀ v = -v)
    (hfpf : ∀ x t : Γ, (orderOf x).Prime → orderOf x ≠ 2 → x * t = t * x →
      (∀ v, ρ t v = -v) → ∀ v, ρ x v = v → v = 0) :
    ∃ σ : Representation k SL(2, F) V, Function.Injective σ ∧ (∀ v, σ (-1) v = -v) ∧
      ∀ g : SL(2, F), (orderOf g).Prime → orderOf g ≠ 2 → ∀ v, σ g v = v → v = 0 := by
  let σ : Representation k SL(2, F) V :=
    (CFSG.Theory.Representation.kerRepresentation ρ).comp e.symm.toMonoidHom
  have hσ : ∀ x : Γ, σ (e (x : Γ ⧸ ρ.ker)) = ρ x := fun x => by
    show CFSG.Theory.Representation.kerRepresentation ρ (e.symm (e x)) = ρ x
    rw [MulEquiv.symm_apply_apply]
    rfl
  refine ⟨σ, (CFSG.Theory.Representation.kerRepresentation_faithful ρ).comp e.symm.injective,
    fun v => ?_, fun g hg hg2 v hv => ?_⟩
  · rw [show σ (-1) = ρ t₀ by rw [← hσ, ht₀, MulEquiv.apply_symm_apply]]
    exact hneg v
  · haveI : Fact (orderOf g).Prime := ⟨hg⟩
    have hgk : ¬ orderOf g ∣ Nat.card ρ.ker := by
      obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hker
      rw [hn]
      exact fun h => hg2 ((Nat.prime_dvd_prime_iff_eq hg Nat.prime_two).mp (hg.dvd_of_dvd_pow h))
    obtain ⟨x, hx, hxg⟩ := CFSG.GroupTheory.CoprimeTransport.exists_orderOf_eq_prime_mk_eq hgk
      (MulEquiv.orderOf_eq e.symm g)
    have hxg' : (x : Γ ⧸ ρ.ker) = e.symm g := hxg
    have hxp : (orderOf x).Prime := by rw [hx]; exact hg
    have hx2 : orderOf x ≠ 2 := by rw [hx]; exact hg2
    obtain ⟨t, hxt, ht⟩ := exists_commute_of_apply_eq_neg ρ hker hxp hx2 hneg
    refine hfpf x t hxp hx2 hxt ht v ?_
    rwa [← hσ x, hxg', MulEquiv.apply_symm_apply]

theorem unip_one_ne_one {F : Type} [Field F] : CFSG.PSL2Table.unip (1 : F) ≠ 1 := fun h => by
  have h1 := congrArg (fun A : SL(2, F) => (A : Matrix (Fin 2) (Fin 2) F) 0 1) h
  simp at h1

theorem ne_card_of_fpf {V : Type*} {F : Type} [Field F] [Fintype F] {p : ℕ} [Fact p.Prime]
    [AddCommGroup V] [Module (ZMod p) V] [Finite V] [Nontrivial V]
    (σ : Representation (ZMod p) SL(2, F) V) (hF : (Fintype.card F).Prime)
    (hF2 : Fintype.card F ≠ 2)
    (hfpf : ∀ g : SL(2, F), (orderOf g).Prime → orderOf g ≠ 2 → ∀ v, σ g v = v → v = 0) :
    p ≠ Fintype.card F := by
  intro hpq
  haveI : Fact (Fintype.card F).Prime := ⟨hF⟩
  haveI : CharP F (Fintype.card F) := charP_of_card_eq_prime rfl
  haveI : FiniteDimensional (ZMod p) V := Module.Finite.of_finite
  have hpow : ∀ n : ℕ, CFSG.PSL2Table.unip (1 : F) ^ n = CFSG.PSL2Table.unip (n : F) := by
    intro n
    induction n with
    | zero => rw [pow_zero, Nat.cast_zero, CFSG.PSL2Table.unip_zero]
    | succ n ih => rw [pow_succ, ih, Nat.cast_succ, CFSG.PSL2Table.unip_add]
  have hu : orderOf (CFSG.PSL2Table.unip (1 : F)) = Fintype.card F := by
    refine orderOf_eq_prime ?_ (unip_one_ne_one (F := F))
    rw [hpow, CharP.cast_eq_zero, CFSG.PSL2Table.unip_zero]
  have hP : IsPGroup p (CFSG.PSL2Table.unipSL F) :=
    IsPGroup.of_card (n := 1) (by rw [CFSG.PSL2Table.card_unipSL, pow_one, hpq])
  obtain ⟨v, hv0, hv⟩ := CFSG.GroupTheory.SteinbergBK.p_group_linear_fixed_vector hP
    (σ.asGroupHom.comp (CFSG.PSL2Table.unipSL F).subtype)
  refine hv0 (hfpf _ (by rw [hu]; exact hF) (by rw [hu]; exact hF2) v ?_)
  have h := hv ⟨_, CFSG.PSL2Table.unip_mem_unipSL 1⟩
  rwa [MonoidHom.comp_apply, Representation.asGroupHom_apply] at h

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9
