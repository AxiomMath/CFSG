module

import CFSG.RankThree.PartOne.S10.PlaneSemidirect
import CFSG.RankThree.PartOne.S9.Extraction.FrattiniAction
import CFSG.RankThree.GroupTheory.SteinbergCEPlaneNormalizerCentralizes
public import CFSG.Assembly.Defs
public import CFSG.LocalAnalysis.ComponentInitial.CoprimeCommutatorFactorization

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement IsMulCommutative

namespace PlaneFrattini

theorem eq_one_of_pow_eq_one {G : Type*} [Group G] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {g : G}
    {m k : ℕ} (hm : g ^ p ^ m = 1) (hk : g ^ 2 ^ k = 1) : g = 1 :=
  orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes
    (Nat.Coprime.pow _ _ ((Nat.coprime_primes hp Nat.prime_two).mpr hp2))
    (orderOf_dvd_of_pow_eq_one hm) (orderOf_dvd_of_pow_eq_one hk))

variable {p : ℕ} {B S D : Type} [Group B] [Group S] [Group D] [Finite D] [MulDistribMulAction B S]

theorem acts_trivially_of_small_frattini (hp : p.Prime) (hp3 : 3 < p) (hBp : IsPGroup p B)
    (hS : IsPGroup 2 S) (hDp : IsPGroup p D) (hV : Nat.card (D ⧸ frattini D) ≤ p ^ 2)
    (hSc : actionCommutator B (⊤ : Subgroup S) = ⊤)
    (β : (S ⋊[MulDistribMulAction.toMulAut B S] B) →* MulAut D) (y : S) :
    β (SemidirectProduct.inl y) = 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp2 : p ≠ 2 := by omega
  obtain ⟨-, -, -, hel, -⟩ := CFSG.GroupTheory.frattini_elementary_quotient hDp
  have := hel
  have hVfin : Finite (Additive (D ⧸ frattini D)) := inferInstanceAs (Finite (D ⧸ frattini D))
  have : FiniteDimensional (ZMod p) (Additive (D ⧸ frattini D)) := Module.Finite.of_finite
  have hdim : Module.finrank (ZMod p) (Additive (D ⧸ frattini D)) ≤ 2 := by
    have : Fintype (Additive (D ⧸ frattini D)) := Fintype.ofFinite _
    have h := Module.card_eq_pow_finrank (K := ZMod p) (V := Additive (D ⧸ frattini D))
    rw [ZMod.card, ← Nat.card_eq_fintype_card] at h
    have h2 : p ^ Module.finrank (ZMod p) (Additive (D ⧸ frattini D)) ≤ p ^ 2 := by
      rw [← h]
      exact hV
    exact (Nat.pow_le_pow_iff_right hp.one_lt).mp h2
  let ρ₀ : (S ⋊[MulDistribMulAction.toMulAut B S] B) →* MulAut (D ⧸ frattini D) :=
    (CFSG.OrderReductions.FrattiniAutomorphisms.quotientAutomorphism (frattini D)).comp β
  let ρ := (Extract.actionGL p (MulAut (D ⧸ frattini D)) (D ⧸ frattini D)).comp ρ₀
  have hconj : ∀ (b : B) (s : S), ρ (SemidirectProduct.inr b) * ρ (SemidirectProduct.inl s) *
      (ρ (SemidirectProduct.inr b))⁻¹ = ρ (SemidirectProduct.inl (b • s)) := by
    intro b s
    rw [← map_inv, ← map_mul, ← map_mul, PlaneSemidirect.conj_inr_inl]
  have hP : IsPGroup p (ρ.comp SemidirectProduct.inr).range :=
    hBp.of_surjective (ρ.comp SemidirectProduct.inr).rangeRestrict
      (ρ.comp SemidirectProduct.inr).rangeRestrict_surjective
  have hT : IsPGroup 2 (ρ.comp SemidirectProduct.inl).range :=
    hS.of_surjective (ρ.comp SemidirectProduct.inl).rangeRestrict
      (ρ.comp SemidirectProduct.inl).rangeRestrict_surjective
  have hPT : (ρ.comp SemidirectProduct.inr).range ≤
      Subgroup.normalizer ((ρ.comp SemidirectProduct.inl).range : Set _) := by
    rintro _ ⟨b, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨s, rfl⟩
      exact ⟨b • s, (hconj b s).symm⟩
    · rintro ⟨s, hs⟩
      refine ⟨b⁻¹ • s, ?_⟩
      have h1 := hconj b⁻¹ s
      simp only [map_inv] at h1
      change ρ (SemidirectProduct.inl (b⁻¹ • s)) = x
      rw [← h1]
      have h2 : ρ (SemidirectProduct.inl s) = ρ (SemidirectProduct.inr b) * x *
          (ρ (SemidirectProduct.inr b))⁻¹ := hs
      rw [h2]
      group
  have hcomm :=
    CFSG.RankThree.GroupTheory.defining_prime_linear_plane_normalizer_centralizes_two_subgroup
      hp3 (Nat.card_zmod p) hdim hP hT hPT
  have hcom : ∀ (b : B) (s : S), ρ (SemidirectProduct.inl s) * ρ (SemidirectProduct.inr b) =
      ρ (SemidirectProduct.inr b) * ρ (SemidirectProduct.inl s) := fun b s =>
    Subgroup.mem_centralizer_iff.mp (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
      ⟨b, rfl⟩) (ρ (SemidirectProduct.inl s)) ⟨s, rfl⟩
  have hker : actionCommutator B (⊤ : Subgroup S) ≤ (ρ.comp SemidirectProduct.inl).ker := by
    unfold actionCommutator
    rw [Subgroup.closure_le]
    rintro x ⟨h, -, b, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker, MonoidHom.comp_apply]
    have e : ρ (SemidirectProduct.inl (h⁻¹ * (b • h))) =
        (ρ (SemidirectProduct.inl h))⁻¹ * ρ (SemidirectProduct.inl (b • h)) := by
      simp only [map_mul, map_inv]
    rw [e, ← hconj b h, ← hcom b h]
    group
  have hρ1 : ρ (SemidirectProduct.inl y) = 1 := by
    have hy : y ∈ actionCommutator B (⊤ : Subgroup S) := by
      rw [hSc]
      exact Subgroup.mem_top y
    exact hker hy
  have hσ : CFSG.OrderReductions.FrattiniAutomorphisms.quotientAutomorphism (frattini D)
      (β (SemidirectProduct.inl y)) = 1 := by
    refine MulEquiv.ext fun v => ?_
    have h1 := congrArg (fun g : LinearMap.GeneralLinearGroup (ZMod p)
      (Additive (D ⧸ frattini D)) => (g : Additive (D ⧸ frattini D) →ₗ[ZMod p]
        Additive (D ⧸ frattini D)) (Additive.ofMul v)) hρ1
    exact Additive.ofMul.injective h1
  obtain ⟨m, hm⟩ := (CFSG.GroupTheory.frattini_automorphism_kernel hDp).2
    ⟨β (SemidirectProduct.inl y), MonoidHom.mem_ker.mpr hσ⟩
  have hσm : β (SemidirectProduct.inl y) ^ p ^ m = 1 := congrArg Subtype.val hm
  obtain ⟨k, hk⟩ := hS y
  have hσk : β (SemidirectProduct.inl y) ^ 2 ^ k = 1 := by
    rw [← map_pow, ← map_pow, hk, map_one, map_one]
  exact eq_one_of_pow_eq_one hp hp2 hσm hσk

end PlaneFrattini

end CFSG.RankThree.PartOne
