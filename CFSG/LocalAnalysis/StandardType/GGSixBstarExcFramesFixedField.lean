module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesHalfCore
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesSplit
public import CFSG.LieType.SeitzGeneration.ExcTorusSylow
public import CFSG.LieType.SeitzGeneration.Lift
public import CFSG.LieType.SeitzGeneration.RegimesExcFamilies

public section

namespace CFSG.StandardType

namespace ExcFrames

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration CFSG.Open
  CFSG.StandardType.ExcFramesHalf

section Field

variable {K : Type*} [Field K] [Finite K] {p : ℕ} [Fact p.Prime]

theorem card_modEq_card_fixed (σ : K ≃+* K) (hσ : σ ^ p = 1) :
    Nat.card K ≡ Nat.card {x : K // σ x = x} [MOD p] := by
  classical
  set π : Equiv.Perm K := σ.toEquiv with hπ
  have hpow : ∀ n : ℕ, ∀ x, (π ^ n) x = (σ ^ n) x := by
    intro n
    induction n with
    | zero => intro x; rfl
    | succ n ih =>
      intro x
      rw [pow_succ, pow_succ, Equiv.Perm.mul_apply, RingAut.mul_apply, ih]
      rfl
  have hπp : π ^ p = 1 := by
    ext x
    rw [hpow, hσ]
    rfl
  have hG : IsPGroup p (Subgroup.zpowers π) := by
    intro g
    refine ⟨1, ?_⟩
    obtain ⟨i, hi⟩ := g.2
    apply Subtype.ext
    rw [pow_one, Subgroup.coe_pow, ← hi, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
      zpow_natCast, hπp, one_zpow]
    rfl
  have h := hG.card_modEq_card_fixedPoints K
  have hfix : Nat.card (MulAction.fixedPoints (Subgroup.zpowers π) K) =
      Nat.card {x : K // σ x = x} := by
    refine Nat.card_congr (Equiv.subtypeEquivRight fun x => ?_)
    rw [MulAction.mem_fixedPoints]
    constructor
    · intro hx
      exact hx ⟨π, Subgroup.mem_zpowers π⟩
    · intro hx m
      obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 m.2
      have hxπ : π x = x := hx
      change (m : Equiv.Perm K) x = x
      rw [← hi]
      exact Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self hxπ i
  rw [hfix] at h
  exact h

theorem exists_subfield_fixed_card_modEq (σ : K ≃+* K) (hσ : σ ^ p = 1) :
    ∃ S : Subfield K, (∀ x ∈ S, σ x = x) ∧
      ((Nat.card S : ℕ) : ZMod p) = ((Nat.card K : ℕ) : ZMod p) := by
  refine ⟨RingHom.eqLocusField σ.toRingHom (RingHom.id K), fun x hx => hx, ?_⟩
  have h := card_modEq_card_fixed σ hσ
  have hS : Nat.card (RingHom.eqLocusField σ.toRingHom (RingHom.id K)) =
      Nat.card {x : K // σ x = x} := rfl
  rw [hS]
  exact ((ZMod.natCast_eq_natCast_iff _ _ p).2 h).symm

end Field

section Base

variable {τ : Tag} {K : Type} [Field K] [Finite K] {p m : ℕ} [Fact p.Prime]

theorem units_map_entrywise_baseChangeGL {K₀ : Type} [Field K₀] (ι : K₀ →+* K) (σ : K ≃+* K)
    (hσ : ∀ x, σ (ι x) = ι x) (g : ModGL τ K₀) :
    Units.map (entrywiseHom σ.toRingHom) (baseChangeGL ι g) = baseChangeGL ι g := by
  have h1 : Units.map (entrywiseHom σ.toRingHom) (baseChangeGL ι g) =
      baseChangeGL σ.toRingHom (baseChangeGL ι g) := Units.ext rfl
  have hcomp : σ.toRingHom.comp ι = ι := RingHom.ext hσ
  rw [h1, baseChangeGL_baseChangeGL, hcomp]

theorem exists_fixedElemAbelian (σ : K ≃+* K) (hσ : σ ^ p = 1)
    (hdata : ∀ (K₀ : Type) [Field K₀] [Finite K₀],
      ((Nat.card K₀ : ℕ) : ZMod p) = ((Nat.card K : ℕ) : ZMod p) →
        SylowTorus (adjointGroup τ K₀) p m) :
    ∃ E : Subgroup (adjointGroup τ K), IsElemAbelian p E ∧ Nat.card E = p ^ m ∧
      ∀ e ∈ E, Units.map (entrywiseHom σ.toRingHom) (e : ModGL τ K) = (e : ModGL τ K) := by
  obtain ⟨S, hS, hSc⟩ := exists_subfield_fixed_card_modEq σ hσ
  obtain ⟨E₀, hE₀, hE₀c⟩ := (hdata S hSc).exists_elemAbelian
  refine ⟨E₀.map (adjBaseChange (τ := τ) S.subtype), isElemAbelian_map_frame _ hE₀, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective (adjBaseChange_injective _), hE₀c]
  · rintro _ ⟨e₀, -, rfl⟩
    rw [coe_adjBaseChange]
    exact units_map_entrywise_baseChangeGL S.subtype σ (fun x => hS x.1 x.2) _

end Base

end ExcFrames

end CFSG.StandardType
