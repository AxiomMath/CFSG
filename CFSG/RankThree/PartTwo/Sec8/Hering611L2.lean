module

public import CFSG.RankThree.PartTwo.KFacts.AutPSL2
public import CFSG.CharacterTheory.PSL2Table.Basic
import CFSG.Quasithin.Background.F7TwoInvL2OddUnip
import CFSG.SignalizerFunctorTheorem.CatalogBridge.FixedFieldCard
import CFSG.RankThree.PartTwo.Sec8.Item82OneProofL2

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering611

open CFSG CFSG.GorensteinWalter CFSG.ComponentClassification.CatalogueSchreierLinearTwo

theorem exists_fixed_E27 {F : Type} [Field F] [Finite F] [CharP F 3] (hcard : Nat.card F = 3 ^ 6)
    {τ : MulAut (PSL2 F)} (hτ : (KFacts.stdPinnedPSL2 F).IsField τ) (hτ2 : τ * τ = 1) :
    ∃ Q : Subgroup (PSL2 F), CFSG.Assembly.IsElemAbelian 3 Q ∧ Nat.card Q = 27 ∧
      ∀ x ∈ Q, τ x = x := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨φ, ⟨σ, rfl⟩, hφ1, d, ⟨g, rfl⟩, rfl⟩ := hτ
  set D := pglAction F g with hD
  set Φ := psl2FieldAut F σ with hΦ
  have hΦ2 : Φ * Φ = 1 := by
    calc Φ * Φ = D⁻¹ * (D * Φ * D⁻¹ * (D * Φ * D⁻¹)) * D := by group
      _ = 1 := by rw [hτ2]; group
  have hσ1 : σ ≠ 1 := fun h => hφ1 (by rw [hΦ, h, map_one])
  have hσ2 : σ * σ = 1 :=
    psl2FieldAut_injective F (by rw [map_mul, map_one]; exact hΦ2)
  have hord : orderOf σ = 2 := orderOf_eq_prime (by rw [pow_two]; exact hσ2) hσ1
  obtain ⟨-, hfix⟩ := SignalizerFunctorTheorem.CatalogBridge.card_fixedField_of_orderOf
    (r := 3) (n := 6) (p := 2) Nat.prime_three (by norm_num) hcard σ hord
  set Fix := RingHom.eqLocusField σ.toRingHom (RingHom.id F) with hFix
  have hmem : ∀ s : Fix, σ (s : F) = s := fun s => s.2
  set ιm : Multiplicative Fix →* Multiplicative F :=
    AddMonoidHom.toMultiplicative (Fix.subtype.toAddMonoidHom) with hιm
  set f : Multiplicative Fix →* PSL2 F :=
    (D.toMonoidHom).comp ((psl2UpperUnipotentHom F).comp ιm) with hf
  have hfapp : ∀ y : Multiplicative Fix, f y = D (PSL2Table.mk (PSL2Table.unip
      ((Multiplicative.toAdd y : Fix) : F))) := fun y => rfl
  have hfinj : Function.Injective f := by
    intro y₁ y₂ h
    have h1 : psl2UpperUnipotentHom F (ιm y₁) = psl2UpperUnipotentHom F (ιm y₂) :=
      D.injective h
    have h2 := Item82OneProof.psl2UpperUnipotentHom_injective' h1
    exact Multiplicative.toAdd.injective (Subtype.ext (Multiplicative.toAdd.injective h2))
  refine ⟨f.range, ⟨⟨⟨fun a b => ?_⟩⟩, fun a ha => ?_⟩, ?_, ?_⟩
  · obtain ⟨y₁, hy₁⟩ := a.2
    obtain ⟨y₂, hy₂⟩ := b.2
    apply Subtype.ext
    change (a : PSL2 F) * b = b * a
    rw [← hy₁, ← hy₂, ← map_mul, ← map_mul, mul_comm y₁ y₂]
  · obtain ⟨y, rfl⟩ := ha
    rw [← map_pow]
    have : y ^ 3 = 1 := by
      rw [← ofAdd_toAdd y, ← ofAdd_nsmul, nsmul_eq_mul, Nat.cast_ofNat]
      have h3F : (3 : F) = 0 := by exact_mod_cast CharP.cast_eq_zero F 3
      have h3 : (3 : Fix) = 0 := by
        apply Subtype.ext
        push_cast
        exact h3F
      rw [h3, zero_mul, ofAdd_zero]
    rw [this, map_one]
  · rw [← Nat.card_congr (MonoidHom.ofInjective hfinj).toEquiv,
      Nat.card_congr Multiplicative.toAdd, Nat.card_congr (Equiv.refl _), hfix]
    norm_num
  · rintro _ ⟨y, rfl⟩
    rw [MulAut.mul_apply, MulAut.mul_apply, hfapp, MulAut.inv_apply_self, hΦ,
      Quasithin.F7Two.psl2FieldAut_mk_unip, hmem]

end CFSG.RankThree.PartTwo.Sec8.Hering611
