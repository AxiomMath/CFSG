
module

public import CFSG.Dihedral.DisconnectedInvolutionGraph.QuaternionCoordinateHom
public import CFSG.GH74.E2.Basic

@[expose] public section

open CFSG
open CFSG.GH74
open CFSG.GH74.E2
open Subgroup

namespace CertificateChecks.Batch5014

def q8Ext (x y : QuaternionGroup 2) : QuaternionGroup 2 → QuaternionGroup 2
  | .a k => x ^ k.val
  | .xa k => y * x ^ k.val

def q8GenPairs : Finset (QuaternionGroup 2 × QuaternionGroup 2) :=
  Finset.univ.filter (fun p => p.1 * p.1 = QuaternionGroup.a 2 ∧ p.2 * p.2 = QuaternionGroup.a 2 ∧
    p.2 * p.1 = p.1 * p.2 * QuaternionGroup.a 2)

theorem card_q8GenPairs : q8GenPairs.card = 24 := by decide +kernel

theorem q8Ext_mul : ∀ p ∈ q8GenPairs, ∀ u v : QuaternionGroup 2,
    q8Ext p.1 p.2 (u * v) = q8Ext p.1 p.2 u * q8Ext p.1 p.2 v := by decide +kernel

theorem q8Ext_inj : ∀ p ∈ q8GenPairs, ∀ u v : QuaternionGroup 2,
    q8Ext p.1 p.2 u = q8Ext p.1 p.2 v → u = v := by decide +kernel

theorem card_mulAut_q8_le' : Nat.card (MulAut (QuaternionGroup 2)) ≤ 24 := by
  have hz : ∀ ρ : MulAut (QuaternionGroup 2), ρ (QuaternionGroup.a 2) = QuaternionGroup.a 2 := by
    intro ρ
    have h1 : ρ (QuaternionGroup.a 2) * ρ (QuaternionGroup.a 2) = 1 := by
      rw [← map_mul]
      have : (QuaternionGroup.a 2 : QuaternionGroup 2) * QuaternionGroup.a 2 = 1 := by decide
      rw [this, map_one]
    have h2 : ρ (QuaternionGroup.a 2) ≠ 1 := by
      intro h
      have := ρ.injective (h.trans (map_one ρ).symm)
      revert this; decide
    revert h1 h2
    generalize ρ (QuaternionGroup.a 2) = w
    revert w; decide
  let f : MulAut (QuaternionGroup 2) → ↥q8GenPairs := fun ρ =>
    ⟨(ρ (QuaternionGroup.a 1), ρ (QuaternionGroup.xa 0)), by
      simp only [q8GenPairs, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨?_, ?_, ?_⟩
      · rw [← map_mul]
        have : (QuaternionGroup.a 1 : QuaternionGroup 2) * QuaternionGroup.a 1 =
            QuaternionGroup.a 2 := by decide
        rw [this, hz]
      · rw [← map_mul]
        have : (QuaternionGroup.xa 0 : QuaternionGroup 2) * QuaternionGroup.xa 0 =
            QuaternionGroup.a 2 := by decide
        rw [this, hz]
      · rw [← map_mul, ← map_mul, ← hz ρ, ← map_mul]
        congr 1⟩
  have hf : Function.Injective f := by
    intro ρ₁ ρ₂ h
    have h1 : ρ₁ (QuaternionGroup.a 1) = ρ₂ (QuaternionGroup.a 1) := congrArg (fun x => x.1.1) h
    have h2 : ρ₁ (QuaternionGroup.xa 0) = ρ₂ (QuaternionGroup.xa 0) := congrArg (fun x => x.1.2) h
    ext w
    have hw : ∀ w : QuaternionGroup 2, w = 1 ∨ w = QuaternionGroup.a 1 ∨
        w = QuaternionGroup.a 1 * QuaternionGroup.a 1 ∨
        w = QuaternionGroup.a 1 * QuaternionGroup.a 1 * QuaternionGroup.a 1 ∨ w = QuaternionGroup.xa 0 ∨
        w = QuaternionGroup.xa 0 * QuaternionGroup.a 1 ∨
        w = QuaternionGroup.xa 0 * QuaternionGroup.a 1 * QuaternionGroup.a 1 ∨
        w = QuaternionGroup.xa 0 * QuaternionGroup.a 1 * QuaternionGroup.a 1 * QuaternionGroup.a 1 := by
      decide
    rcases hw w with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [map_mul, map_one, h1, h2]
  calc Nat.card (MulAut (QuaternionGroup 2)) ≤ Nat.card ↥q8GenPairs := Nat.card_le_card_of_injective f hf
    _ = 24 := by rw [Nat.card_eq_fintype_card, Fintype.card_coe, card_q8GenPairs]

theorem card_mulAut_q8_ge : 24 ≤ Nat.card (MulAut (QuaternionGroup 2)) := by
  let g : ↥q8GenPairs → MulAut (QuaternionGroup 2) := fun p =>
    MulEquiv.ofBijective (MonoidHom.mk' (q8Ext p.1.1 p.1.2) (q8Ext_mul p.1 p.2))
      (Finite.injective_iff_bijective.mp (fun u v => q8Ext_inj p.1 p.2 u v))
  have hg : Function.Injective g := by
    intro p₁ p₂ h
    have h1 := congrArg (fun σ : MulAut (QuaternionGroup 2) => σ (QuaternionGroup.a 1)) h
    have h2 := congrArg (fun σ : MulAut (QuaternionGroup 2) => σ (QuaternionGroup.xa 0)) h
    simp only [g, MulEquiv.ofBijective_apply, MonoidHom.mk'_apply, q8Ext] at h1 h2
    have hv : (1 : ZMod (2 * 2)).val = 1 := rfl
    simp only [hv, ZMod.val_zero, pow_one, pow_zero, mul_one] at h1 h2
    exact Subtype.ext (Prod.ext h1 h2)
  calc 24 = Nat.card ↥q8GenPairs := by
        rw [Nat.card_eq_fintype_card, Fintype.card_coe, card_q8GenPairs]
    _ ≤ Nat.card (MulAut (QuaternionGroup 2)) := Nat.card_le_card_of_injective g hg

private theorem card_mulAut_q8_0 : Nat.card (MulAut (QuaternionGroup 2)) = 24 :=
  le_antisymm card_mulAut_q8_le' card_mulAut_q8_ge

end CertificateChecks.Batch5014

