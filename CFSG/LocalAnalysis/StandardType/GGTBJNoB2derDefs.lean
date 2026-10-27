module

public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
public import CFSG.LocalAnalysis.StandardType.GGFixSub
public import CFSG.LocalAnalysis.StandardType.GGResLeaf
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallRuleSpRank

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] noncomputable def ggSpFixPerp {K : Type} [Field K] [Finite K] [CharP K 2] {r : ℕ}
    [NeZero r]
    (W : Submodule K (Fin r ⊕ Fin r → K)) : Subgroup (LargeEvenProj (LargeEvenSpGroup K r)) where
  carrier := {s | ∀ v ∈ (SmallRule.spBilin K r).orthogonal W,
    (SmallRule.spRep s : Module.End K (Fin r ⊕ Fin r → K)) v = v}
  mul_mem' {a b} ha hb v hv := by
    rw [map_mul, Units.val_mul, Module.End.mul_apply, hb v hv, ha v hv]
  one_mem' v _ := by simp
  inv_mem' {a} ha v hv := by
    have h := ha v hv
    have : (SmallRule.spRep a⁻¹ : Module.End K (Fin r ⊕ Fin r → K)) v =
        (SmallRule.spRep a⁻¹ : Module.End K (Fin r ⊕ Fin r → K))
          ((SmallRule.spRep a : Module.End K (Fin r ⊕ Fin r → K)) v) := by rw [h]
    rw [this, ← Module.End.mul_apply, ← Units.val_mul, ← map_mul]
    simp

@[expose] def GGB2derSympKnown : Prop :=
  (∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab →
    LargeEvenLabelAll lab fun R _ I _ =>
      ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
        ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
        ∀ e : MulAut L', e ≠ 1 → e ^ 3 = 1 → (∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (e l)) →
          ∀ J : Subgroup L', IsComponentOf J (ggFixSub e) →
            GGHasLabel (⟨.B2der, 0, 1⟩ : LargeEvenLabel) (↥J ⧸ Subgroup.center ↥J) →
              (lab.tag = .B ∨ lab.tag = .C) ∧ lab.n = 1 ∧ 3 ≤ lab.rank) ∧
  (∀ (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 → ∀ (r : ℕ) [NeZero r], 3 ≤ r →
    ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* LargeEvenProj (LargeEvenSpGroup K r)),
      Function.Surjective ψ → ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
      IsPGroup 2 (Subgroup.center L') ∧ (4 ≤ r → Subgroup.center L' = ⊥) ∧
      ∀ e : MulAut L', e ≠ 1 → e ^ 3 = 1 →
        ∀ g : LargeEvenProj (LargeEvenSpGroup K r), (∀ l : L', ψ (e l) = g * ψ l * g⁻¹) →
          ∀ J : Subgroup L', IsComponentOf J (ggFixSub e) →
            GGHasLabel (⟨.B2der, 0, 1⟩ : LargeEvenLabel) (↥J ⧸ Subgroup.center ↥J) →
              Module.finrank K (SmallRule.fixSpaceOf SmallRule.spRep (Subgroup.zpowers g)) = 4 ∧
              J.map ψ = ⁅ggSpFixPerp (SmallRule.fixSpaceOf SmallRule.spRep (Subgroup.zpowers g)),
                ggSpFixPerp (SmallRule.fixSpaceOf SmallRule.spRep (Subgroup.zpowers g))⁆)

end CFSG.StandardType

end
