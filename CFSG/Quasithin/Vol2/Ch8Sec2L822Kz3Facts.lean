module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Quasithin.Background.B4ModelsSporadic
public import CFSG.Quasithin.Background.F1Models

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin

@[expose] def kzFix_kz3 {V : Type} [CommGroup V] (z : V) : Subgroup (MulAut V) where
  carrier := {f | f z = z}
  mul_mem' := by
    intro f g hf hg
    have hf' : f z = z := hf
    have hg' : g z = z := hg
    show f (g z) = z
    rw [hg', hf']
  one_mem' := rfl
  inv_mem' := by
    intro f hf
    have hf' : f z = z := hf
    have h : f.symm (f z) = z := f.symm_apply_apply z
    rw [hf'] at h
    exact h

@[expose] def KzM22Sub5760_kz3 : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q], Nonempty (Q ≃* CFSG.Blueprint.NativeSporadic.Carrier .M22) →
    ∀ W : Subgroup Q, Nat.card W = 5760 → ⁅W, W⁆ = W ∧ IsAlt 6 (↥W ⧸ CFSG.pCore 2 ↥W)

@[expose] def KzM22Cover17280_kz3 : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q], IsHat Q (CFSG.Blueprint.NativeSporadic.Carrier .M22) →
    ∀ W : Subgroup Q, Subgroup.center Q ≤ W → Nat.card W = 17280 →
      ⁅W, W⁆ = W ∧ IsHat (↥W ⧸ CFSG.pCore 2 ↥W) (alternatingGroup (Fin 6))

@[expose] def KzCodeHexad5760_kz3 : Prop :=
  ∀ (V : Type) [CommGroup V] (A : Subgroup (MulAut V)), MathieuCode22 A ⊤ ⊥ →
    ∀ R : Subgroup (MulAut V), R ≤ Subgroup.normalizer (A : Set (MulAut V)) → IsPGroup 2 R →
      ¬ R ≤ A → Nat.card ↥(R ⊓ A) = 128 → ∀ z : V, z ≠ 1 → (∀ r ∈ R, r z = z) →
        Nat.card ↥(A ⊓ kzFix_kz3 z) = 5760

end CFSG.Quasithin.H13
