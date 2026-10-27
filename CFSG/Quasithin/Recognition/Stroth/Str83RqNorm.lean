module

public import CFSG.Quasithin.Recognition.Stroth.Str83Props
public import CFSG.Quasithin.Recognition.Stroth.BenderFrame

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F112R

@[expose] def Str83RqEqNorm : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L1 L2 S : Subgroup G) (a : ℕ),
    F112HypW L1 L2 S → (S ⊓ L1) ⊔ (S ⊓ L2) = S →
    bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G) →
    1 ≤ a → Nonempty (oTwoQuot ↥L1 ≃* Sz a) → VBig L2 → VL2 L2 →
      IsL2Quot (2 * a + 1) (oTwoQuot ↥L2)

theorem str83RqEq_of_norm (h : Str83RqEqNorm) : Str83RqEq := by
  intro G _ _ L1 L2 S a hF ha hSz hB hL2
  set T : Subgroup G := (S ⊓ L1) ⊔ (S ⊓ L2) with hT
  have hF' : F112HypW L1 L2 T := f112HypW_sup_inf hF
  have hT1 : T ⊓ L1 = S ⊓ L1 := by rw [hT]; exact sup_inf_inf_left L1 L2 S
  have hT2 : T ⊓ L2 = S ⊓ L2 := by rw [hT]; exact sup_inf_inf_right L1 L2 S
  have hS' : (T ⊓ L1) ⊔ (T ⊓ L2) = T := by rw [hT1, hT2, hT]
  exact h G L1 L2 T a hF' hS' (bigB_le_normalizer_of_sup_inf_eq hF'.1 hS') ha hSz hB hL2
