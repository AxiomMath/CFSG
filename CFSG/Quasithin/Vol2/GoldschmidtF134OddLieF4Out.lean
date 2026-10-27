module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6LargeRee
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogLargeReeNormalForm

set_option linter.unusedSectionVars false

public section

open CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag CFSG.Blueprint CFSG.QuasithinUnique.Setup.X6
  CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.ComponentClassification.UnbalancedCatalog
  (large_Ree_full_inner_field_automorphism_normal_form)

namespace CFSG.Quasithin.H13.NQCore.F4


theorem odd_and_pow_mem_inner {X : Type} [Group X] {n : ℕ}
    (hX : ReeTitsModel X .twistedF4 2 n) :
    Odd n ∧ ∀ α : MulAut X, ∃ y : X, α ^ n = MulAut.conj y := by
  obtain ⟨a, K, _, _, _, ha, hn, hK, ⟨e⟩⟩ := exists_mulEquiv_largeRee_model hX
  have hK' : Nat.card K = 2 ^ (2 * a + 1) := hn ▸ hK
  obtain ⟨-, -, -, -, hcard, -⟩ :=
    large_Ree_full_inner_field_automorphism_normal_form a ha K hK'
  have hOut : Nat.card (Outer X) = n := by
    rw [Nat.card_congr (equivalence e).toEquiv, hcard, hn]
  refine ⟨hn ▸ odd_two_mul_add_one a, fun α => ?_⟩
  have h1 : (QuotientGroup.mk α : Outer X) ^ Nat.card (Outer X) = 1 := pow_card_eq_one'
  rw [hOut, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at h1
  obtain ⟨y, hy⟩ := h1
  exact ⟨y, hy.symm⟩

theorem center_eq_bot {X : Type} [Group X] [Finite X] {n : ℕ}
    (hX : ReeTitsModel X .twistedF4 2 n) : Subgroup.center X = ⊥ :=
  (large_Ree_model_two_extensions hX).1

end CFSG.Quasithin.H13.NQCore.F4
