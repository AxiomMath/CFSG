module

public import CFSG.Quasithin.Background.Harris.KFact2d.F3L3
public import CFSG.Quasithin.Background.Harris.KFact2d.F3U3
public import CFSG.ClassicalInvolution.Q3.Q3WASAut
public import CFSG.Adapters.SpecialLinearPerfect
public import CFSG.ClassicalInvolution.ModelFacts.UnitaryAutLift

public section

open CFSG.Open CFSG.Quasithin.E2P.Asc80 CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.B6
open scoped MatrixGroups Matrix

namespace CFSG.Quasithin.Background.Harris.KFact2d

variable {p : ℕ} [Fact p.Prime]

theorem linClass_zmod_all
    (hp2 : p ≠ 2) :
    CFSG.ClassicalInvolution.RouteD.Gaps.LinearAutClassification (ZMod p) 3 := by
  by_cases h3 : p = 3
  · subst h3
    have : Fintype (GaloisField 3 1) := Fintype.ofFinite _
    have hc : Fintype.card (GaloisField 3 1) = Fintype.card (ZMod 3) := by
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, GaloisField.card 3 1 one_ne_zero,
        pow_one, Nat.card_zmod]
    exact linAutClass_of_ringEquiv (FiniteField.ringEquivOfCardEq hc)
      (CFSG.ClassicalInvolution.Q3.Q3W.linearAutClassification3 le_rfl)
  · have : 5 ≤ p := by
      have := (Fact.out : p.Prime).two_le
      have h4 : p ≠ 4 := by
        intro h
        have hp := (Fact.out : p.Prime)
        rw [h] at hp
        exact absurd hp (by norm_num)
      omega
    exact linClass_zmod hp2 this

end CFSG.Quasithin.Background.Harris.KFact2d
