module

public import CFSG.Quasithin.Background.F918Z1Quot
public import CFSG.Quasithin.Background.F918Z0Mat

public section

namespace CFSG.Quasithin

theorem fixV_eq_bot_of_irrPlus {V : Type} [CommGroup V] [Finite V] (hexp : ∀ v : V, v ^ 2 = 1)
    {D X : Subgroup (MulAut V)} (hcomm : ∀ g ∈ D, ∀ x ∈ X, g * x = x * g)
    (hV : commV (D ⊔ X) = ⊤)
    (hirr : ∀ U : Subgroup V, (∀ g ∈ D ⊔ X, ∀ u ∈ U, g u ∈ U) → fixV (D ⊔ X) ≤ U →
      U = fixV (D ⊔ X) ∨ U = ⊤)
    (hDnt : ¬ D ≤ centSec ⊤ (fixV (D ⊔ X))) (hXnt : ¬ X ≤ centSec ⊤ (fixV (D ⊔ X))) :
    fixV (D ⊔ X) = ⊥ := by
  have hD : D ≤ stabSub (fixV (D ⊔ X)) := le_sup_left.trans (D37Lift.le_stabSub_fixV (D ⊔ X))
  have hX : X ≤ stabSub (fixV (D ⊔ X)) := le_sup_right.trans (D37Lift.le_stabSub_fixV (D ⊔ X))
  have hnt : Nontrivial (V ⧸ fixV (D ⊔ X)) := by
    rw [QuotientGroup.nontrivial_iff]
    intro hC
    refine hDnt fun g _ => ⟨fun u => iff_of_true trivial trivial, fun w _ => ?_⟩
    rw [hC]
    trivial
  have hexpQ : ∀ q : V ⧸ fixV (D ⊔ X), q ^ 2 = 1 := by
    intro q
    obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective q
    rw [← QuotientGroup.mk_pow, hexp v]
    rfl
  exact fixV_eq_bot_of_hasMatModel hexp hcomm hV hDnt hXnt
    (hasMatModel_of_irr hexpQ (D37Lift.comm_autQuot hcomm) (D37Lift.irr_autQuot hD hX hirr))

end CFSG.Quasithin
