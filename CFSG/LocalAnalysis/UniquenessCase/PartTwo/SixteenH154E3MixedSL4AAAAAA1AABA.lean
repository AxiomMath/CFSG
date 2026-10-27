module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedSL4AAAAAA1AABAA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedSL4AAAAAA1AABAB

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
variable {G : Type} [Group G] [Finite G]

theorem s16h_sl4_trivial_scalar_rank_two_X
    (D : Data G) {V L : Subgroup G} (h : Setting16 D ⊥ V L)
    (hrow : s16h_H5RowSL2 (lBar ⊥ V h.hyp151.isElemAbelian L)
      (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L))
      (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
        fixV (lBar ⊥ V h.hyp151.isElemAbelian L)) 2)
    (h3C : ¬ 3 ∣ Nat.card ↥(F11.CTilde D.M ⊥ V))
    {x : G} (hxM : x ∈ D.M) (hxn : x ∉ nBar D.M ⊥ V h.hyp151.isElemAbelian L)
    {φ : MulAut (Vtil ⊥ V h.hyp151.isElemAbelian)}
    (hφM : φ ∈ Mbar D.M ⊥ V h.hyp151.isElemAbelian) (hφ3 : orderOf φ = 3)
    (hcentx : ∀ a ∈ lBar ⊥ V h.hyp151.isElemAbelian (conjSubgroup L x), φ * a = a * φ)
    (hfix : ∀ z ∈ wTil ⊥ V h.hyp151.isElemAbelian L, φ z = z) :
    ∃ E : Subgroup G, E ≤ D.M ∧
      E ≤ preBarSub D.M ⊥ V h.hyp151.isElemAbelian
        (centSub (wTil ⊥ V h.hyp151.isElemAbelian L)) ∧
      IsElemAbelian 3 E ∧ 9 ≤ Nat.card ↥E := by
  obtain ⟨Ebar, hEbarM, hEbarC, hEbarAb, hEbarCard⟩ :=
    s16h_sl4_closure_rank_two D h hrow hxM hxn hφM hφ3 hcentx hfix
  exact s16h_sl4_elemAbelian_lift D h h3C hEbarM hEbarC hEbarAb hEbarCard

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
