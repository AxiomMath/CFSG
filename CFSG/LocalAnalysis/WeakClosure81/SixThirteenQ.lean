module

public import CFSG.LocalAnalysis.WeakClosure81.SixThirteenMod
public import CFSG.LocalAnalysis.WeakClosure81.FourteenSeven

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem commutator_barSub_BOf_ne_bot {n p : ℕ} {M V₀ V : Subgroup G} {g : G}
    (h : Hyp64 n M V₀ V g) (hgen : GenHyp M V g) (hirr : ConjGenerated M V₀ V)
    (hp : p.Prime) (hp2 : p ≠ 2) (hnp : n < dParam p)
    {X : Subgroup (MulAut (Vtil V₀ V h.elemAbelian))} (hX1 : X ≠ ⊥)
    (hXnorm : ∀ m ∈ Mbar M V₀ V h.elemAbelian, ∀ x ∈ X, m * x * m⁻¹ ∈ X)
    (hXp : IsPGroup p X) :
    ⁅X, barSub V₀ V h.elemAbelian (BOf M V g)⁆ ≠ ⊥ := by
  intro hXB
  have hV := h.elemAbelian
  have hM : M ≤ normalizer (V : Set G) := h.normalizer_eq.symm.le
  have hM₀ : M ≤ normalizer (V₀ : Set G) := h.le_normalizer₀
  have hW : ∀ w : Vtil V₀ V hV, w ^ 2 = 1 := by
    intro w
    obtain ⟨x, rfl⟩ := mkTil_surjective V₀ V hV w
    rw [← map_pow, IntMod.sq_eq_one, map_one]
  have hcard : Nat.card (Vtil V₀ V hV ⧸ imgTil V₀ V hV (UOf M V g)) < 2 ^ dParam p := by
    rw [card_quotient_imgTil hV (V₀_le_UOf h hgen), E3.relIndex_eq_two_pow hV.isPGroup]
    exact Nat.pow_lt_pow_right (by norm_num) ((mQuot_UOf_le h).trans_lt hnp)
  have htriv := commutator_le_of_card_quot_lt hW hp hp2 hXp
    (imgTil_UOf_stable_X h hgen hXB) hcard
  obtain ⟨ξ, hξ, w, hw⟩ :=
    exists_commutator_notMem hV hM hM₀ hirr hX1 hXnorm (imgTil_UOf_ne_top h hgen)
  exact hw (htriv ξ hξ w)

end CFSG.LocalAnalysis.WeakClosure81
