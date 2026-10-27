module

public import CFSG.LocalAnalysis.WeakClosure81.SixThirteen
public import CFSG.LocalAnalysis.WeakClosure81.SixThirteenQ
public import CFSG.LocalAnalysis.WeakClosure81.SixFiveL
public import CFSG.LocalAnalysis.WeakClosure81.FourteenUncond

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

section Certified


variable {M V₀ V : Subgroup G}

theorem not_inCalO1 (hH : Hyp6H M V₀ V) (hV₀ : V₀ ≠ ⊥) {k p : ℕ}
    {X : Subgroup (MulAut (Vtil V₀ V hH.elemAbelian))}
    (h : Hyp613 k p M V₀ V hH.elemAbelian X) (g : G) : ¬ InCalO1 k M V₀ V g := by
  intro hO1
  have hstar : InCalOStar k M V₀ V g := (hH.hyp65 hV₀ hO1).inCalOStar_of_lt_rMV h.lt_rMV
  have h64 : Hyp64 k M V₀ V g := hH.hyp64 hstar
  have hgen : GenHyp M V g := genHyp_of_hyp64 h64
  have hB : barSub V₀ V hH.elemAbelian (BOf M V g) ≠ ⊥ := barSub_BOf_ne_bot_uncond h64
  have hBA := six_ten_calABar_of_ne_bot hH.hyp62 (j := 2) (by norm_num) hO1.1 h.hmin hB
  have hXB : ⁅X, barSub V₀ V hH.elemAbelian (BOf M V g)⁆ = ⊥ :=
    commutator_eq_bot_of_mem_calABar_two hH.elemAbelian hBA h.le h.odd_card h.normal
  have hp2 : p ≠ 2 := by
    have := Nat.odd_iff.1 h.odd_prime
    omega
  exact commutator_barSub_BOf_ne_bot h64 hgen (hH.conjGenerated hV₀) h.prime hp2 h.lt_dParam
    h.ne_bot h.normal h.isPGroup hXB

end Certified

end CFSG.LocalAnalysis.WeakClosure81
