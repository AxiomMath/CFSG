module

public import CFSG.Permutation.FiveTransitive.HallDihedralLifts
public import CFSG.Permutation.FiveTransitive.HallExceptionalCalculation

public section

namespace CFSG

namespace FiveTransitive.Research.HallExceptionalContradiction

open MulAction
open Research.HallDihedralLifts
open Research.HallExceptionalCalculation

variable {G X : Type} [Group G] [Finite G] [Fintype X] [MulAction G X]

theorem false_of_oriented_threeCycle_and_quarterTurn
    (h4 : MulAction.IsMultiplyPretransitive G X 4)
    (e : Fin 4 ↪ X)
    (hodd : Odd (Nat.card (MulAction.stabilizer G e)))
    (p q r : X)
    (hq0 : q ≠ e 0) (hq1 : q ≠ e 1) (hq3 : q ≠ e 3)
    (he2p : e 2 ≠ p)
    (z u : G)
    (hz0 : z • e 0 = e 0) (hz1 : z • e 1 = e 1)
    (hz2 : z • e 2 = e 2) (hz3 : z • e 3 = e 3)
    (hzp : z • p = r) (hzq : z • q = p) (hzr : z • r = q)
    (hu0 : u • e 0 = e 0) (hu1 : u • e 1 = e 1)
    (hur : u • r = r)
    (hu2 : u • e 2 = q) (huq : u • q = e 3)
    (hu3 : u • e 3 = p) (hup : u • p = e 2) :
    False := by
  classical
  let f : Fin 4 → X := ![e 0, e 1, e 3, q]
  have hf : Function.Injective f := by
    have h01 : e 0 ≠ e 1 := e.injective.ne (by decide)
    have h03 : e 0 ≠ e 3 := e.injective.ne (by decide)
    have h13 : e 1 ≠ e 3 := e.injective.ne (by decide)
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp [f, h01, h03, h13, h01.symm, h03.symm, h13.symm,
        hq0, hq1, hq3, hq0.symm, hq1.symm, hq3.symm] at hij ⊢
  let b : Fin 4 ↪ X := ⟨f, hf⟩
  have hb0 : b 0 = e 0 := rfl
  have hb1 : b 1 = e 1 := rfl
  have hb2 : b 2 = e 3 := rfl
  have hb3 : b 3 = q := rfl
  have htwo : 2 ∣ Nat.card (MulAction.stabilizer G b) :=
    two_dvd_stabilizer_natCard_of_hall_exceptional
      b z u (e 0) (e 1) (e 2) (e 3) p q r
      hb0 hb1 hb2 hb3 he2p
      hz0 hz1 hz2 hz3 hzp hzq hzr
      hu0 hu1 hur hu2 huq hu3 hup
  have hoddB : Odd (Nat.card (MulAction.stabilizer G b)) :=
    stabilizer_card_odd_of_four_transitive h4 e b hodd
  exact hoddB.not_two_dvd_nat htwo

end FiveTransitive.Research.HallExceptionalContradiction

end CFSG
