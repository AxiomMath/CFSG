module

public import Mathlib.Data.Nat.Totient
public import Mathlib.GroupTheory.GroupAction.SubMulAction.OfStabilizer
public import Mathlib.GroupTheory.Perm.Cycle.Type

public section

namespace CFSG

namespace FiveTransitive.Research.HallExceptionalCalculation

open scoped Pointwise
open MulAction Subgroup

variable {G X : Type} [Group G] [Finite G] [Fintype X] [MulAction G X]

theorem two_dvd_orderOf_of_smul_swap
    (w : G) (x y : X) (hxy : x ≠ y)
    (hwx : w • x = y) (hwy : w • y = x) :
    2 ∣ orderOf w := by
  classical
  let S : Set X := {x, y}
  have hwMem : w ∈ MulAction.stabilizer G S := by
    rw [MulAction.mem_stabilizer_iff]
    simp [S, Set.smul_set_insert, hwx, hwy, Set.pair_comm]
  let wS : MulAction.stabilizer G S := ⟨w, hwMem⟩
  let rho : MulAction.stabilizer G S →* Equiv.Perm S :=
    MulAction.toPermHom (MulAction.stabilizer G S) S
  let xS : S := ⟨x, by simp [S]⟩
  let yS : S := ⟨y, by simp [S]⟩
  have hxyS : xS ≠ yS := by
    intro h
    exact hxy (congrArg Subtype.val h)
  have hrho : rho wS = Equiv.swap xS yS := by
    ext a
    rcases a with ⟨a, ha⟩
    have ha' : a = x ∨ a = y := by
      simpa [S] using ha
    rcases ha' with rfl | rfl
    · simp [rho, wS, xS, yS, hwx, hxy]
    · simp [rho, wS, xS, yS, hwy, hxy]
  have hswapOrder : orderOf (Equiv.swap xS yS) = 2 :=
    (Equiv.Perm.swap_isSwap_iff.mpr hxyS).orderOf
  have htwoS : 2 ∣ orderOf wS := by
    rw [← hswapOrder, ← hrho]
    exact orderOf_map_dvd rho wS
  have htwoG : 2 ∣ orderOf (wS : G) := by
    rw [Subgroup.orderOf_coe]
    exact htwoS
  simpa [wS] using htwoG

private theorem two_dvd_stabilizer_natCard_of_fixed_base_and_smul_swap
    (e : Fin 4 ↪ X) (w : G)
    (hwFix : ∀ i, w • e i = e i)
    (x y : X) (hxy : x ≠ y)
    (hwx : w • x = y) (hwy : w • y = x) :
    2 ∣ Nat.card (MulAction.stabilizer G e) := by
  have hwMem : w ∈ MulAction.stabilizer G e := by
    rw [MulAction.mem_stabilizer_iff]
    apply Function.Embedding.ext
    exact hwFix
  exact (two_dvd_orderOf_of_smul_swap w x y hxy hwx hwy).trans
    ((MulAction.stabilizer G e).orderOf_dvd_natCard hwMem)

private theorem hall_exceptional_word_action
    (z u : G) (e0 e1 e2 e3 p q r : X)
    (hz0 : z • e0 = e0) (hz1 : z • e1 = e1)
    (hz2 : z • e2 = e2) (hz3 : z • e3 = e3)
    (hzp : z • p = r) (hzq : z • q = p) (hzr : z • r = q)
    (hu0 : u • e0 = e0) (hu1 : u • e1 = e1) (hur : u • r = r)
    (hu2 : u • e2 = q) (huq : u • q = e3)
    (hu3 : u • e3 = p) (hup : u • p = e2) :
    let w := (z * u) ^ 3
    w • e2 = p ∧ w • p = e2 ∧
      w • e0 = e0 ∧ w • e1 = e1 ∧ w • e3 = e3 ∧
      w • q = q ∧ w • r = r := by
  dsimp only
  simp [pow_succ, mul_smul, hu2, hzq, hup, hz2, hu0, hz0,
    hu1, hz1, hu3, hzp, hur, hzr, huq, hz3]

theorem two_dvd_stabilizer_natCard_of_hall_exceptional
    (b : Fin 4 ↪ X)
    (z u : G) (e0 e1 e2 e3 p q r : X)
    (hb0 : b 0 = e0) (hb1 : b 1 = e1)
    (hb2 : b 2 = e3) (hb3 : b 3 = q)
    (he2p : e2 ≠ p)
    (hz0 : z • e0 = e0) (hz1 : z • e1 = e1)
    (hz2 : z • e2 = e2) (hz3 : z • e3 = e3)
    (hzp : z • p = r) (hzq : z • q = p) (hzr : z • r = q)
    (hu0 : u • e0 = e0) (hu1 : u • e1 = e1) (hur : u • r = r)
    (hu2 : u • e2 = q) (huq : u • q = e3)
    (hu3 : u • e3 = p) (hup : u • p = e2) :
    2 ∣ Nat.card (MulAction.stabilizer G b) := by
  let w := (z * u) ^ 3
  have hw := hall_exceptional_word_action z u e0 e1 e2 e3 p q r
    hz0 hz1 hz2 hz3 hzp hzq hzr hu0 hu1 hur hu2 huq hu3 hup
  dsimp only at hw
  have hwFix : ∀ i, w • b i = b i := by
    intro i
    fin_cases i
    · simpa [w, hb0] using hw.2.2.1
    · simpa [w, hb1] using hw.2.2.2.1
    · simpa [w, hb2] using hw.2.2.2.2.1
    · simpa [w, hb3] using hw.2.2.2.2.2.1
  exact two_dvd_stabilizer_natCard_of_fixed_base_and_smul_swap
    b w hwFix e2 p he2p hw.1 hw.2.1

end FiveTransitive.Research.HallExceptionalCalculation

end CFSG
