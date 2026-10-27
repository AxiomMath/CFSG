module

import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix
public import CFSG.Quasithin.Background.G117Top

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank

namespace G11

namespace G117

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

theorem natCard_statedSL_two {e : ℕ} (he : e ≠ 0) :
    Nat.card ↥(StatedSL 2 (GaloisField 2 e)) = 2 ^ e * (2 ^ (2 * e) - 1) := by
  rw [← Nat.card_congr (specialLinearGroupEquivStatedSL 2 (GaloisField 2 e)).toEquiv,
    CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, GaloisField.card 2 e he,
    pow_mul']

theorem natCard_alternatingGroup_six : Nat.card ↥(alternatingGroup (Fin 6)) = 360 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]
  decide

theorem permAct_mem_permCore {n : ℕ} (σ : Equiv.Perm (Fin n)) {x : Fin n → ZMod 2}
    (hx : x ∈ permCore n) : permAct σ x ∈ permCore n := by
  have h : ∑ i, x i = 0 := hx
  show ∑ i, permAct σ x i = 0
  simp only [permAct]
  rw [Equiv.sum_comp σ⁻¹ x]
  exact h

theorem centralizer_trivial {Γ L : Subgroup (GLV V)}
    (hend : EndIsField (restrictRange (normalClosure Γ L) (⊤ : Submodule (ZMod 2) V)
      (invariant_top _)) 1) :
    ∀ x ∈ Γ, (∀ h ∈ normalClosure Γ L, x * h = h * x) → x = 1 := fun _ _ hx =>
  eq_one_of_commute_of_endIsField_one hend (fun k hk => (hx k hk).symm)

theorem ten_dvd_of_card_eq {Γ L : Subgroup (GLV V)} (hL : L ≤ Γ)
    (hH : Nat.card ↥(normalClosure Γ L) = 60) : 10 ∣ Nat.card ↥Γ := by
  have hdvd : Nat.card ↥(normalClosure Γ L) ∣ Nat.card ↥Γ :=
    Subgroup.card_dvd_of_le (normalClosure_le hL)
  rw [hH] at hdvd
  exact Dvd.dvd.trans (by norm_num) hdvd

variable [Finite V]

end G117

end G11

end CFSG.Quasithin
