module

public import CFSG.Permutation.FiveTransitive.Degree20Eleven
public import CFSG.Permutation.FiveTransitive.Degree20Seven
public import CFSG.Permutation.FiveTransitive.Degree20Thirteen

public section

namespace CFSG

namespace FiveTransitive.Degree20

open MulAction SubMulAction Subgroup

theorem five_point_stabilizer_card_dvd_one_hundred_eighty_six_million
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 20)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a → Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) :
    Nat.card (fixingSubgroup P s) ∣ 186624000 := by
  classical
  let H : Subgroup P := fixingSubgroup P s
  let Y := SubMulAction.ofFixingSubgroup P s
  have hYcard : Nat.card Y = 15 := by
    change Nat.card ↥(sᶜ : Set X) = 15
    rw [Nat.card_coe_set_eq]
    have htotal := Set.ncard_add_ncard_compl s
    rw [Nat.card_eq_fintype_card, hcard, hs] at htotal
    omega
  have hfaithful :
      Function.Injective (MulAction.toPermHom H Y) := by
    intro a b hab
    apply Subtype.ext
    apply P.subtype_injective
    ext x
    by_cases hx : x ∈ s
    · have ha :=
        (mem_fixingSubgroup_iff P).mp a.prop x hx
      have hb :=
        (mem_fixingSubgroup_iff P).mp b.prop x hx
      simpa [Subgroup.smul_def, Equiv.Perm.smul_def] using
        ha.trans hb.symm
    · let y : Y := ⟨x, hx⟩
      have hy :=
        congrArg (fun q : Equiv.Perm Y => q y) hab
      have hy' := congrArg Subtype.val hy
      simpa [y, Subgroup.smul_def, Equiv.Perm.smul_def] using hy'
  have hHdvdFactorial : Nat.card H ∣ (15 : ℕ).factorial := by
    have hdvd :=
      Subgroup.card_dvd_of_injective
        (MulAction.toPermHom H Y) hfaithful
    rw [Nat.card_perm, Nat.card_eq_fintype_card,
      ← Nat.card_eq_fintype_card, hYcard] at hdvd
    exact hdvd
  have hnotSevenP : ¬7 ∣ Nat.card P :=
    seven_not_dvd_card_of_not_alternating
      X P hcard h5 hnotAlt
  have hnotElevenP : ¬11 ∣ Nat.card P :=
    eleven_not_dvd_card_of_not_alternating
      X P hcard h5 hnotAlt
  have hnotThirteenP : ¬13 ∣ Nat.card P :=
    thirteen_not_dvd_card_of_not_alternating
      X P hcard h5 hnotAlt
  have hHdvdP : Nat.card H ∣ Nat.card P :=
    Subgroup.card_subgroup_dvd_card H
  have hnotSeven : ¬7 ∣ Nat.card H :=
    fun h => hnotSevenP (h.trans hHdvdP)
  have hnotEleven : ¬11 ∣ Nat.card H :=
    fun h => hnotElevenP (h.trans hHdvdP)
  have hnotThirteen : ¬13 ∣ Nat.card H :=
    fun h => hnotThirteenP (h.trans hHdvdP)
  have hcoprimeSeven : Nat.Coprime (Nat.card H) (7 ^ 2) :=
    (show Nat.Prime 7 by norm_num).coprime_pow_of_not_dvd
      hnotSeven
  have hcoprimeEleven : Nat.Coprime (Nat.card H) 11 :=
    ((show Nat.Prime 11 by norm_num).coprime_iff_not_dvd.mpr
      hnotEleven).symm
  have hcoprimeThirteen : Nat.Coprime (Nat.card H) 13 :=
    ((show Nat.Prime 13 by norm_num).coprime_iff_not_dvd.mpr
      hnotThirteen).symm
  have hcoprime :
      Nat.Coprime (Nat.card H)
        (13 * (11 * 7 ^ 2)) :=
    hcoprimeThirteen.mul_right
      (hcoprimeEleven.mul_right hcoprimeSeven)
  apply hcoprime.dvd_of_dvd_mul_left
  norm_num at hHdvdFactorial ⊢
  exact hHdvdFactorial

end FiveTransitive.Degree20

end CFSG
