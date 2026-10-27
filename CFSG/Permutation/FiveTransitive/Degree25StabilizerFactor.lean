module

public import CFSG.Permutation.FiveTransitive.Degree25
public import CFSG.Permutation.FiveTransitive.Degree25Seventeen
public import CFSG.Permutation.FiveTransitive.Degree25SylowEleven
public import CFSG.Permutation.FiveTransitive.Degree25Thirteen
public import CFSG.Permutation.FiveTransitive.Degree25Nineteen

public section

namespace CFSG

namespace FiveTransitive.Degree25

open MulAction SubMulAction Subgroup

theorem five_point_stabilizer_card_dvd_reduced
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 25)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) :
    Nat.card (fixingSubgroup P s) ∣
      2 ^ 18 * 3 ^ 8 * 5 ^ 4 * 7 ^ 2 := by
  classical
  let H : Subgroup P := fixingSubgroup P s
  let Y := SubMulAction.ofFixingSubgroup P s
  have hYcard : Nat.card Y = 20 := by
    change Nat.card ↥(sᶜ : Set X) = 20
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
      simpa [y, Subgroup.smul_def, Equiv.Perm.smul_def] using
        hy'
  have hHdvdFactorial :
      Nat.card H ∣ (20 : ℕ).factorial := by
    have hdvd :=
      Subgroup.card_dvd_of_injective
        (MulAction.toPermHom H Y) hfaithful
    rw [Nat.card_perm, Nat.card_eq_fintype_card,
      ← Nat.card_eq_fintype_card, hYcard] at hdvd
    exact hdvd
  have hHdvdP : Nat.card H ∣ Nat.card P :=
    Subgroup.card_subgroup_dvd_card H
  have hnotEleven : ¬11 ∣ Nat.card H := by
    simpa only [H] using
      eleven_not_dvd_five_point_stabilizer_of_not_alternating
        X P hcard h5 hnotAlt s hs
  have hnotThirteenP : ¬13 ∣ Nat.card P :=
    thirteen_not_dvd_card_of_not_alternating
      X P hcard h5 hnotAlt
  have hnotSeventeenP : ¬17 ∣ Nat.card P :=
    seventeen_not_dvd_card_of_not_alternating
      X P hcard h5 hnotAlt
  have hnotNineteenP : ¬19 ∣ Nat.card P :=
    nineteen_not_dvd_card_of_not_alternating
      X P hcard h5 hnotAlt
  have hnotThirteen : ¬13 ∣ Nat.card H :=
    fun h => hnotThirteenP (h.trans hHdvdP)
  have hnotSeventeen : ¬17 ∣ Nat.card H :=
    fun h => hnotSeventeenP (h.trans hHdvdP)
  have hnotNineteen : ¬19 ∣ Nat.card H :=
    fun h => hnotNineteenP (h.trans hHdvdP)
  have hcoprimeEleven : Nat.Coprime (Nat.card H) 11 :=
    ((show Nat.Prime 11 by norm_num).coprime_iff_not_dvd.mpr
      hnotEleven).symm
  have hcoprimeThirteen : Nat.Coprime (Nat.card H) 13 :=
    ((show Nat.Prime 13 by norm_num).coprime_iff_not_dvd.mpr
      hnotThirteen).symm
  have hcoprimeSeventeen : Nat.Coprime (Nat.card H) 17 :=
    ((show Nat.Prime 17 by norm_num).coprime_iff_not_dvd.mpr
      hnotSeventeen).symm
  have hcoprimeNineteen : Nat.Coprime (Nat.card H) 19 :=
    ((show Nat.Prime 19 by norm_num).coprime_iff_not_dvd.mpr
      hnotNineteen).symm
  have hcoprime :
      Nat.Coprime (Nat.card H) (11 * (13 * (17 * 19))) :=
    hcoprimeEleven.mul_right
      (hcoprimeThirteen.mul_right
        (hcoprimeSeventeen.mul_right hcoprimeNineteen))
  apply hcoprime.dvd_of_dvd_mul_left
  norm_num [Nat.factorial] at hHdvdFactorial ⊢
  exact hHdvdFactorial

theorem five_point_stabilizer_card_at_least_forty
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 25)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) :
    40 ≤ Nat.card (fixingSubgroup P s) := by
  let H : Subgroup P := fixingSubgroup P s
  let h := Nat.card H
  change 40 ≤ h
  have hmod : h % 23 = 17 := by
    simpa only [H, h] using
      five_point_stabilizer_card_mod_twentyThree
        X P hcard h5 hnotAlt s hs
  have hnotSeventeenP : ¬17 ∣ Nat.card P :=
    seventeen_not_dvd_card_of_not_alternating
      X P hcard h5 hnotAlt
  have hHdvdP : h ∣ Nat.card P := by
    simpa only [H, h] using
      Subgroup.card_subgroup_dvd_card H
  have hnotSeventeen : ¬17 ∣ h :=
    fun hdvd => hnotSeventeenP (hdvd.trans hHdvdP)
  by_contra hlt
  have heq : h = 17 := by omega
  exact hnotSeventeen (by rw [heq])

end FiveTransitive.Degree25

end CFSG
