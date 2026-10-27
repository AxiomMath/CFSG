module

public import CFSG.Permutation.FiveTransitive.Degree52SeventeenTransferCore
public import CFSG.Permutation.FiveTransitive.Degree52SeventeenTransferArithmetic
public import CFSG.Permutation.FiveTransitive.Degree52LargeSylowNormalizer
public import CFSG.Permutation.FiveTransitive.Degree52LargePrimeFree
public import CFSG.Permutation.FiveTransitive.Degree31FiveFixerNormalizer

public section

namespace CFSG

namespace FiveTransitive.Degree52SeventeenTransfer

open MulAction Subgroup

private theorem normalizer_card_cases
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 52)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    {H : ℕ} (hH : H = 16 ∨ H = 48) (horder : Nat.card P = 311875200 * H)
    (S : Sylow 17 P) :
    Nat.card (normalizer (S : Set P)) = 17 ∨
      Nat.card (normalizer (S : Set P)) = 51 := by
  classical
  let _ : Fact (Nat.Prime 17) := ⟨by decide⟩
  let _ : Fintype P := Fintype.ofFinite P
  have hfree : ∀ s : Set X, s.ncard = 5 → ¬ 17 ∣ Nat.card (fixingSubgroup P s) := by
    intro s hs
    exact Degree52LargePrimeFree.not_dvd_five_fixer P hcard h5 hnotAlt s hs 17
      (by decide) (by omega)
  have hS := Degree52LargeSylowData.sylow_card P hcard h5 (Or.inl rfl) hfree S
  have hC := Degree52LargeSylowNormalizer.centralizer_card_dvd P hcard h5
    (Or.inl rfl) hfree S
  obtain ⟨hc,hr,_,_,hk,hprod⟩ :=
    Degree31FiveFixerNormalizer.normalizer_constraints P (52 / 17).factorial S hS hC
  let C := centralizer (S : Set P)
  let N := normalizer (S : Set P)
  let c := (S : Subgroup P).relIndex C
  let r := C.relIndex N
  change c ∣ (52 / 17).factorial at hc
  change r ∣ 17 - 1 at hr
  change N.index % 17 = 1 at hk
  change c * r * N.index * 17 = Nat.card P at hprod
  have hd : c * r ∣ 96 := by
    simpa [Nat.factorial] using Nat.mul_dvd_mul hc hr
  have hdcases := Degree52SeventeenTransferArithmetic.multiplier_cases hH hd hk
    (hprod.trans horder)
  have hkpos : 0 < N.index := by omega
  have hNcard : Nat.card N = c * r * 17 := by
    have hi := N.index_mul_card
    nlinarith
  change Nat.card N = 17 ∨ Nat.card N = 51
  rcases hdcases with hd | hd <;> rw [hd] at hNcard <;> omega

private theorem excluded_of_order
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 52)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    {H : ℕ} (hH : H = 16 ∨ H = 48) (horder : Nat.card P = 311875200 * H) : False := by
  let _ : Fact (Nat.Prime 17) := ⟨by decide⟩
  let S : Sylow 17 P := Sylow.nonempty.some
  have hfree : ∀ s : Set X, s.ncard = 5 → ¬ 17 ∣ Nat.card (fixingSubgroup P s) := by
    intro s hs
    exact Degree52LargePrimeFree.not_dvd_five_fixer P hcard h5 hnotAlt s hs 17
      (by decide) (by omega)
  have hS := Degree52LargeSylowData.sylow_card P hcard h5 (Or.inl rfl) hfree S
  exact Degree52SeventeenTransferCore.excluded_of_normalizer_card P hcard h5 hnotAlt S hS
    (normalizer_card_cases P hcard h5 hnotAlt hH horder S)

theorem excluded_five_fixer_orders
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 52)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5)
    (hH : Nat.card (fixingSubgroup P s) = 16 ∨ Nat.card (fixingSubgroup P s) = 48) :
    False := by
  have hi := IsMultiplyPretransitive.index_of_fixingSubgroup_eq (G := P) s (by rwa [hs])
  rw [Nat.card_eq_fintype_card,hcard,hs] at hi
  norm_num [Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial] at hi
  have hm := (fixingSubgroup P s).index_mul_card
  rw [hi] at hm
  exact excluded_of_order P hcard h5 hnotAlt hH hm.symm

end FiveTransitive.Degree52SeventeenTransfer

end CFSG
