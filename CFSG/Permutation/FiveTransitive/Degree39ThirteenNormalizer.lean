module

public import CFSG.Permutation.FiveTransitive.Degree39FiveFixerOrder

public section

namespace CFSG

namespace FiveTransitive.Degree39ThirteenNormalizer
open MulAction Subgroup

theorem card_eq_thirteen
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 39)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (S : Sylow 13 P) : Nat.card S = 13 ∧ Nat.card (Subgroup.normalizer (S : Set P)) = 13 := by
  classical
  let _ : Fintype P := Fintype.ofFinite P
  let _ : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  have hfree : ∀ s : Set X, s.ncard = 5 → ¬ 13 ∣ Nat.card (fixingSubgroup P s) :=
    fun s hs => Degree39LargePrimeFree.not_dvd_five_fixer P hcard h5 hnotAlt s hs 13
      (by norm_num) (by omega)
  have hS := Degree39LargeSylowData.sylow_card P hcard h5 (Or.inr rfl) hfree S
  have hC := Degree39LargeSylowNormalizer.centralizer_card_dvd P hcard h5 (Or.inr rfl) hfree S
  obtain ⟨s,_,hs⟩ := Set.exists_subset_card_eq
    (show 5 ≤ (Set.univ : Set X).ncard by simp [Set.ncard_univ,hcard])
  have hP := (Degree39FiveFixerOrder.card_eq P hcard h5 hnotAlt s hs).2
  obtain ⟨hc,hr,_,_,hk,hprod⟩ := Degree31FiveFixerNormalizer.normalizer_constraints
    P 6 S hS (by norm_num at hC ⊢; exact hC)
  let C := Subgroup.centralizer (S : Set P)
  let N := Subgroup.normalizer (S : Set P)
  let c := (S : Subgroup P).relIndex C
  let r := C.relIndex N
  change c * r * N.index * 13 = Nat.card P at hprod
  have hd : c * r = 1 := Degree39FiveFixerNumeric.thirteen_factor_eq_one
    (by simpa using Nat.mul_dvd_mul hc hr) hk (hprod.trans hP)
  refine ⟨hS,?_⟩
  change Nat.card N = 13
  apply Nat.eq_of_mul_eq_mul_left (show 0 < N.index from Nat.pos_of_ne_zero
    Subgroup.index_ne_zero_of_finite)
  calc
    N.index * Nat.card N = Nat.card P := N.index_mul_card
    _ = N.index * 13 := by simpa [hd] using hprod.symm

end FiveTransitive.Degree39ThirteenNormalizer

end CFSG
