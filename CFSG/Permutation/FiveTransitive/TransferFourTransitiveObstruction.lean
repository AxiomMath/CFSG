module

public import CFSG.Permutation.FiveTransitive.MinimalNormalFour
public import Mathlib.GroupTheory.Transfer

public section

namespace CFSG

namespace FiveTransitive.TransferFourTransitiveObstruction

open MulAction

theorem false_of_centralizing_sylow
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : 6 ≤ Fintype.card X)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    {p : ℕ} [Fact p.Prime] (S : Sylow p P)
    (hsmall : Nat.card S < Nat.card P)
    (hdegree : p ∣ (Fintype.card X).descFactorial 4)
    (hnormalizer : Subgroup.normalizer (S : Set P) ≤ Subgroup.centralizer (S : Set P)) :
    False := by
  let f : P →* S := MonoidHom.transferSylow S hnormalizer
  let N : Subgroup P := f.ker
  let _ : N.Normal := by dsimp only [N]; infer_instance
  have hproduct : Nat.card N * Nat.card S = Nat.card P :=
    (MonoidHom.ker_transferSylow_isComplement' S hnormalizer).card_mul_card
  have hNne : N ≠ ⊥ := by
    intro he
    rw [he,Subgroup.card_bot,one_mul] at hproduct
    omega
  let _ : Nontrivial N := N.nontrivial_iff_ne_bot.mpr hNne
  have h4 := MinimalNormalFour.four_of_normal_of_not_alternating X P hcard h5 hnotAlt N
  have hd := descFactorial_dvd_card_of_isMultiplyPretransitive N X 4 (by omega) h4
  exact MonoidHom.not_dvd_card_ker_transferSylow S hnormalizer (hdegree.trans hd)

end FiveTransitive.TransferFourTransitiveObstruction

end CFSG
