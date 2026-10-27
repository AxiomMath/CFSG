module

public import CFSG.Permutation.FiveTransitive.Degree59LargeSylowData
public import CFSG.Permutation.FiveTransitive.AmbientSylowSmallFixedImage
public import CFSG.Permutation.FiveTransitive.PrimeNormalizerResidueObstruction

public section

namespace CFSG

namespace FiveTransitive.Degree59ElevenContradictionCore

open MulAction Subgroup FixedNormalizerAction

theorem excluded_of_three_eleven_free
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 59)
    (h5 : IsMultiplyPretransitive P X 5)
    (hthree : ∀ s : Set X, s.ncard = 5 → ¬ 3 ∣ Nat.card (fixingSubgroup P s))
    (heleven : ∀ s : Set X, s.ncard = 5 → ¬ 11 ∣ Nat.card (fixingSubgroup P s)) : False := by
  classical
  let _ : Fact (Nat.Prime 11) := ⟨by decide⟩
  let S : Sylow 11 P := Sylow.nonempty.some
  let Q : Subgroup P := S
  have hQcard : Nat.card Q = 11 := Degree59LargeSylowData.sylow_card P hcard h5
    (Or.inr (Or.inr rfl)) heleven S
  have hF : Nat.card (fixedPoints Q X) = 4 :=
    Degree59LargeSylowData.sylow_fixed_card P hcard h5 (Or.inr (Or.inr rfl)) heleven S
  have him : Image (X := X) Q = ⊤ := AmbientSylowSmallFixedImage.sylow_fixed_image
    11 4 (by decide) (by decide) P (by omega) h5 S hF
  have hFc : Nat.card (Fixed (X := X) Q) = 4 := by rw [fixed_eq]; exact hF
  have hsmall (g : P) (hg : orderOf g = 3) : Nat.card (Function.fixedPoints g.val) ≤ 4 := by
    by_contra hn
    have hlarge : 5 ≤ (Function.fixedPoints g.val).ncard := by rw [← Nat.card_coe_set_eq]; omega
    obtain ⟨s,hsub,hs⟩ := Set.exists_subset_card_eq hlarge
    let u : fixingSubgroup P s := ⟨g,(mem_fixingSubgroup_iff P).mpr (fun x hx => hsub hx)⟩
    have hu : orderOf u = 3 := (Subgroup.orderOf_coe u).symm.trans hg
    exact hthree s hs (hu ▸ orderOf_dvd_natCard u)
  exact PrimeNormalizerResidueObstruction.excluded P 11 3 4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    Q hQcard hFc him (by norm_num) hsmall (by rw [Nat.card_eq_fintype_card,hcard]; norm_num)

end FiveTransitive.Degree59ElevenContradictionCore

end CFSG
