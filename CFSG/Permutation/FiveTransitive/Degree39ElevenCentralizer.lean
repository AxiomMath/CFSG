module

public import CFSG.Permutation.FiveTransitive.SimpleGoursat
public import CFSG.Permutation.FiveTransitive.FixedNormalizerAction
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

public section

namespace CFSG

namespace FiveTransitive.Degree39ElevenCentralizer

open MulAction FixedNormalizerAction

theorem five_dvd_centralizer
    {G X : Type} [Group G] [Finite G] [Fintype X] [DecidableEq X] [MulAction G X]
    (Q : Subgroup G) [Fintype (Fixed (X := X) Q)] (hF : Nat.card (Fixed (X := X) Q) = 6 ∨ Nat.card (Fixed (X := X) Q) = 17)
    (himage : alternatingGroup (Fixed (X := X) Q) ≤ Image (X := X) Q)
    (haut : ¬ 9 ∣ Nat.card (MulAut Q)) :
    5 ∣ Nat.card (Subgroup.centralizer (Q : Set G)) := by
  classical
  let F := Fixed (X := X) Q
  have hFcard : Nat.card F = 6 ∨ Nat.card F = 17 := hF
  have hFge : 6 ≤ Nat.card F := by omega
  let N := Normalizer Q
  let rho : N →* Equiv.Perm F := toPermHom N F
  let T := alternatingGroup F
  let C := Q.normalizerMonoidHom.ker
  let psi : C →* Equiv.Perm F := rho.comp C.subtype
  let _ : Nontrivial F := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  let _ : IsSimpleGroup T := alternatingGroup.isSimpleGroup (by omega)
  have hT9 : 9 ∣ Nat.card T := by
    change 9 ∣ Nat.card (alternatingGroup F)
    rw [nat_card_alternatingGroup]
    rcases hFcard with h | h <;> rw [h] <;> norm_num
  have hT5 : 5 ∣ Nat.card T := by
    change 5 ∣ Nat.card (alternatingGroup F)
    rw [nat_card_alternatingGroup]
    rcases hFcard with h | h <;> rw [h] <;> norm_num
  have haux : ¬ Nat.card T ∣ Nat.card Q.normalizerMonoidHom.range := by
    intro h
    apply haut
    have hd := h.trans (Subgroup.card_subgroup_dvd_card Q.normalizerMonoidHom.range)
    exact hT9.trans hd
  have hAlt : T ≤ psi.range := by
    intro t ht
    obtain ⟨c,hfc,hgc⟩ := SimpleGoursat.exists_lift_with_aux_eq_one_of_not_dvd
      N (Equiv.Perm F) (MulAut Q) rho Q.normalizerMonoidHom T
      himage
      haux t ht
    exact ⟨⟨c,hgc⟩,hfc⟩
  have hd : 5 ∣ Nat.card C :=
    hT5.trans
      ((Subgroup.card_dvd_of_le hAlt).trans (Subgroup.card_range_dvd psi))
  have hCcard : Nat.card C = Nat.card (Subgroup.centralizer (Q : Set G)) := by
    dsimp only [C]
    rw [Q.normalizerMonoidHom_ker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (Subgroup.centralizer_le_normalizer (Q : Set G))).toEquiv
  rwa [hCcard] at hd

end FiveTransitive.Degree39ElevenCentralizer

end CFSG
