module

public import CFSG.Permutation.FiveTransitive.SimpleGoursat
public import CFSG.Permutation.FiveTransitive.FixedNormalizerAction
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

public section

namespace CFSG

namespace FiveTransitive.Degree31FiveCentralizerImage

open MulAction FixedNormalizerAction

theorem nine_dvd_centralizer
    {G X : Type} [Group G] [Finite G] [Fintype X] [DecidableEq X] [MulAction G X]
    (Q : Subgroup G) (hF : Nat.card (Fixed (X := X) Q) = 6)
    (himage : Image (X := X) Q = ⊤)
    (haut : ¬ 9 ∣ Nat.card (MulAut Q)) :
    9 ∣ Nat.card (Subgroup.centralizer (Q : Set G)) := by
  classical
  let F := Fixed (X := X) Q
  have hFcard : Nat.card F = 6 := hF
  let N := Normalizer Q
  let rho : N →* Equiv.Perm F := toPermHom N F
  let T := alternatingGroup F
  let C := Q.normalizerMonoidHom.ker
  let psi : C →* Equiv.Perm F := rho.comp C.subtype
  let _ : Nontrivial F := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  let _ : IsSimpleGroup T := alternatingGroup.isSimpleGroup (by omega)
  have hT : Nat.card T = 360 := by
    change Nat.card (alternatingGroup F) = 360
    rw [nat_card_alternatingGroup,show Nat.card F = 6 from hF]
    norm_num [Nat.factorial]
  have haux : ¬ Nat.card T ∣ Nat.card Q.normalizerMonoidHom.range := by
    intro h
    apply haut
    have hd := h.trans (Subgroup.card_subgroup_dvd_card Q.normalizerMonoidHom.range)
    exact (show 9 ∣ Nat.card T by rw [hT]; norm_num).trans hd
  have hAlt : T ≤ psi.range := by
    intro t ht
    obtain ⟨c,hfc,hgc⟩ := SimpleGoursat.exists_lift_with_aux_eq_one_of_not_dvd
      N (Equiv.Perm F) (MulAut Q) rho Q.normalizerMonoidHom T
      (by change alternatingGroup (Fixed (X := X) Q) ≤ Image (X := X) Q; rw [himage]; exact le_top)
      haux t ht
    exact ⟨⟨c,hgc⟩,hfc⟩
  have hd : 9 ∣ Nat.card C :=
    (show 9 ∣ Nat.card T by rw [hT]; norm_num).trans
      ((Subgroup.card_dvd_of_le hAlt).trans (Subgroup.card_range_dvd psi))
  have hCcard : Nat.card C = Nat.card (Subgroup.centralizer (Q : Set G)) := by
    dsimp only [C]
    rw [Q.normalizerMonoidHom_ker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (Subgroup.centralizer_le_normalizer (Q : Set G))).toEquiv
  rwa [hCcard] at hd

end FiveTransitive.Degree31FiveCentralizerImage

end CFSG
