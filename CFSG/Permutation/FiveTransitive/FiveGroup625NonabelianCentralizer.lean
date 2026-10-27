module

public import CFSG.Permutation.FiveTransitive.SimpleIteratedKernelImage
public import CFSG.Permutation.FiveTransitive.FiveGroup625CenterBounds
public import CFSG.Permutation.FiveTransitive.FiveGroupSmallThreeAutomorphism
public import CFSG.Permutation.FiveTransitive.CharacteristicAutomorphismKernel
public import CFSG.Permutation.FiveTransitive.FixedNormalizerAction
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
public import Mathlib.GroupTheory.Schreier

public section

namespace CFSG

namespace FiveTransitive.FiveGroup625NonabelianCentralizer

open MulAction FixedNormalizerAction

theorem nine_dvd_centralizer
    {G X : Type} [Group G] [Finite G] [Fintype X] [DecidableEq X] [MulAction G X]
    (Q : Subgroup G) (hQ : IsPGroup 5 Q) (hcard : Nat.card Q ≤ 625)
    (hnonabelian : ¬ IsMulCommutative Q) (hF : Nat.card (Fixed (X := X) Q) = 6)
    (himage : Image (X := X) Q = ⊤) :
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
  let Z := Subgroup.center Q
  have hZp : IsPGroup 5 Z := hQ.to_subgroup Z
  have hVp : IsPGroup 5 (Q ⧸ Z) :=
    hQ.of_surjective (QuotientGroup.mk' Z) (QuotientGroup.mk'_surjective Z)
  obtain ⟨hZ125,hV125⟩ := FiveGroup625CenterBounds.card_bounds Q hQ hcard hnonabelian
  have hAutZ := FiveGroupSmallThreeAutomorphism.nine_not_dvd_card_mulAut Z hZp hZ125
  have hAutV := FiveGroupSmallThreeAutomorphism.nine_not_dvd_card_mulAut (Q ⧸ Z) hVp hV125
  have hcop : Nat.Coprime 3 (Nat.card Z) := by
    let _ : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    obtain ⟨e,he⟩ := IsPGroup.iff_card.mp hZp
    rw [he]
    exact (by decide : Nat.Coprime 3 5).pow_right e
  have hJoint := CharacteristicAutomorphismKernel.prime_not_dvd Z 3 (by norm_num) hcop
  have hthree : 3 ∣ Nat.card T := by rw [hT]; norm_num
  have hnine : 9 ∣ Nat.card T := by rw [hT]; norm_num
  have hAlt : T ≤ psi.range :=
    SimpleIteratedKernelImage.le_kernel_image_of_two_aux rho Q.normalizerMonoidHom
      (CharacteristicAutomorphism.restrict Z) (CharacteristicAutomorphism.quotient Z) T
      (by change alternatingGroup (Fixed (X := X) Q) ≤ Image (X := X) Q; rw [himage]; exact le_top)
      (fun h => hAutZ (hnine.trans h)) (fun h => hAutV (hnine.trans h))
      (fun h => hJoint (hthree.trans h))
  have hd : 9 ∣ Nat.card C :=
    (show 9 ∣ Nat.card T by rw [hT]; norm_num).trans
      ((Subgroup.card_dvd_of_le hAlt).trans (Subgroup.card_range_dvd psi))
  have hCcard : Nat.card C = Nat.card (Subgroup.centralizer (Q : Set G)) := by
    dsimp only [C]
    rw [Q.normalizerMonoidHom_ker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (Subgroup.centralizer_le_normalizer (Q : Set G))).toEquiv
  rwa [hCcard] at hd

end FiveTransitive.FiveGroup625NonabelianCentralizer

end CFSG
