module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseA7IntersectionLeACentralizer
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.KleinFourSupInvolutionSylow
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.DihedralSylowCosetInvolutionConjugacy
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.NormalizedKleinFourInvolutionDihedral
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.InvolutionNormalizerInfConjugate
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.TwoCoreNormal
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.TwoCoreCentralizerEqualsHhat
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.KleinFourMapInjective
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CosetInvolutionCount
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.InvertedElementsLeInfConjugate
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-! # The single orbit of involutions in an even A7 coset -/

noncomputable section

open scoped Pointwise

namespace CFSG.GorensteinWalter

universe u

/-- For a centralizing outside representative `y`, any two involutions in
the coset `M y` are conjugate by an element of `D = M ∩ M^y`. -/
public theorem secondCase_a7_involutions_in_coset_conjugate_by_intersection
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (hA7 : Nonempty ((d.E ⧸ Subgroup.center d.E) ≃*
      alternatingGroup (Fin 7)))
    (hmodel : d.model = ComponentQuotientModel.alternating hA7)
    (od : SecondCaseA7OmegaData c w d)
    {y : G} (hy : IsInvolution y) (hyM : y ∉ w.M) (hyH : y ∈ c.H)
    {a b : G} (ha : IsInvolution a) (hb : IsInvolution b)
    (haCoset : a ∈ (w.M : Set G) * ({y} : Set G))
    (hbCoset : b ∈ (w.M : Set G) * ({y} : Set G)) :
    ∃ g : G, g ∈ w.M ⊓ conjugateSubgroup w.M y ∧
      g * a * g⁻¹ = b := by
  classical
  let M : Subgroup G := w.M
  let D : Subgroup G := M ⊓ conjugateSubgroup M y
  let V : Subgroup G := twoCoreOf c.Hhat
  let Z : Subgroup G := Subgroup.zpowers y
  let R : Subgroup G := D ⊔ Z
  let P : Subgroup G := V ⊔ Z
  have hVleD : V ≤ D := by
    change twoCoreOf c.Hhat ≤
      w.M ⊓ conjugateSubgroup w.M y
    exact le_sup_right.trans
      (secondCase_a7_A_sup_twoCore_le_inter_conjugate
        hmin c w d hA7 hmodel od hyH)
  have hVKint : IsKleinFour (pCore 2 c.Hhat) :=
    (secondCase_a7_klein_branch hmin c w d hA7 hmodel).1
  have hVK : IsKleinFour V := by
    change IsKleinFour ((pCore 2 c.Hhat).map c.Hhat.subtype)
    exact isKleinFour_map_of_injective
      (pCore 2 c.Hhat) hVKint c.Hhat.subtype c.Hhat.subtype_injective
  have hyD : y ∉ D := fun hyD => hyM hyD.1
  have hyV : y ∉ V := fun hyV => hyD (hVleD hyV)
  have hy2 : y * y = 1 := by simpa [pow_two] using hy.2
  have hyND : y ∈ Subgroup.normalizer (D : Set G) := by
    simpa [D, M] using
      involution_mem_normalizer_inf_conjugateSubgroup w.M hy2
  have hVeqH : twoCoreOf c.H = V := by
    simpa [V] using
      twoCoreOf_H_eq_twoCoreOf_Hhat_of_centralizerStructure c
        (theorem_2_6 hmin c)
  have hVnormal : IsNormalIn V c.H := by
    rw [← hVeqH]
    exact twoCoreOf_isNormalIn c.H
  have hyNV : y ∈ Subgroup.normalizer (V : Set G) :=
    le_normalizer_of_isNormalIn hVnormal hyH
  have hScard : Nat.card (c.S : Subgroup G) = 8 :=
    secondCase_a7_S_card_eq_eight hmin c w d hA7 hmodel
  let PR : Subgroup R := P.subgroupOf R
  obtain ⟨Q, hPReqQ, hRcard, hPRcard⟩ :=
    exists_sylow_sup_zpowers_of_normalized_kleinFour
      c.S hScard D V hVleD hVK hy hyD hyND hyNV
  change PR = (Q : Subgroup R) at hPReqQ
  change Nat.card R = Nat.card D * 2 at hRcard
  change Nat.card PR = 8 at hPRcard
  have hDleR : D ≤ R := le_sup_left
  have hVleR : V ≤ R := hVleD.trans hDleR
  have hPleR : P ≤ R := sup_le (hVleD.trans le_sup_left) le_sup_right
  let DR : Subgroup R := D.subgroupOf R
  let VR : Subgroup R := V.subgroupOf R
  have hDRcard : Nat.card DR = Nat.card D :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDleR).toEquiv
  have hDRindex : DR.index = 2 := by
    have hmul := Subgroup.card_mul_index DR
    rw [hDRcard, hRcard] at hmul
    exact Nat.mul_left_cancel (Nat.card_pos (α := D)) hmul
  have hVRcard : Nat.card VR = 4 := by
    calc
      Nat.card VR = Nat.card V :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVleR).toEquiv
      _ = 4 := hVK.card_four
  have hQcard : Nat.card Q = 8 := by
    rw [← hPReqQ]
    exact hPRcard
  have hVRlePR : VR ≤ PR := by
    intro v hv
    change (v : G) ∈ P
    exact (le_sup_left : V ≤ P) hv
  have hVRleQ : VR ≤ (Q : Subgroup R) := by
    rw [← hPReqQ]
    exact hVRlePR
  let VQ : Subgroup Q := VR.subgroupOf (Q : Subgroup R)
  have hVQcard : Nat.card VQ = 4 := by
    calc
      Nat.card VQ = Nat.card VR :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVRleQ).toEquiv
      _ = 4 := hVRcard
  have hVRK : IsKleinFour VR := isKleinFour_subgroupOf hVleR hVK
  have hVQK : IsKleinFour VQ := isKleinFour_subgroupOf hVRleQ hVRK
  let H : Subgroup Q := DR.comap (Q : Subgroup R).subtype
  have hVQleH : VQ ≤ H := by
    intro v hv
    change (v : R) ∈ DR
    change (v : G) ∈ D
    exact hVleD hv
  let yR : R :=
    ⟨y, (le_sup_right : Z ≤ R) (Subgroup.mem_zpowers y)⟩
  have hyPR : yR ∈ PR := by
    change y ∈ P
    exact (le_sup_right : Z ≤ P) (Subgroup.mem_zpowers y)
  have hyQ : yR ∈ (Q : Subgroup R) := by
    rw [← hPReqQ]
    exact hyPR
  let yQ : Q := ⟨yR, hyQ⟩
  have hyHnot : yQ ∉ H := by
    intro hyHmem
    apply hyD
    change (yR : R) ∈ DR at hyHmem
    exact hyHmem
  have hHindexNeOne : H.index ≠ 1 := by
    intro hindex
    have htop : H = ⊤ := Subgroup.index_eq_one.mp hindex
    apply hyHnot
    rw [htop]
    exact Subgroup.mem_top yQ
  have hHcardGe : 4 ≤ Nat.card H := by
    rw [← hVQcard]
    exact Nat.le_of_dvd Nat.card_pos (Subgroup.card_dvd_of_le hVQleH)
  have hHindexPos : 0 < H.index :=
    Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have hHmul := Subgroup.card_mul_index H
  have hHindexLe : H.index ≤ 2 := by
    rw [hQcard] at hHmul
    nlinarith
  have hHindex : H.index = 2 := by omega
  have hHcard : Nat.card H = 4 := by
    rw [hHindex, hQcard] at hHmul
    omega
  have hVQeqH : VQ = H :=
    Subgroup.eq_of_le_of_card_ge hVQleH (by rw [hVQcard, hHcard])
  have hHklein : IsKleinFour H := by
    rw [← hVQeqH]
    exact hVQK
  let eP : P ≃* DihedralGroup 4 :=
    (normalized_kleinFour_sup_involution_is_dihedral_four
      c.S hScard c.dihedralEquiv.some V hVK hy hyV hyNV).some
  let eQ : Q ≃* DihedralGroup 4 :=
    (MulEquiv.subgroupCongr hPReqQ).symm |>.trans
      ((Subgroup.subgroupOfEquivOfLe hPleR).trans eP)
  have coset_involution_data {x : G} (hx : IsInvolution x)
      (hxCoset : x ∈ (M : Set G) * ({y} : Set G)) :
      ∃ xR : R, (xR : G) = x ∧ xR ∉ DR := by
    have hxSet : x ∈ {z : G | IsInvolution z ∧
        z ∈ (M : Set G) * ({y} : Set G)} := ⟨hx, hxCoset⟩
    rw [involution_coset_fiber_set_eq M hy] at hxSet
    rcases hxSet with ⟨i, hi, hix⟩
    have hiInvM : i ∈ invertedElements M y := by
      rw [← invertedIn_eq_invertedElements M y]
      exact hi.1
    have hiD : i ∈ D := by
      simpa [D] using
        invertedElements_subset_inf_conjugateSubgroup M y hiInvM
    have hiM : i ∈ M := hiD.1
    have hxR : x ∈ R := by
      rw [← hix]
      exact R.mul_mem ((le_sup_left : D ≤ R) hiD)
        ((le_sup_right : Z ≤ R) (Subgroup.mem_zpowers y))
    let xR : R := ⟨x, hxR⟩
    refine ⟨xR, rfl, ?_⟩
    intro hxDR
    apply hyM
    have hxD : x ∈ D := hxDR
    have hyEq : y = i⁻¹ * x := by rw [← hix]; group
    rw [hyEq]
    exact M.mul_mem (M.inv_mem hiM) hxD.1
  obtain ⟨aR, haR, haDR⟩ :=
    coset_involution_data ha (by simpa [M] using haCoset)
  obtain ⟨bR, hbR, hbDR⟩ :=
    coset_involution_data hb (by simpa [M] using hbCoset)
  have haRI : IsInvolution aR := by
    subst a
    exact ⟨fun h => ha.1 (congrArg Subtype.val h), Subtype.ext ha.2⟩
  have hbRI : IsInvolution bR := by
    subst b
    exact ⟨fun h => hb.1 (congrArg Subtype.val h), Subtype.ext hb.2⟩
  obtain ⟨gR, hgDR, hg⟩ :=
    dihedral_sylow_involutions_not_mem_normal_index_two_conjugate
      DR hDRindex Q hHklein eQ haRI hbRI haDR hbDR
  refine ⟨(gR : G), ?_, ?_⟩
  · change (gR : G) ∈ D at hgDR
    simpa [D, M] using hgDR
  · have hgG := congrArg Subtype.val hg
    simpa [haR, hbR] using hgG

end CFSG.GorensteinWalter
