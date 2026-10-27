module

public import CFSG.LocalAnalysis.WeakClosure81.InCalEOneSurjective
public import CFSG.LocalAnalysis.WeakClosure81.InCalETwoAlmostSimple
public import CFSG.LocalAnalysis.WeakClosure81.InFGroupAlmostSimple
public import CFSG.Quasithin.Background.FFC4NatS3
public import CFSG.Quasithin.EmptyFaithful.PGLTwoPrimeE1Generation
import CFSG.Permutation.FiveTransitive.TwoGroupSmallCard

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.E1 CFSG.GorensteinWalter
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.Quasithin.E22L2
open CFSG.ComponentClassification.AschbacherKnownGroup.FactsL2 (pslRange pslRange_normal)
open CFSG.Quasithin.Vol2.Ch11.SecE3 (AlmostSimple)

theorem relative_generation_printed_of_pgl2_prime
    {G F : Type} [Group G] [Finite G] [Field F] [Finite F]
    {p : ℕ} [Fact p.Prime] (hF : Nat.card F = p) (hp : 5 < p)
    {T A D : Subgroup G}
    (hT : CFSG.Quasithin.IsSylowIn 2 T ⊤)
    (hAT : A ≤ T) (hA : CFSG.Open.IsElemAbelian 2 A)
    (hTau : E1.tauOf (⊤ : Subgroup G) T A ≤ T ⊓ D)
    (hSyl : CFSG.Quasithin.IsSylowIn 2 (T ⊓ D) D)
    (pi : ↥D →* PGL2 F) (hpi : Function.Surjective pi)
    (hker : IsPGroup 2 pi.ker)
    (hne : (A.subgroupOf D).map pi ≠ ⊥) :
    D ≤ T ⊔ ⨆ J ∈ {J : Subgroup G |
      CFSG.LocalAnalysis.UniquenessCase.PartTwo.InCalEi 1 T A J}, J := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite (PGL2 F) := e22pl2pgl_finite F
  have hp_ne_six : p ≠ 6 := by
    intro h
    have hp6 : Nat.Prime 6 := h ▸ Fact.out
    norm_num at hp6
  have hp7 : 7 ≤ p := by omega
  have hodd : IsOddPrimePower (Nat.card F) := e22pl2pgl_isOddPrimePower hp7 hF
  have hcardF : 3 < Nat.card F := by rw [hF]; omega
  have hAD : A ≤ D :=
    (le_sup_left.trans (E1.le_tauOf hT hAT hA)).trans (hTau.trans inf_le_right)
  let B : Subgroup (PGL2 F) := (A.subgroupOf D).map pi
  let Sbar : Subgroup (PGL2 F) := ((T ⊓ D).subgroupOf D).map pi
  have hBelem : IsElemAbelian 2 B := (hA.subgroupOf D).map pi
  have hBp : IsPGroup 2 B := hBelem.isPGroup
  have hBne : B ≠ ⊥ := hne
  have hBS : B ≤ Sbar :=
    Subgroup.map_mono (Subgroup.subgroupOf_mono D (le_inf hAT hAD))
  have hSylS : IsSylowIn 2 Sbar ⊤ := by
    have hSylD : IsSylowIn 2 ((T ⊓ D).subgroupOf D) ⊤ := by
      have h := (E1.isSylowIn_subgroupOf_iff (p := 2) (P := T ⊓ D) (K := D) (H := D)
        inf_le_right le_rfl).mpr hSyl
      simpa [Subgroup.subgroupOf_self] using h
    exact E1.isSylowIn_two_map_top hpi hSylD
  have hBcard_le : Nat.card B ≤ 4 :=
    CFSG.Quasithin.H13.card_le_four_of_isElemAbelian_pgl2_614 hodd hcardF B hBelem
  haveI : Nontrivial ↥B := (Subgroup.nontrivial_iff_ne_bot B).mpr hBne
  rcases CFSG.FiveTransitive.TwoGroupSmallCard.two_or_four hBp hBcard_le with hB2 | hB4
  ·
    haveI : (pslRange F).Normal := pslRange_normal hodd hcardF
    haveI : IsSimpleGroup ↥(pslRange F) := e22pl2pgl_simple_J hcardF
    have hnab : ∃ a b : ↥(pslRange F), a * b ≠ b * a :=
      e22pl2pgl_nonabelian_J hcardF
    have hC : Subgroup.centralizer (pslRange F : Set (PGL2 F)) = ⊥ :=
      e22pl2pgl_centralizer_J hodd hcardF
    have hLT : pslRange F ⊔ Sbar = ⊤ := e22pl2pgl_sup_eq_top hodd hSylS
    have hAS : AlmostSimple (pslRange F) :=
      almostSimple_of_normal_simple_sup_sylow (pslRange_normal hodd hcardF)
        (e22pl2pgl_simple_J hcardF) hnab hC hSylS hLT
    have hIn : InCalEi 1 T A D :=
      inCalEi_one_of_surjective_almostSimple_two_kernel hAT hA
        (by simpa [CFSG.LocalAnalysis.UniquenessCase.PartTwo.tA] using hTau)
        hSyl pi hpi hker hAS hB2
    exact le_sup_of_le_right (le_iSup₂_of_le D hIn le_rfl)
  ·
    have hKlein : IsKleinFour ↥B :=
      CFSG.Quasithin.FFC.isKleinFour_of_card_four hB4 (fun u => by
        apply Subtype.ext
        simpa using hBelem.2 u.val u.property)
    have hgen : Sbar ⊔
        (⨆ I ∈ {I : Subgroup (PGL2 F) |
          IsE 1 ⊤ Sbar B I ∧ EOne ↥I (B.subgroupOf I)}, I) = ⊤ :=
      pgl2_prime_sup_isE_one_and_eOne_eq_top hF hp hSylS hBS hKlein
    exact relative_generation_printed_of_eOne hT hAT hA hTau hSyl pi hpi hker hgen

end CFSG.LocalAnalysis.WeakClosure81

end
