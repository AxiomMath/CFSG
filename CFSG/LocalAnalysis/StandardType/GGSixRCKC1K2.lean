module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1Helpers

public section

namespace CFSG.StandardType.RCKC1

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.StandardType CFSG.StandardType.S2MathFi1035Pos
open CFSG.StandardType.RCKSmall (RCKSmallTag RCKSmallLabel RCKSmallEmpty)

theorem rckRowK2_I_of
    (hR : RCKRootPosKnownFlag)
    (hNbr : RCKK2NbrRootSub)
    (hFlag : RCKK2FlagRootSub) :
    RCKRowK2 .I RCKPosRootSub := by
  intro X _ _ t n f ψ p G₀ A B₁ D J L
    hJrow hG0 hOddCent hprime hpne2 hA hB1A hDB1 hDcard hAnorm hMarkG hB1norm hB1cap
    hB1card hApow hAcap hAcapBot hB1L hMarkL hCompJ hOddCenJ hLG0 hExists hNotCent hCompL
    hNoA6 rb Vb hK1 hPos V r hrV hVJ hVab hVcard hr_eq hVmap hConj hK1'
  intro e heD hene K hKcomp hJK hOddK
  obtain ⟨R₀, Rm₀, hpos, hVb_le⟩ := hPos
  have himg : (V.subgroupOf J).map (QuotientGroup.mk' (Subgroup.center ↥J)) ≤
      R₀.map (QuotientGroup.mk' (Subgroup.center ↥J)) := by
    rw [hVmap]; exact hVb_le
  have hR'pos : GGRootPosJ J (R₀.map J.subtype) (Rm₀.map J.subtype) :=
    rck_rootPosJ_subtype hpos
  have hVpg : IsPGroup 2 V :=
    IsPGroup.of_card (p := 2) (G := V) (n := 2) (by rw [hVcard]; norm_num)
  have hVleR' : V ≤ R₀.map J.subtype :=
    rck_V_le_R_of_image hOddCenJ (rck_rootPosJ_isPGroup hpos) hVpg hVJ himg
  have hrne : r ≠ 1 := by
    intro h
    exact hK1.2.1 (by rw [← hr_eq, h, map_one])
  have hrneX : (r : X) ≠ 1 := by
    intro h
    exact hrne (Subtype.ext (by simpa using h))
  have hCase := hR X t n f ψ p G₀ A B₁ D J L hG0 hOddCent hprime hpne2 hA hB1A hDB1
    hDcard hAnorm hMarkG hB1norm hB1cap hB1card hApow hAcap hAcapBot hB1L hMarkL hCompJ
    hOddCenJ hLG0 hExists hNotCent hCompL hNoA6 (R₀.map J.subtype) (Rm₀.map J.subtype)
    (Subgroup.map_subtype_le R₀) (Subgroup.map_subtype_le Rm₀) hR'pos e heD hene K hKcomp hJK hOddK
  rcases hCase with hKJ | hnbrPos | hflagPos
  · subst K
    exact rck_K2_self (X := X) (J := J) (V := V) (r := (r : X)) hOddCenJ hrV hVJ hVab hVcard hK1'
  · have hNbr' := hNbr X K (R₀.map J.subtype) hnbrPos (r : X) (hVleR' hrV) hrneX
    exact hNbr'.trans ((Subgroup.centralizer_le hVleR').trans
      (Subgroup.centralizer_le_normalizer (V : Set X)))
  · have hFlag' := hFlag X K (R₀.map J.subtype) hflagPos (r : X) (hVleR' hrV) hrneX
    exact hFlag'.trans ((Subgroup.centralizer_le hVleR').trans
      (Subgroup.centralizer_le_normalizer (V : Set X)))

theorem rckRowK2_II_of
    (hR : RCKRootPosKnownII)
    (hCol : RCKK2NbrCollinear) :
    RCKRowK2 .II RCKPosRootElt := by
  intro X _ _ t n f ψ p G₀ A B₁ D J L
    hJrow hG0 hOddCent hprime hpne2 hA hB1A hDB1 hDcard hAnorm hMarkG hB1norm hB1cap
    hB1card hApow hAcap hAcapBot hB1L hMarkL hCompJ hOddCenJ hLG0 hExists hNotCent hCompL
    hNoA6 rb Vb hK1 hPos V r hrV hVJ hVab hVcard hr_eq hVmap hConj hK1'
  intro e heD hene K hKcomp hJK hOddK
  obtain ⟨R₀, Rm₀, hpos, hR0card, hR0mem⟩ := hPos
  have hR'pos : GGRootPosJ J (R₀.map J.subtype) (Rm₀.map J.subtype) :=
    rck_rootPosJ_subtype hpos
  have hR'card : Nat.card (R₀.map J.subtype) = 2 := by
    rw [Subgroup.card_subtype J R₀, hR0card]
  have hrne : r ≠ 1 := by
    intro h
    exact hK1.2.1 (by rw [← hr_eq, h, map_one])
  have hrneX : (r : X) ≠ 1 := by
    intro h
    exact hrne (Subtype.ext (by simpa using h))
  have hr2 : r ^ 2 = 1 := by
    apply Subtype.ext
    simpa using hVab.2 (r : X) hrV
  have himgR : QuotientGroup.mk' (Subgroup.center ↥J) r ∈
      R₀.map (QuotientGroup.mk' (Subgroup.center ↥J)) := by
    rw [hr_eq]; exact hR0mem
  have hrR0 : r ∈ R₀ := rck_r_mem_R hOddCenJ (rck_rootPosJ_isPGroup hpos) hr2 himgR
  have hrR' : (r : X) ∈ R₀.map J.subtype := by
    simpa using Subgroup.mem_map_of_mem J.subtype hrR0
  have hConjK : ∀ v ∈ V, v ≠ 1 → ∃ k ∈ K, v = k * (r : X) * k⁻¹ := by
    intro v hv hv1
    obtain ⟨j, hjJ, hj⟩ := hConj v hv hv1
    exact ⟨j, hJK hjJ, hj⟩
  have hCase := hR X t n f ψ p G₀ A B₁ D J L hJrow hG0 hOddCent hprime hpne2 hA hB1A hDB1
    hDcard hAnorm hMarkG hB1norm hB1cap hB1card hApow hAcap hAcapBot hB1L hMarkL hCompJ
    hOddCenJ hLG0 hExists hNotCent hCompL hNoA6 (R₀.map J.subtype) (Rm₀.map J.subtype)
    (Subgroup.map_subtype_le R₀) (Subgroup.map_subtype_le Rm₀) hR'pos hR'card e heD hene K hKcomp
    hJK hOddK
  rcases hCase with hKJ | hnbrPos
  · subst K
    exact rck_K2_self (X := X) (J := J) (V := V) (r := (r : X)) hOddCenJ hrV hVJ hVab hVcard hK1'
  · exact hCol X K (R₀.map J.subtype) V hnbrPos hR'card (r : X) hrR' hrneX hrV
      (hVJ.trans hJK) hVab hVcard hConjK

end CFSG.StandardType.RCKC1
