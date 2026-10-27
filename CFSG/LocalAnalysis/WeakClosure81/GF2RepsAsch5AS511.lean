module

public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5ASShape
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5ASMaster
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch511
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5CF1
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5PSp4Five

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsL2 IsL3 IsU3 IsSp4 IsAlt OInf)
open CFSG.Blueprint (LieModel)

section Asch511

theorem asch5_11AS_of_shapes
    (h54 : Asch5_4)
    (hshape : ∀ (p : ℕ), p.Prime → 5 < p →
      ShapeInEAS 1 (fun X _ => LieModel X .PSp 2 p 1))
    (hPS : Asch5_PSp4Three) : Asch5_11AS := by
  intro Q _ _ H T hK hT hTH hCF hne hrank
  rcases h54 Q H T hK hT hTH hCF with h1 | ⟨p, hp, hp2, h3, h1⟩ | ⟨hU, hcase⟩
  · exact absurd h1 hne
  · exfalso
    rcases hrank p hp hp2 with hr | hr
    · have := CFSG.SectionRank.pRank_mono hp.one_lt (perfectCore_le H)
      omega
    · omega
  · refine ⟨⟨hU, ?_⟩, ?_⟩
    · rcases hcase with hs | ⟨L, hL, hLT, -⟩
      · exact Or.inl hs
      · exact Or.inr ⟨L, hL, hLT⟩
    rcases hcase with hs | ⟨L, hL, hLT, hShape⟩
    · exact Or.inl (inFSqAS_of_isSolvable hT hU hs)
    have hTp : IsPGroup 2 T := hT.isPGroup
    rcases hShape with h | h | ⟨h, ht⟩ | ⟨p, e, hp, hp2, h9, h⟩ |
      ⟨p, hp, hp2, ⟨hp4, h⟩ | ⟨hp4, h⟩⟩ | ⟨p, hp, hp2, h⟩
    ·
      have hCFs : CFShape ↥H (fun X _ => IsL2 X 2 ∨ IsU3 X 2) :=
        cfShape_of_isComponentModN
          (isoInvPred_or (isoInvPred_lieModel _ _ _ _) (isoInvPred_lieModel _ _ _ _)) hL hLT hTp h
      have hF2 : InFSqAS 2 H :=
        inFSqAS_of_cfShape (by norm_num) hT hU hCFs shapeInEAS_l2u3_four
      refine Or.inr ⟨hF2, L, hL, hLT, ?_⟩
      rcases hasQuotShape_or h with h' | h'
      · exact Or.inl h'
      · exact Or.inr (Or.inl h')
    ·
      have hCFs : CFShape ↥H (fun X _ => IsAlt X 6 ∨ IsL3 X 1) :=
        cfShape_of_isComponentModN
          (isoInvPred_or (isoInvPred_isAlt 6) (isoInvPred_lieModel _ _ _ _)) hL hLT hTp h
      exact Or.inl (inFSqAS_of_cfShape le_rfl hT hU hCFs shapeInEAS_alt6_l3)
    ·
      have hCFs : CFShape ↥H (fun X _ => IsL3 X 2 ∨ IsSp4 X 2) :=
        cfShape_of_isComponentModN
          (isoInvPred_or (isoInvPred_lieModel _ _ _ _) (isoInvPred_lieModel _ _ _ _)) hL hLT hTp h
      have hF2 : InFSqAS 2 H :=
        inFSqAS_of_cfShape (by norm_num) hT hU hCFs shapeInEAS_l3sp4_four
      exact Or.inr ⟨hF2, L, hL, hLT, Or.inr (Or.inr ⟨hasQuotShape_or h, ht⟩)⟩
    ·
      have hCFs : CFShape ↥H (fun X _ => F6.IsL2 p e X) :=
        cfShape_of_isComponentModN (isoInvPred_f6IsL2 p e) hL hLT hTp h
      exact Or.inl (inFSqAS_of_cfShape le_rfl hT hU hCFs (shapeInEAS_l2 hp hp2 (by omega)))
    ·
      have hCFs : CFShape ↥H (fun X _ => LieModel X .PSL 3 p 1) :=
        cfShape_of_isComponentModN (isoInvPred_lieModel _ _ _ _) hL hLT hTp h
      exact Or.inl (inFSqAS_of_cfShape le_rfl hT hU hCFs (shapeInEAS_l3_one hp hp2 hp4))
    ·
      have hCFs : CFShape ↥H (fun X _ => LieModel X .PSU 3 p 1) :=
        cfShape_of_isComponentModN (isoInvPred_lieModel _ _ _ _) hL hLT hTp h
      exact Or.inl (inFSqAS_of_cfShape le_rfl hT hU hCFs (shapeInEAS_u3_one hp hp4))
    ·
      by_cases hp3 : p = 3
      · subst hp3
        exact (false_of_psp4Three hPS hT hU hL hLT h).elim
      · by_cases hp5 : p = 5
        · subst hp5
          exact (false_of_psp4Five
            hT hU hL hLT h).elim
        · have hgt5 : 5 < p := by
            by_contra hle
            have hp4 : p ≠ 4 := by
              rintro rfl
              norm_num at hp
            have := hp.two_le
            omega
          have hCFs : CFShape ↥H (fun X _ => LieModel X .PSp 2 p 1) :=
            cfShape_of_isComponentModN (isoInvPred_lieModel _ _ _ _) hL hLT hTp h
          exact Or.inl (inFSqAS_of_cfShape le_rfl hT hU hCFs
            (hshape p hp hgt5))

end Asch511

end CFSG.LocalAnalysis.WeakClosure81

end
