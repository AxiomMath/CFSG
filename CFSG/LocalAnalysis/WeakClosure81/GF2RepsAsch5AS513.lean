module

public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5ASShape
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5ASMaster
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch513
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5CF2c

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsL2 IsU3)
open CFSG.Blueprint (LieModel)

section Asch513


theorem asch5_13AS_holds (h512 : Asch5_12) (h411 : Asch4_11ASPow) (hSOS : Asch5_SimpOutSolv) :
    Asch5_13AS := by
  intro Q _ _ H T hK hT hTH hrank hCF hne
  obtain ⟨hU, hcase⟩ := h512 Q H T hK hT hTH hrank hCF hne
  refine ⟨hU, ?_⟩
  rcases hcase with hs | ⟨hQs, -, hShape⟩
  · exact Or.inl (inFSqAS_of_isSolvable hT hU hs)
  have hNH := relPPrimeCore_le_ambient 3 H
  have hN := normal_subgroupOf_relPPrimeCore 3 H
  rcases hShape with ⟨p, e, hp, hp5, h9, h⟩ | ⟨p, f, hp, hp5, ⟨-, h4, h⟩ | ⟨-, h4, h⟩⟩ | ⟨h, -⟩ |
    ⟨n, hn, h⟩
  ·
    have hp2 : p ≠ 2 := by omega
    have hCFs : CFShape ↥H (fun X _ => F6.IsL2 p e X) :=
      cfShape_of_fStarMod hNH hN hQs (isoInvPred_f6IsL2 p e)
        (fun X _ _ hX => hSOS X (Or.inl ⟨p, e, hp, hp2, by omega, hX⟩)) h
    exact Or.inl (inFSqAS_of_cfShape le_rfl hT hU hCFs (shapeInEAS_l2 hp hp2 (by omega)))
  ·
    have hp2 : p ≠ 2 := by omega
    have hCFs : CFShape ↥H (fun X _ => LieModel X .PSL 3 p f) :=
      cfShape_of_fStarMod hNH hN hQs (isoInvPred_lieModel _ _ _ _)
        (fun X _ _ hX => hSOS X (Or.inr ⟨p, f, hp, hp2, Or.inl hX⟩)) h
    exact Or.inl (inFSqAS_of_cfShape le_rfl hT hU hCFs
      (shapeInEAS_l3 h411 hp hp2 fun hf => by rwa [hf, pow_one] at h4))
  ·
    have hp2 : p ≠ 2 := by omega
    have hCFs : CFShape ↥H (fun X _ => LieModel X .PSU 3 p f) :=
      cfShape_of_fStarMod hNH hN hQs (isoInvPred_lieModel _ _ _ _)
        (fun X _ _ hX => hSOS X (Or.inr ⟨p, f, hp, hp2, Or.inr hX⟩)) h
    exact Or.inl (inFSqAS_of_cfShape le_rfl hT hU hCFs
      (shapeInEAS_u3 h411 hp hp2 fun hf => by rwa [hf, pow_one] at h4))
  ·
    have hCFs : CFShape ↥H (fun X _ => F6.IsL2 7 1 X) :=
      cfShape_of_fStarMod hNH hN hQs (isoInvPred_f6IsL2 7 1)
        (fun X _ _ hX => hSOS X
          (Or.inl ⟨7, 1, by norm_num, by norm_num, by norm_num, hX⟩)) h
    exact Or.inl (inFSqAS_of_cfShape le_rfl hT hU hCFs
      (shapeInEAS_l2 (by norm_num) (by norm_num) (by norm_num)))
  ·
    exact Or.inr ⟨n, hn, h⟩

end Asch513

end CFSG.LocalAnalysis.WeakClosure81

end
