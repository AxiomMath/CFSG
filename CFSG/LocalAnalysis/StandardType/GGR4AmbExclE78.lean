module

public import CFSG.LocalAnalysis.StandardType.GGR4JMeetKGDefs
public import CFSG.LocalAnalysis.GLTheoremB.ComponentTools
public import CFSG.LocalAnalysis.GLTheoremB.QuotientTools

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem ggR4AmbExcl_E78 (hM11 : GGE78TwoLocalRankSix) :
    GGR4AmbExcl fun lab => lab.tag = .E7 ∨ lab.tag = .E8 := by
  intro G _ _ B Bs x L D J hCfg hInner hCard
  intro _ Γ _ _ C V _ _ ι φ h α _ _ _ hmark
  obtain ⟨hperf, lab, hlab, hraw⟩ := hmark
  have hlabel : GGHasLabel lab (↥L ⧸ Subgroup.center ↥L) :=
    largeEvenRawDatum_mono (fun R _ I F hq => by
      obtain ⟨-, -, θ, -⟩ := hq
      exact ⟨θ⟩) hraw
  have hT : lab.tag = .E7 ∨ lab.tag = .E8 :=
    GGDichotomy.rawDatum_elim_const (largeEvenRawDatum_mono (fun R _ I F hq => by
      obtain ⟨-, -, θ, hθ⟩ := hq
      exact hθ.1) hraw)
  haveI : Group.IsPerfect ↥L := Group.isPerfect_def.mpr hperf
  have h6 : 6 ≤ LargeEvenTwoLocalRank 3 ↥L := hM11 ↥L lab hlab hT hlabel
  have hle : LargeEvenTwoLocalRank 3 ↥L ≤ LargeEvenTwoLocalRank 3 G :=
    CFSG.LocalAnalysis.GLTheoremB.glaTwoLocalRank_subgroup_le (by norm_num) L
  have hBmax : LargeEvenIsBmax 3 B := hCfg.1.2.2.2.2.2.2.1.1
  have hBcard : Nat.card B = 3 ^ LargeEvenTwoLocalRank 3 G := hBmax.2.1
  have hBBs : B ≤ Bs := hCfg.2.1.1
  have hBle : Nat.card B ≤ Nat.card Bs :=
    Nat.card_le_card_of_injective (Subgroup.inclusion hBBs)
      (Subgroup.inclusion_injective hBBs)
  have h5 : LargeEvenTwoLocalRank 3 G ≤ 5 := by
    have hpow : 3 ^ LargeEvenTwoLocalRank 3 G ≤ 3 ^ 5 := by
      rw [← hBcard, ← hCard]
      exact hBle
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp hpow
  omega

end CFSG.StandardType

end
