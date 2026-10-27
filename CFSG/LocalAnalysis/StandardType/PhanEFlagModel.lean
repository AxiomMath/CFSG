module

public import CFSG.LocalAnalysis.StandardType.PhanEFlagPsiMax
public import CFSG.LocalAnalysis.StandardType.PhanEFlagProj

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE.Flag

open Module CFSG.Monster.B.Geometry CFSG.LieType.Chevalley.CosetBuilding
  CFSG.ClassicalInvolution.Phan.PhanE

variable {K : Type} [Field K] [Finite K] {f : ℕ} [CharP K 2] {m : ℕ} {d : List ℕ}

theorem genSet_eq_flipSet (hK : Nat.card K = (2 ^ f) ^ 2) (hq : 4 ≤ 2 ^ f) (hn : m + 1 ≤ 4)
    (hd : IsCut (m + 1) d) (pol : List Bool) :
    genSet K f (m + 1) d pol =
      {E | Gate.IsFar (symCox m) (flagδ (K := K) m) (cutTypes m d) Set.univ
          (stdFlag K (m + 1)) E ∧
        resProj (symCox m) (flagδ (K := K) m) (cutTypes m d) (stdFlag K (m + 1)) E ∈
          flagPsiMax hK hd pol} := by
  have hx₀ : stdFlag K (m + 1) ∈ refSet K (m + 1) d := stdFlag_mem_refSet hd
  ext E
  constructor
  · intro hE
    obtain ⟨hfar, hOK⟩ := hE
    refine ⟨(isFar_iff_mem_farSet (K := K) hd hx₀).mpr hfar, ?_⟩
    rw [resProj_eq_gateFlag (K := K) hd hfar hx₀,
      mem_flagPsiMax_iff hK hq hn hd pol]
    exact ⟨gateFlag_mem_refSet hd hfar,
      (blockOK_iff_flagδ hK hd pol hfar).mp hOK⟩
  · rintro ⟨hfar, hmax⟩
    have hEfar : E ∈ farSet (m + 1) d :=
      (isFar_iff_mem_farSet (K := K) hd hx₀).mp hfar
    have hgate : gateFlag hd hEfar ∈ flagPsiMax hK hd pol := by
      rw [resProj_eq_gateFlag (K := K) hd hEfar hx₀] at hmax
      exact hmax
    exact ⟨hEfar, (blockOK_iff_flagδ hK hd pol hEfar).mpr
      ((mem_flagPsiMax_iff hK hq hn hd pol).mp hgate).2⟩

end CFSG.ClassicalInvolution.Phan.PhanE.Flag
