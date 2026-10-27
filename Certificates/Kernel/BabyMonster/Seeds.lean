
module

public import Certificates.Kernel.BSeed.Bind
public import Certificates.Kernel.BabyMonster.Chain
public import CFSG.Certificates.Kernel.BabyMonster.Seeds.Check0
public import CFSG.Certificates.Kernel.BabyMonster.Seeds.Check1
public import CFSG.Certificates.Kernel.BabyMonster.Seeds.Check2
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsF2Fast
public import CFSG.Open.Defs
public import Certificates.Data.CFSGNative.SectionRank.B

public section

namespace CertificateChecks.KernelBM

open CFSG.KC.BM CFSG.KC.BSeed

theorem genA₁_eq_stripMat : CFSG.Monster.B.genA₁ = stripMat CFSG.KC.BM.Seeds.A1 := by
  rw [CertificateChecks.KernelBSeed.genA₁_eq]
  exact rowsMat_eq_stripMat (R := CFSG.KC.BM.Seeds.A1.rows) (S := CFSG.KC.BM.Seeds.A1)
    (by bm_blocks CFSG.KC.BM.Seeds.rows_A1 69) CFSG.KC.BM.Seeds.wf_A1

theorem genA₂_eq_stripMat : CFSG.Monster.B.genA₂ = stripMat CFSG.KC.BM.Seeds.A2 := by
  rw [CertificateChecks.KernelBSeed.genA₂_eq]
  exact rowsMat_eq_stripMat (R := CFSG.KC.BM.Seeds.A2.rows) (S := CFSG.KC.BM.Seeds.A2)
    (by bm_blocks CFSG.KC.BM.Seeds.rows_A2 69) CFSG.KC.BM.Seeds.wf_A2

theorem genA₁_mul_self : CFSG.Monster.B.genA₁ * CFSG.Monster.B.genA₁ = 1 := by
  have h := stripMat_mul_eq_one (Ws := [CFSG.KC.BM.Seeds.A1]) (A := CFSG.KC.BM.Seeds.A1)
    (by
      intro W hW
      rw [List.mem_singleton] at hW
      rw [hW]
      exact CFSG.KC.BM.Seeds.wf_A1)
    CFSG.KC.BM.Seeds.wf_A1 (by bm_strips CFSG.KC.BM.Seeds.a1sq 69)
  rw [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil] at h
  rw [genA₁_eq_stripMat]
  exact h

theorem genA₂_cube :
    CFSG.Monster.B.genA₂ * CFSG.Monster.B.genA₂ * CFSG.Monster.B.genA₂ = 1 := by
  have h := stripMat_mul_eq_one (Ws := [CFSG.KC.BM.Seeds.A2, CFSG.KC.BM.Seeds.A2])
    (A := CFSG.KC.BM.Seeds.A2)
    (by
      intro W hW
      rw [List.mem_cons, List.mem_singleton, or_self] at hW
      rw [hW]
      exact CFSG.KC.BM.Seeds.wf_A2)
    CFSG.KC.BM.Seeds.wf_A2 (by bm_strips CFSG.KC.BM.Seeds.a2cube 69)
  rw [List.map_cons, List.map_cons, List.map_nil, List.foldl_cons, List.foldl_cons,
    List.foldl_nil] at h
  rw [genA₂_eq_stripMat]
  exact h

end CertificateChecks.KernelBM

end
