module

public import CFSG.Quasithin.Background.C126RFMain
public import CFSG.Quasithin.Background.C126RFCentral
public import CFSG.Quasithin.Background.C126RadFree
public import CFSG.Quasithin.Background.E2TwoNoNStmt

public section

namespace CFSG.Quasithin.C126

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin B2F E2

theorem radFreeStmt_of_e22 (he22 : E2.E22StatementNoN)
    (hmult : Mult2Fact) : RadFreeStmt := by
  intro G _ _ H T M V hV hmin hsq hF hred hVZ hJ hcase
  have hT := hmin.isSylow
  have hHN : H ≤ Subgroup.normalizer (V : Set G) := hred.2.1
  have hHV : ¬ H ≤ Subgroup.centralizer (V : Set G) := fun hle =>
    hJ ((thompsonJ_le_self T).trans (hT.1.trans hle))
  have hns : ¬ Group.IsSolvable ↥H := not_isSolvable_of_cases hHN hcase
  obtain ⟨⟨K₁, hK₁c, hHK, hq, hcases⟩, -⟩ := he22 G H T M hmin ⟨hsq.2, hsq.1⟩ hns
  dsimp only [E2.E22CasesNoN] at hcases
  rcases hcases with ⟨hker, -⟩ | ⟨hTN, hJ', -⟩
  · intro x hx
    obtain ⟨hxK, hxC⟩ := Subgroup.mem_inf.1 hx
    have h1 := hmin.inf_centralizer_le_kerIn hred hHV ⟨twoResidual_le H hxK, hxC⟩
    rwa [hker] at h1
  · have hK₁H : K₁ ≤ H := le_of_mem_cComp hK₁c
    have hHN₁ : H ≤ Subgroup.normalizer (K₁ : Set G) := by
      rw [hHK]
      exact sup_le Subgroup.le_normalizer hTN
    have hperf : Group.IsPerfect ↥K₁ := Subgroup.isPerfect_iff.2 (perfect_of_mem_cComp hK₁c)
    have hres : twoResidual H = K₁ := le_antisymm
      (twoResidual_le_of_isTwoQuotient hK₁H hHN₁
        (B6.isTwoQuotient_of_sup_eq hT.2.1 hHN₁ ((sup_comm T K₁).trans hHK.symm)))
      (GE23.le_twoResidual_of_perfect hK₁H hperf)
    have hQV := MinParabolic.pCoreOf_le_centralizer hred
    have hA := a134_of_cases hHN hK₁H hHN₁ hres hQV hq hcase
    exact inf_centralizer_le_pCoreOf_of_case_two hmin hred hHV hK₁H hHK hTN hJ'
      (hmult _ (c126_isQuasisimple_of_open hq) hA)

end CFSG.Quasithin.C126
