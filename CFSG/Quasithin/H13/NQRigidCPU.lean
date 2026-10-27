module

public import CFSG.Quasithin.H13.NQRigidCPUCore
public import CFSG.Quasithin.H13.NQRigidInputs
public import CFSG.Quasithin.H13.NQRigidCPUSection

public section

namespace CFSG.Quasithin.H13.NQRigid

open Subgroup CFSG.Quasithin

theorem stmtCPUOffenderSection_holds : StmtCPUOffenderSection := by
  intro H _ _ R hR2 hRpush K hK hF hKq hRK M hKM hRchar
  obtain ⟨V, _, _, hVv, G₀, L₀, B, hcomp, hbest, hLB, ⟨eJ⟩⟩ :=
    cpu_component_offender hR2 hRpush hK hF hKq hRK hKM hRchar
  obtain ⟨W₀, _, _, _, hW₀, L₁, B₁, hL₁q, hirr, hBe, hB1, hBN, hquad, hoff, ⟨e10⟩⟩ :=
    section_of_bestOffender hVv hcomp hbest hLB
  obtain ⟨W, _, _, _, _, L₁', B₁', hq', hirr', hBe', hB1', hBN', hquad', hoff', ⟨e1⟩⟩ :=
    moduleForm_of_mulAut hW₀ hL₁q hirr hBe hB1 hBN hquad hoff
  exact ⟨W, inferInstance, inferInstance, inferInstance, inferInstance, L₁', B₁', hq', hirr', hBe',
    hB1', hBN', hquad', hoff', ⟨((centerQuotEquivOfMulEquiv e1).trans e10).trans eJ⟩⟩

end CFSG.Quasithin.H13.NQRigid
