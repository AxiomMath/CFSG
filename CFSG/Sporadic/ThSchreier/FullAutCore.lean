
module

public import CFSG.Sporadic.ThSchreier.FullAutCoreBase

public import CFSG.Sporadic.ThSchreier.TwoGenerate
public import CFSG.Sporadic.ThSchreier.CoreHyperplane
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import CFSG.Sporadic.Th.Plane
public import CFSG.Sporadic.Th.FormBase
public import Certificates.Data.CFSGNative.Th.Base
public import Mathlib
public import CFSG.Blueprint.NativeSporadic
public import CFSG.Blueprint.MatrixSeedIdentification
public import CFSG.Sporadic.Th.F2Spec
public import CFSG.Certificates.SchreierStabilizerGenerators
public import Certificates.Data.CFSGNative.Th.Certificate
public import CFSG.Sporadic.ThSchreier.CentralizerDataInputs
public meta import CFSG.Sporadic.ThSchreier.Text
public import CFSG.Sporadic.ThSchreier.GlobalData
public import CFSG.Sporadic.Th.Simple
public meta import CFSG.Sporadic.ThSchreier.Row
public meta import CFSG.Sporadic.ThSchreier.LocalOrbit
public import CFSG.Sporadic.ThSchreier.LocalOrbitInputs
public meta import CFSG.Sporadic.ThSchreier.Words
public meta import CFSG.Sporadic.ThSchreier.LocalData
public import CFSG.Sporadic.ThSchreier.OrbitCheck819Inputs
public meta import CFSG.Sporadic.ThSchreier.Transporter
public import CFSG.Sporadic.ThSchreier.GlobalIndex
public import CFSG.Sporadic.ThSchreier.RowInputs
public meta import Certificates.Data.CFSGNative.Th.Base
public import CFSG.Sporadic.ThSchreier.TwoCentralizerInputs
public meta import CFSG.Sporadic.ThSchreier.OrbitCheck819
public meta import CFSG.Sporadic.Th.Max3.Packet
public import CFSG.Sporadic.ThSchreier.UASpaceInputs
public meta import CFSG.Sporadic.ThSchreier.CentralizerData
public import CFSG.Sporadic.Th.Max3.Core
public import CFSG.Sporadic.Th.Max3.PacketInputs
public import CFSG.Sporadic.Th.Max3.AltNine
public import CFSG.LocalAnalysis.ComponentClassification.PresentationLocalCarmichael
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
public import CFSG.Sporadic.Th.Max3.QuotientInputs
public import CFSG.Sporadic.Th.Max3.Data
public import CFSG.Sporadic.ThSchreier.NoTransvectionInputs
public meta import CFSG.Sporadic.ThSchreier.Rigidity
public import CFSG.Sporadic.ThSchreier.RigidityInputs
public meta import CFSG.Sporadic.ThSchreier.Enc8
public import CFSG.Sporadic.Th.KernelCentralizer
public import CFSG.Sporadic.Th.KernelSimple

public section

namespace CFSG.Sporadic.ThSchreier

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Max3 CFSG.ComponentClassification.OuterAutomorphisms

theorem twoR_mem_M :
    twoR ∈ M := Q_le_M twoR_mem_Q

theorem twoR_not_mem_center :
    (⟨twoR, twoR_mem_Q⟩ : Q) ∉ Subgroup.center Q := by
  rw [center_Q, Subgroup.mem_subgroupOf]
  exact twoR_not_mem_zpowers

theorem inner_J_eq_top
    {c : ℕ} (hC : CertFacts c) (hS : ThScanFacts)
    (hInv : ∀ u : J, orderOf u = 2 → IsConj a u) : inner J = ⊤ := by
  have hcore := (ctuc_Th_core_hyperplane_centralizers twoR twoR_mem_Q twoR_not_mem_center).2
  rw [z_eq_a] at hcore
  have hL : M ⊓ twoM1 = Subgroup.centralizer {twoR} ⊓ M := by
    rw [twoM1_eq_centralizer hC hS, inf_comm]
  have hZ : ∀ s ∈ M ⊓ twoM1, (∀ l ∈ M ⊓ twoM1, s * l = l * s) →
      s ∈ Subgroup.closure {a, twoR} := by
    intro s hs hsc
    rw [hL] at hs hsc
    rw [← hcore]
    exact ⟨Subgroup.mem_centralizer_iff.2 fun l hl => (hsc l hl).symm, hs⟩
  have h1 : ∀ α : MulAut ↥M, ∃ m : ↥M, α = MulAut.conj m := max3_aut_eq_conj
  have h2 : twoR = twoG * a * twoG⁻¹ := rfl
  have h3 : twoM1 = M.map (MulAut.conj twoG).toMonoidHom := rfl
  have h := aut_inner_of_two_centralizers a twoR twoG M twoM1 hInv (orderOf_a hC)
    (centralizer_a_eq_M hC hS) h1 twoR_mem_M h2 h3 hZ (sup_twoM1_eq_top hC hS)
  exact inner_eq_top_of_allInner h

end CFSG.Sporadic.ThSchreier
