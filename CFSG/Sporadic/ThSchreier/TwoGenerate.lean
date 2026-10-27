
module

public import CFSG.Sporadic.ThSchreier.TwoGenerateBase1

public import CFSG.Sporadic.ThSchreier.CentralCentralizer
public import CFSG.Sporadic.ThSchreier.TwoCentralizer
public import CFSG.Sporadic.ThSchreier.AutAssembly
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
public import CFSG.Sporadic.Th.Max3.AltNine
public import CFSG.LocalAnalysis.ComponentClassification.PresentationLocalCarmichael
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
public import CFSG.Sporadic.Th.Max3.QuotientInputs
public import CFSG.Sporadic.Th.Max3.Data
public import CFSG.Sporadic.Th.KernelCentralizer
public import CFSG.Sporadic.Th.KernelPlanes

public section

namespace CFSG.Sporadic.ThSchreier

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Max3 Pointwise

section Facts

variable {c : ℕ} (hC : CertFacts c) (hS : ThScanFacts)
include hC hS

theorem twoM1_eq_centralizer :
    twoM1 = Subgroup.centralizer {twoR} := by
  rw [twoM1, ← centralizer_a_eq_M hC hS, centralizer_map_conj]
  rfl

omit hS in
theorem stabilizer_planeStar :
    MulAction.stabilizer J planeStar = localH.map (MulAut.conj transporterV).toMonoidHom := by
  rw [planeStar, MulAction.stabilizer_smul_eq_stabilizer_map_conj, stabilizer_planeWSet hC,
    localH_eq]

omit hS in
theorem isCoatom_stabilizer_planeStar :
    IsCoatom (MulAction.stabilizer J planeStar) := by
  have := isPreprimitive_planeX hC
  have hnt : Nontrivial planeX := by
    rw [Set.nontrivial_coe_sort, ← Set.one_lt_ncard_iff_nontrivial, ncard_planeX hC]
    norm_num
  have hmem : planeStar ∈ planeX := ⟨transporterV, rfl⟩
  have h := MulAction.IsPreprimitive.isCoatom_stabilizer_of_isPreprimitive (G := J)
    (⟨planeStar, hmem⟩ : planeX)
  have e : MulAction.stabilizer J (⟨planeStar, hmem⟩ : planeX) =
      MulAction.stabilizer J planeStar := by
    ext g
    rw [MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff, Subtype.ext_iff]
    rfl
  rwa [e] at h

theorem sup_twoM1_eq_top :
    M ⊔ twoM1 = ⊤ := by
  have hK := isCoatom_stabilizer_planeStar hC
  rw [stabilizer_planeStar hC] at hK
  have hle : localH.map (MulAut.conj transporterV).toMonoidHom ≤ M ⊔ twoM1 := by
    rw [localH_eq_twoH4, twoH4, MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨x, hx, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    have h0 : transporterV * twoC0 * transporterV⁻¹ ∈ M := by
      rw [← centralizer_a_eq_M hC hS]
      exact conj_mem_centralizer_a twoC_comm.1
    have h1 : transporterV * twoC1 * transporterV⁻¹ ∈ M := by
      rw [← centralizer_a_eq_M hC hS]
      exact conj_mem_centralizer_a twoC_comm.2
    have hk (y : J) (hy : transporterV * y * transporterV⁻¹ ∈ M) :
        transporterV * (twoK * y * twoK⁻¹) * transporterV⁻¹ ∈ twoM1 := by
      refine ⟨_, hy, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, twoG]
      group
    rcases hx with rfl | rfl | rfl | rfl
    · exact Subgroup.mem_sup_left h0
    · exact Subgroup.mem_sup_left h1
    · exact Subgroup.mem_sup_right (hk _ h0)
    · exact Subgroup.mem_sup_right (hk _ h1)
  have hMK : ¬ M ≤ localH.map (MulAut.conj transporterV).toMonoidHom := by
    intro h
    have hd := Subgroup.card_dvd_of_le h
    rw [card_M, Subgroup.card_map_of_injective (conj_injective _), localH_eq, card_H hC] at hd
    norm_num at hd
  rcases hK.le_iff.1 hle with h | h
  · exact h
  · exact absurd (h ▸ le_sup_left) hMK

end Facts

end CFSG.Sporadic.ThSchreier
