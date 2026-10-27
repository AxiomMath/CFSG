
module

public import CFSG.Sporadic.ThSchreier.CentralCentralizerBase1

public import CFSG.Sporadic.ThSchreier.PlaneStabilizer
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
public import CFSG.Sporadic.ThSchreier.UASpaceInputs
public meta import CFSG.Sporadic.ThSchreier.CentralizerData
public import CFSG.Sporadic.Th.Max3.Core
public import CFSG.Sporadic.Th.Max3.AltNine
public import CFSG.LocalAnalysis.ComponentClassification.PresentationLocalCarmichael
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
public import CFSG.Sporadic.Th.Max3.QuotientInputs
public import CFSG.Sporadic.Th.Max3.Data
public import CFSG.Sporadic.Th.KernelPlanes

public section

namespace CFSG.Sporadic.ThSchreier

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Th.Max3 Pointwise

section Facts

variable {c : ℕ} (hC : CertFacts c) (hS : ThScanFacts)
include hC hS

theorem card_centralizer_a_le :
    Nat.card (Subgroup.centralizer {a} : Subgroup J) ≤ 92897280 := by
  have hOrb : (MulAction.orbit (Subgroup.centralizer {a} : Subgroup J) planeStar).ncard ≤ 120 := by
    rw [← ncard_planeY hC.orbit hS]
    apply Set.ncard_le_ncard _ (Set.toFinite _)
    rintro _ ⟨g, rfl⟩
    have hg : (g : J) * a = a * g := by
      have h := g.2
      rw [Subgroup.mem_centralizer_singleton_iff] at h
      exact h
    obtain ⟨-, hY⟩ := (planeStar_eq_iota hC.orbit hS).choose_spec
    rw [← (planeStar_eq_iota hC.orbit hS).choose_spec.1] at hY
    exact smul_mem_planeY hg hY
  have hStab : Nat.card (MulAction.stabilizer (Subgroup.centralizer {a} : Subgroup J) planeStar) =
      774144 := by
    have h1 : (MulAction.stabilizer (Subgroup.centralizer {a} : Subgroup J) planeStar).map
        (Subgroup.centralizer {a} : Subgroup J).subtype =
        Subgroup.centralizer {a} ⊓ MulAction.stabilizer J planeStar := by
      ext g
      simp only [Subgroup.mem_map, Subgroup.mem_inf, MulAction.mem_stabilizer_iff]
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨x.2, hx⟩
      · rintro ⟨hg, hgs⟩
        exact ⟨⟨g, hg⟩, hgs, rfl⟩
    have h2 : MulAction.stabilizer J planeStar =
        localH.map (MulAut.conj transporterV).toMonoidHom := by
      rw [planeStar, MulAction.stabilizer_smul_eq_stabilizer_map_conj, stabilizer_planeWSet hC,
        localH_eq]
    rw [← Subgroup.card_map_of_injective (Subgroup.centralizer {a} : Subgroup J).subtype_injective,
      h1, h2, ← centralizer_a_inf_conj, Subgroup.card_map_of_injective (conj_injective _)]
    exact card_centralizer_involT hC
  have h1 := MulAction.index_stabilizer (Subgroup.centralizer {a} : Subgroup J) planeStar
  have h2 := Subgroup.card_mul_index
    (MulAction.stabilizer (Subgroup.centralizer {a} : Subgroup J) planeStar)
  rw [h1, hStab] at h2
  rw [← h2]
  calc 774144 * (MulAction.orbit (Subgroup.centralizer {a} : Subgroup J) planeStar).ncard ≤
        774144 * 120 :=
        Nat.mul_le_mul_left _ hOrb
    _ = 92897280 := by norm_num

theorem centralizer_a_eq_M :
    Subgroup.centralizer {a} = M := by
  have hle : M ≤ Subgroup.centralizer {a} := by
    intro m hm
    rw [Subgroup.mem_centralizer_singleton_iff, ← z_eq_a]
    exact (commute_z_of_mem_M hm).eq.symm
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  rw [card_M]
  exact card_centralizer_a_le hC hS

end Facts

end CFSG.Sporadic.ThSchreier
