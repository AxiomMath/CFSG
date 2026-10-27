module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearAlignedSylowLeComponent
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearS0CentralizesU
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearIndexParameters
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearEquationTenData
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2UniformReflectionFixed
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2CentralizerIndex
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2S0LeQuotientTorus
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Integrated equation-(9)/(10) data for the aligned linear branch
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- The group-theoretic data through equation (10), assembled after aligning
a Sylow subgroup of `M` with the ambient Sylow subgroup. -/
public structure SecondCaseLinearPostNineData
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (K : Type u) [Field K] [Finite K] where
  od : SecondCaseLinearOmegaData c w d
  hsS : (od.s : G) ∈ (c.S : Subgroup G)
  hsS0 : (od.s : G) ∉ c.S0
  hSleE : (c.S : Subgroup G) ≤ d.E
  K0_normal : IsNormalIn od.K0 (c.H ⊓ w.M)
  torus : SecondCasePSL2QuotientTorusCard d K
  S0_le_torus : (c.S0.subgroupOf d.E).map
    (QuotientGroup.mk' (Subgroup.center d.E)) ≤ torus.T
  S0_centralizes_U : (c.S0 : Subgroup G) ≤
    Subgroup.centralizer (c.U : Set G)
  equation9 : SecondCaseLinearEquationNineData d K
  equation9_Kinv : equation9.Kinv = od.K
  equation9_K0 : equation9.K0 = od.K0
  indices : SecondCaseLinearIndexParameters c w od
  equation10 : SecondCaseLinearEquationTenData c w
    (Nat.card K : ℚ) (equation9.k : ℚ) (equation9.k' : ℚ)
      (indices.u : ℚ) (indices.p0 : ℚ)

/-- Assemble equations (9) and (10) from an aligned Sylow pair. -/
public noncomputable def secondCase_linearPostNineData_of_alignedSylow
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K))
    (e : Nonempty ((d.E ⧸ Subgroup.center d.E) ≃* PSL2 K))
    (SM : Sylow 2 (↥w.M))
    (hSMleS : (SM : Subgroup w.M).map w.M.subtype ≤
      (c.S : Subgroup G))
    (SE : Sylow 2 (↥d.E))
    (hSEamb : (SE : Subgroup d.E).map d.E.subtype =
      ((SM : Subgroup w.M).map w.M.subtype) ⊓ d.E) :
    SecondCaseLinearPostNineData c w d K := by
  classical
  have hSMcent : (SM : Subgroup w.M).map w.M.subtype ≤
      Subgroup.centralizer ({c.t} : Set G) := by
    rw [← c.H_eq_centralizer]
    exact hSMleS.trans (centralizerSetup_S_le_H c)
  let hod := secondCase_linear_omegaData_of_alignedSylow
    hmin c w d K hK e SM hSMleS SE hSEamb
  let od : SecondCaseLinearOmegaData c w d := Classical.choose hod
  have hodSpec := Classical.choose_spec hod
  rcases hodSpec with
    ⟨hsSE, hsS, hsS0, _hFeq, _hBcent, _hKnorm, hKcomm⟩
  have hK0normal : IsNormalIn od.K0 (c.H ⊓ w.M) :=
    secondCase_linear_K0_normal_H_inter_M_of_aligned_commutator
      hmin c w d K hK e SM hSMcent hSMleS SE hSEamb od hsSE hKcomm
  have hSleE : (c.S : Subgroup G) ≤ d.E :=
    secondCase_linear_alignedSylow_le_component
      hmin c w d K hK e SM hSMleS SE hSEamb
  let torus : SecondCasePSL2QuotientTorusCard d K :=
    Classical.choice (secondCase_psl2_quotient_torus_card c w d K hK e)
  have hS0leT := secondCase_psl2_S0_le_quotient_torus c w d K torus hSleE
  have hS0centU : (c.S0 : Subgroup G) ≤
      Subgroup.centralizer (c.U : Set G) :=
    secondCase_linear_S0_centralizes_U
      hmin c w d K torus od hSleE hK0normal hS0leT
  let indices : SecondCaseLinearIndexParameters c w od :=
    secondCase_linearIndexParameters hmin c w d od hsS hsS0 hS0centU
  have hLayer : ∀ X : Subgroup G, X ≠ ⊥ → X ≤ od.F →
      componentLayerOf (Subgroup.normalizer (X : Set G)) = d.E :=
    secondCase_linear_layer_eq_component_of_omegaData
      hmin c w d K hK e od hsS hsS0
  let hk'ex := secondCase_psl2_odd_centralizer_index_half c w d K torus
  let k' : ℕ := Classical.choose hk'ex
  have hk'spec := Classical.choose_spec hk'ex
  rcases hk'spec with ⟨hk'half, hk'odd, _hhalfprod⟩
  let k : ℕ := Nat.card od.K * Nat.card c.S0
  have hk'half9 : k' = (Nat.card K + 1) / 2 ∨
      k' = (Nat.card K - 1) / 2 := hk'half.elim Or.inr Or.inl
  let equation9 : SecondCaseLinearEquationNineData d K :=
    secondCase_linearEquationNine_data
      hmin c w d K hK e torus od.s od.K od.K0 od.K_inverted od.K_cyclic
        od.K_le_E od.K0_eq (by
          constructor
          · intro hsone
            exact od.s_involution.1 (congrArg Subtype.val hsone)
          · apply Subtype.ext
            exact od.s_involution.2)
        od.F od.F_fixed od.FU_inter_M_eq od.F_centralizes_E hLayer
        hSleE hS0leT k k' rfl hk'half9 hk'odd
  have hFfull : od.F = centralizerIn c.FU (od.s : G) := by
    have hfull := full_fixed_subgroups_of_nilpotent_normalizer_eq
      c.U c.FU w.M od.F od.B (od.s : G)
      (fittingSubgroupOf_isNilpotent c.U)
      (fittingSubgroupOf_isNormalIn c.U)
      od.F_fixed od.B_fixed od.F_normalizer
    exact hfull.1
  have hNFfull : Subgroup.normalizer
      (centralizerIn c.FU (od.s : G) : Set G) = w.M := by
    rw [← hFfull]
    exact od.F_normalizer
  have hCU : ∀ r : G, r ∈ (c.S : Subgroup G) → r ∉ c.S0 →
      centralizerIn c.U r = od.B :=
    secondCase_psl2_uniform_reflection_fixed
      hmin c w d od.s od.B od.B_fixed hsS hsS0 hSleE hS0centU hNFfull
  have hMInter : (c.H ⊓ w.M).relIndex w.M = Nat.card K * equation9.k' := by
    apply secondCase_psl2_centralizer_index c w d K hK e torus
    · exact equation9.k'_is_half.elim Or.inr Or.inl
    · exact equation9.k'_odd
  have hequation9K : equation9.Kinv = od.K := rfl
  have hequation9K0 : equation9.K0 = od.K0 := rfl
  have hsI : IsInvolution od.s := by
    constructor
    · intro hsone
      exact od.s_involution.1 (congrArg Subtype.val hsone)
    · apply Subtype.ext
      exact od.s_involution.2
  let equation10 : SecondCaseLinearEquationTenData c w
      (Nat.card K : ℚ) (equation9.k : ℚ) (equation9.k' : ℚ)
        (indices.u : ℚ) (indices.p0 : ℚ) :=
    secondCase_linearEquationTenData
      hmin c w d od.K od.B od.s od.K_inverted od.B_fixed od.U_inter_M_eq
        hsI od.s_mem_H hCU indices.index_factor
        (hSleE.trans d.E_component.1) hMInter
        (by rw [equation9.k_def, hequation9K])
        indices.u_pos indices.p0_pos
  exact
    { od := od
      hsS := hsS
      hsS0 := hsS0
      hSleE := hSleE
      K0_normal := hK0normal
      torus := torus
      S0_le_torus := hS0leT
      S0_centralizes_U := hS0centU
      equation9 := equation9
      equation9_Kinv := hequation9K
      equation9_K0 := hequation9K0
      indices := indices
      equation10 := equation10 }

end CFSG.GorensteinWalter
