module

public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs
public import CFSG.LocalAnalysis.StandardType.GGStdPosLocalDefs
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate120
public import Certificates.Certificate123
import CFSG.LocalAnalysis.StandardType.GGSecFivePumpBstar
import CFSG.LocalAnalysis.StandardType.GGStdPosAutHolds
import CFSG.LocalAnalysis.StandardType.GGRootInvolutionRank
import CFSG.LieType.Steinberg.CentralExt.Unipotent
import Mathlib.Tactic.Group

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.LieType.Steinberg

theorem ggKGCent_bstar_eq
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J)
    {X : Subgroup G} {tg : StatedLieTag} {n f : ℕ}
    {ψ : (ggU tg n f).K →* G} (hloc : GGKGPosLocalHyp p Bs X tg n f ψ)
    (hstd : GGKGPosStdPos (ggU tg n f).D ψ Bs) :
    Bs = B := by
  obtain ⟨-, -, hadm, hrank⟩ := hloc.1
  have ht := hloc.2.1.2.2.1
  obtain ⟨-, -, xp, C, O, hE⟩ := ggStdPos_bruhatData (f := f) hrank ht
  have hr : 0 < (ggU tg n f).D.rank := by
    rw [lieUniversal_rank_eq_bnRank tg n 2 f Nat.prime_two hadm hrank]
    omega
  set γ : Fin (ggU tg n f).D.rank → ℤ := Pi.single ⟨0, hr⟩ 1
  have hγ : γ ∈ (ggU tg n f).D.roots := single_mem_roots ⟨0, hr⟩
  set T : Subgroup G := ((ggU tg n f).D.rootGroup γ).map ψ
  have hT2 : IsPGroup 2 T := (isPGroup_of_isParametrization (p := 2) hE.param hγ).map ψ
  have hT1 : T ≠ ⊥ := by
    obtain ⟨b, -, z, hz, hne⟩ := ggKGPosNoTrivRootStmt_holds G p Bs X tg n f ψ hloc hstd γ hγ
    intro hbot
    have hzT : ψ z ∈ T := Subgroup.mem_map_of_mem ψ hz
    rw [hbot, Subgroup.mem_bot] at hzT
    exact hne (by rw [hzT, mul_one, mul_inv_cancel])
  have key : ∀ c ∈ Bs, ∀ z ∈ (ggU tg n f).D.rootGroup γ, c * ψ z * c⁻¹ ∈ T := by
    intro c hc z hz
    obtain ⟨h, hh, hcz⟩ := hstd c hc γ hγ
    have hN := Subgroup.mem_iInf.mp (Subgroup.mem_iInf.mp hh γ) hγ
    rw [hcz z hz]
    exact Subgroup.mem_map_of_mem ψ ((Subgroup.mem_normalizer_iff.mp hN z).mp hz)
  refine ggBstar_eq_of_normalizes_two hcfg hT2 hT1 fun c hc => ?_
  rw [Subgroup.mem_normalizer_iff]
  intro g
  constructor
  · intro hg
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hg
    exact key c hc z hz
  · intro hg
    obtain ⟨z, hz, hzg⟩ := Subgroup.mem_map.mp hg
    have hk := key c⁻¹ (Bs.inv_mem hc) z hz
    have e : c⁻¹ * ψ z * c⁻¹⁻¹ = g := by
      rw [hzg]
      group
    rwa [e] at hk

end CFSG.StandardType

end
