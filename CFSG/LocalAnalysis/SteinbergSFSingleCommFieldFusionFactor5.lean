module

public import CFSG.LocalAnalysis.SteinbergSFSingleCommFieldFusionBridge

public section

namespace CFSG.LocalAnalysis.SymplecticFourStandard

namespace SingleCommParts

open Subgroup GomiFusion
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b
  CFSG.RankThree.PartOne.KCRootAxis RootAxisTwoCore FullCenter
open scoped Pointwise

section Steps

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {L : Subgroup G} {K : Type} [Field K]
  [CharP K 2] [Finite K] {n : ℕ} {φ : L ≃* antiSp K} {t : G} {i : Axis}

theorem sixFF_ff8_factor5 (hS : SCSetting L K n φ t i) (hH : SixHConclusion φ t i)
    (hE : EmbConclusion φ t i) (hK : SixKConclusion φ t i) (f7 : FF7Concl φ t i) :
    FF8FactorConcl n φ t i 4 := by
  intro v₀ hv2 hvC hvF hn h1 h0 _
  have hcard := ffTorus_card_K hS hn
  have hFC := hS.fc
  have hne := hS.ne_bot
  have hbot := hS.eq_bot
  obtain ⟨μ, f, g, hμJ, hμ, hχ, hfrob⟩ := ffTorus_exists_adapted_a φ (n := n)
    (by have := hS.fc.setup.two_le; omega) hS.fc.setup.card_K i.swap
  obtain ⟨c, hc⟩ := ffLayer_A φ i.swap hμ hχ
  have hMhatZ : Z₀ φ ≤ Mhat φ t i i := fun z hz =>
    mem_sup_left ((NextCores.F_le_M hFC i hne hbot)
      ((FullCenterTorus.ZP_le_Fi hFC i.swap hz).1))
  have hMC : Mhat φ t i i ⊓ centralizer ({t} : Set G) = A φ i := SixF.Mhat_inf_C hFC i hne hbot
  have hAA : A φ i ⊓ A φ i.swap = Z₀ φ := by
    cases i
    · show pull φ (rootA K Axis.one) ⊓ pull φ (rootA K Axis.two) = pull φ (antiUnipotentCenter K)
      rw [← pull_inf]
      exact congrArg (pull φ) radA1_inf_radA2
    · show pull φ (rootA K Axis.two) ⊓ pull φ (rootA K Axis.one) = pull φ (antiUnipotentCenter K)
      rw [← pull_inf]
      exact congrArg (pull φ) ((inf_comm _ _).trans radA1_inf_radA2)
  have hAM : Mhat φ t i i ⊓ A φ i.swap = Z₀ φ := by
    apply le_antisymm
    · intro x ⟨hxM, hxA⟩
      have hxC : x ∈ centralizer ({t} : Set G) := FullCenterWeyl.A_le_C hFC i.swap hxA
      have hxA' : x ∈ A φ i := by
        rw [← hMC]
        exact mem_inf.mpr ⟨hxM, hxC⟩
      rw [← hAA]
      exact mem_inf.mpr ⟨hxA', hxA⟩
    · exact le_inf hMhatZ (pull_mono φ (center_le_rootA i.swap))
  have hNM : Tplus φ t i ≤ normalizer (Mhat φ t i i : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (hH.normal_Mhat i).1).mp (hH.normal_Mhat i).2.1
  have hDT : Dstar φ t i ≤ Tplus φ t i := hH.normal_Dstar.1
  have hKD : Kc φ t i.swap ≤ Dstar φ t i := le_sup_right
  have hAD : A φ i.swap ≤ Dstar φ t i := le_sup_left.trans hKD
  have hMD : Mhat φ t i i ≤ Dstar φ t i := le_sup_left
  obtain ⟨c', hc'⟩ : ∃ c' : G → K, ScalarLayer μ (Dstar φ t i) (Mhat φ t i i) c' := by
    refine ScalarLayer.of_sup (Y := A φ i.swap) (cY := c) hMD hAD (fun x hx => ?_)
      (fun a ha m hm => ?_)
      (fun l => hH.normal_Mhat i |>.2.2 (hμJ l))
      (fun l => FullCenter.FCHyp.torus_le_normalizer_A (φ := φ) i.swap (hμJ l)) ?_
    · have hxK : x ∈ ((Mhat φ t i i : Subgroup G) : Set G) * ((Kc φ t i.swap : Subgroup G) : Set G) := by
        rw [← Subgroup.coe_mul_of_right_le_normalizer_left (Mhat φ t i i) (Kc φ t i.swap)
          ((hKD.trans hDT).trans hNM)]
        exact hx
      obtain ⟨m, hm, k, hk, rfl⟩ := Set.mem_mul.mp hxK
      have hk' : k ∈ ((A φ i.swap : Subgroup G) : Set G) * ((F φ t ⊓ D φ t i.swap : Subgroup G) : Set G) := by
        rw [FullCenterWeyl.K_mul hFC i.swap]
        exact hk
      obtain ⟨a, ha, f', hf', rfl⟩ := Set.mem_mul.mp hk'
      have hfM : f' ∈ Mhat φ t i i := mem_sup_left ((NextCores.F_le_M hFC i hne hbot) hf'.1)
      refine ⟨m * f', mul_mem hm hfM, a, ha, ?_⟩
      calc m * (a * f') = m * (f' * a) := by rw [FullCenterWeyl.A_comm_D hFC i.swap ha hf'.2]
        _ = m * f' * a := (mul_assoc _ _ _).symm
    · exact (mem_normalizer_iff.mp (hNM (hDT (hAD ha))) m).mp hm
    · rw [hAM]
      exact hc
  haveI := (f7.2.2.1 4).choose_spec
  exact ffBridge_scalar_section_one hcard μ hv2 (hfrob hv2 hvF) h1 h0 hMD
    (fun l => hH.normal_Dstar.2.2 (hμJ l)) (fun l => hH.normal_Mhat i |>.2.2 (hμJ l)) hc'

end Steps

end SingleCommParts

end CFSG.LocalAnalysis.SymplecticFourStandard
