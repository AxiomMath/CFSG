module

import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.QuasithinUnique.QTKECore
public import CFSG.Quasithin.Background.A3ComponentsBasic
public import CFSG.Quasithin.Background.B6Sections
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

open CFSG.QuasithinUnique (quasithinIsQTKECat)

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace S1414

variable {G : Type} [Group G] [Finite G]

theorem isSolvable_of_minParabolic_of_perfectCore_le {U T N V : Subgroup G}
    (h : MinParabolic U T N) (hUN : U ≤ Subgroup.normalizer (V : Set G))
    (hUV : ¬ twoResidual U ≤ Subgroup.centralizer (V : Set G))
    (hperf : perfectCore U ≤ Subgroup.centralizer (V : Set G)) : Group.IsSolvable ↥U := by
  have hCn : U ≤ Subgroup.normalizer ((U ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) :=
    fun g hg => Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer hg, B6.le_normalizer_centralizer hUN hg⟩
  have hker : U ⊓ Subgroup.centralizer (V : Set G) ≤ kerIn N U :=
    h.le_kerIn_of_not_twoResidual_le inf_le_left hCn fun hK => hUV (hK.trans inf_le_right)
  have hJ : perfectCore U ≤ kerIn N U := (le_inf (perfectCore_le U) hperf).trans hker
  have hsyl := h.isSylowTwoOf_pCoreOf_kerIn
  have hQJ : pCoreOf 2 U ≤ kerIn N U := hsyl.1
  have hNn : ((pCoreOf 2 U).subgroupOf (kerIn N U)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQJ).2
      (h.kerIn_le_H.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 U))
  have hJsolv : Group.IsSolvable ↥(kerIn N U) := by
    have h2 : IsPGroup 2 ↥((pCoreOf 2 U).subgroupOf (kerIn N U)) :=
      (hsyl.2.1).of_equiv (Subgroup.subgroupOfEquivOfLe hQJ).symm
    have hnil := h2.isNilpotent
    have : Group.IsSolvable ↥((pCoreOf 2 U).subgroupOf (kerIn N U)) := inferInstance
    have hodd : Odd (Nat.card (↥(kerIn N U) ⧸ (pCoreOf 2 U).subgroupOf (kerIn N U))) := by
      rw [Nat.odd_iff]
      have hrel := hsyl.2.2
      rcases Nat.even_or_odd (Nat.card (↥(kerIn N U) ⧸ (pCoreOf 2 U).subgroupOf (kerIn N U)))
        with he | ho
      · exact absurd (even_iff_two_dvd.1 he) hrel
      · exact Nat.odd_iff.1 ho
    have hq : Group.IsSolvable (↥(kerIn N U) ⧸ (pCoreOf 2 U).subgroupOf (kerIn N U)) :=
      CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
    exact Group.isSolvable_of_ker_le_range ((pCoreOf 2 U).subgroupOf (kerIn N U)).subtype
      (QuotientGroup.mk' ((pCoreOf 2 U).subgroupOf (kerIn N U)))
      (by simp)
  have hle : perfectCore U ≤ perfectCore (kerIn N U) :=
    le_perfectCore_of_perfect hJ (perfectCore_perfect U)
  have h0 : perfectCore (kerIn N U) = ⊥ := (isSolvable_iff_perfectCore_eq_bot _).1 hJsolv
  rw [isSolvable_iff_perfectCore_eq_bot]
  exact le_bot_iff.1 (hle.trans h0.le)

omit [Finite G] in
theorem minParabolic_of_uFamHat {M₁ K P T : Subgroup G} (hT₁ : IsSylowTwoOf T M₁)
    (hPmem : P ∈ uFamHat K T) (hPM₁ : P ≤ M₁) : ∃ N : Subgroup G, MinParabolic P T N := by
  obtain ⟨N, hN⟩ := Set.ncard_eq_one.mp hPmem.1.2.2
  exact ⟨N, B6.isSylowTwoOf_mono hT₁ hPmem.1.2.1.le hPM₁, hPmem.2, hN⟩

theorem isSolvable_of_uFamHat {M₁ K P T V : Subgroup G} (hT₁ : IsSylowTwoOf T M₁)
    (hPmem : P ∈ uFamHat K T) (hPM₁ : P ≤ M₁) (hMN : M₁ ≤ Subgroup.normalizer (V : Set G))
    (hsolv : perfectCore M₁ ≤ Subgroup.centralizer (V : Set G))
    (hPC : ¬ P ≤ (M₁ ⊓ Subgroup.centralizer (V : Set G)) ⊔ T) : Group.IsSolvable ↥P := by
  obtain ⟨N, hN⟩ := minParabolic_of_uFamHat hT₁ hPmem hPM₁
  have hUV : ¬ twoResidual P ≤ Subgroup.centralizer (V : Set G) := fun hK => hPC (by
    rw [hN.eq_twoResidual_sup]
    exact sup_le_sup_right (le_inf ((twoResidual_le P).trans hPM₁) hK) T)
  exact isSolvable_of_minParabolic_of_perfectCore_le hN (hPM₁.trans hMN) hUV
    ((perfectCore_mono hPM₁).trans hsolv)

end S1414

end CFSG.Quasithin
