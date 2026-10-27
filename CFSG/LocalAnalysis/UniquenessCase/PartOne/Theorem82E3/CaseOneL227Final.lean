module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.CaseOneL227Fusion
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.CaseOneL227Setup
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.CaseOneL227Transport
import CFSG.GroupTheory.TransferCoset
import CFSG.GroupTheory.ABGLocalTools.SylowNormalizerGrows

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3

open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82 (K4a K4b)

variable {G : Type} [Group G] [Finite G] {D : Data G}

namespace Case811L227

variable {c : Ctx82E3 D} (h : Case811L227 c)

theorem normalizer_P_le : Subgroup.normalizer (h.P : Set G) ≤ D.M := by
  have hNP : Subgroup.normalizer (h.P : Set G) ≤
      Subgroup.normalizer (h.P : Set G) ⊓
        Subgroup.normalizer (Subgroup.centralizer (h.P : Set G) : Set G) :=
    le_inf le_rfl
      (CFSG.GorensteinWalter.normalizer_le_normalizer_centralizer_subgroup h.P)
  have hNz : Subgroup.normalizer (h.P : Set G) ≤
      Subgroup.normalizer (Subgroup.zpowers h.z : Set G) := by
    have h' := hNP.trans Subgroup.inf_normalizer_le_normalizer_inf
    simpa only [h.center_eq] using h'
  exact hNz.trans
    (h.normalizer_le (Subgroup.zpowers h.z) h.zpowers_z_le_S h.zpowers_z_ne_bot)

theorem isSylowOf_top : CFSG.ABGLocalTools.IsSylowOf 3 h.P ⊤ := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hT : CFSG.ABGLocalTools.IsSylowOf 3 h.P (D.M ⊓ ⊤) := by
    simpa using h.sylow
  have hN : Subgroup.normalizer (h.P : Set G) ⊓ ⊤ ≤ D.M := by
    simpa using normalizer_P_le h
  exact CFSG.ABGLocalTools.isSylowOf_of_normalizer_inf_le hT hN

theorem not_three_dvd_index : ¬ 3 ∣ h.P.index := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hP3 := (CFSG.ABGLocalTools.isSylowOf_iff.mp h.isSylowOf_top).2.2
  rwa [Subgroup.relIndex_top_right] at hP3

end Case811L227

theorem Case811L227.isEmpty (c : Ctx82E3 D) : IsEmpty (Case811L227 c) := by
  refine ⟨fun h => ?_⟩
  haveI : IsSimpleGroup G := D.standing.simple
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  exact CFSG.GroupTheory.false_of_isSimpleGroup_of_conj_mem_coset
    (p := 3) D.standing.nonab h.not_three_dvd_index h.S_normal_in_P
    h.relIndex_S h.y_mem h.y_not_mem_S h.y_pow_three h.inv_mul_conj_mem

namespace Ctx82E3

theorem false_of_L227 (c : Ctx82E3 D)
    (h811 : CFSG.Yardstones.Mf4cdcdf2e013.QuasisimpleModOTwo c.L)
    (hK4a : K4a) (hK4b : K4b)
    (h227 : CFSG.Blueprint.LieModel (c.Lbar ⧸ Subgroup.center c.Lbar) .PSL 2 3 3)
    (hZ : ¬ 3 ∣ Nat.card (Subgroup.center c.Lbar)) : False := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨p, hp⟩ := c.sig_nonempty
  have h76 := c.conclusion76 hp
  obtain ⟨P, hP⟩ := CFSG.ABGLocalTools.exists_isSylowOf 3 D.M
  obtain ⟨y, hyP, hyL, hy3⟩ :=
    exists_not_mem_L_of_L227 c h811 hK4a h227 hp h76 hP
  have hN : ∀ Y : Subgroup G, Y ≤ P ⊓ c.L → Y ≠ ⊥ →
      Subgroup.normalizer (Y : Set G) ≤ D.M :=
    fun Y hY hY1 => normalizer_le_of_L227 c h811 hK4a h227 hp h76 hP hY hY1
  obtain ⟨t, -, -⟩ :=
    exists_case811L227 c h811 hK4a hK4b h227 hZ hP hyP hyL hy3 hN
  exact (Case811L227.isEmpty c).false t

end Ctx82E3

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3
