module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseOneL227Fusion
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseOneL227Setup
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseOneL227Transport
import CFSG.GroupTheory.TransferCoset
import CFSG.GroupTheory.ABGLocalTools.SylowNormalizerGrows

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

variable {G : Type} [Group G] [Finite G]

namespace Case811L227

variable {c : Counterexample4 G} (h : Case811L227 c)

theorem normalizer_P_le : Subgroup.normalizer (h.P : Set G) ≤ c.S.M := by
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
  have hT : CFSG.ABGLocalTools.IsSylowOf 3 h.P (c.S.M ⊓ ⊤) := by
    simpa using h.sylow
  have hN : Subgroup.normalizer (h.P : Set G) ⊓ ⊤ ≤ c.S.M := by
    simpa using normalizer_P_le h
  exact CFSG.ABGLocalTools.isSylowOf_of_normalizer_inf_le hT hN

theorem not_three_dvd_index : ¬ 3 ∣ h.P.index := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hP3 := (CFSG.ABGLocalTools.isSylowOf_iff.mp h.isSylowOf_top).2.2
  rwa [Subgroup.relIndex_top_right] at hP3

end Case811L227

theorem Case811L227.isEmpty (c : Counterexample4 G) : IsEmpty (Case811L227 c) := by
  refine ⟨fun h => ?_⟩
  haveI : IsSimpleGroup G := c.standing.simple
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  exact CFSG.GroupTheory.false_of_isSimpleGroup_of_conj_mem_coset
    (p := 3) c.standing.nonab h.not_three_dvd_index h.S_normal_in_P
    h.relIndex_S h.y_mem h.y_not_mem_S h.y_pow_three h.inv_mul_conj_mem

namespace Counterexample4

theorem false_of_L227 (c : Counterexample4 G)
    (h811 : CFSG.Yardstones.Mf4cdcdf2e013.QuasisimpleModOTwo c.L)
    (hK4a : K4a) (hK4b : K4b)
    (h227 : CFSG.Blueprint.LieModel (c.Lbar ⧸ Subgroup.center c.Lbar) .PSL 2 3 3)
    (hZ : ¬ 3 ∣ Nat.card (Subgroup.center c.Lbar)) {p : ℕ}
    (hp : p ∈ CFSG.Open.uniqueFourSigma c.S.M)
    (h76 : CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Conclusion76 c.S.M p) : False := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨P, hP⟩ := CFSG.ABGLocalTools.exists_isSylowOf 3 c.S.M
  obtain ⟨y, hyP, hyL, hy3⟩ :=
    exists_not_mem_L_of_L227 c h811 hK4a h227 hp h76 hP
  have hN : ∀ Y : Subgroup G, Y ≤ P ⊓ c.L → Y ≠ ⊥ →
      Subgroup.normalizer (Y : Set G) ≤ c.S.M :=
    fun Y hY hY1 => normalizer_le_of_L227 c h811 hK4a h227 hp h76 hP hY hY1
  obtain ⟨t, -, -⟩ :=
    exists_case811L227 c h811 hK4a hK4b h227 hZ hP hyP hyL hy3 hN
  exact (Case811L227.isEmpty c).false t

end Counterexample4

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
