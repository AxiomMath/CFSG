module

public import CFSG.Blueprint.Catalog
public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.RankThree.PartTwo.ClassTwoEightActionInverting
import CFSG.RankThree.PartTwo.Sec18.Item187NAut
import CFSG.RankThree.PartTwo.Sec16.Item166StepsProofSzGen
import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8YCfgAct

public section

namespace CFSG.RankThree.PartTwo.Sec18.Item187Proof

open CFSG CFSG.RankThree.PartTwo
open CFSG.ABGLocalTools (IsSylowOf)

section Cert113


private theorem coe_mem_fixedSubgroupOf_of_restrictAut {Y : Type*} [Group Y] (σ : MulAut Y)
    (K : Subgroup Y) (hK : K.map σ.toMonoidHom = K) {y : K}
    (hy : y ∈ fixedSubgroupOf (restrictAut σ K hK)) : (y : Y) ∈ fixedSubgroupOf σ := by
  rw [mem_fixedSubgroupOf] at hy ⊢
  have h := congrArg Subtype.val hy
  rwa [coe_restrictAut] at h

theorem layer_le_fixedSubgroupOf_sup {Y : Type} [Group Y] [Finite Y] (σ : MulAut Y)
    (hσ : σ ^ 3 = 1)
    (hcomp : ∀ K : Subgroup Y, IsComponent K → ∃ n, CFSG.Blueprint.SuzukiModel ↥K 2 n)
    (hinv : ∀ K : Subgroup Y, IsComponent K → K.map σ.toMonoidHom = K)
    {T : Subgroup Y} (hT : IsSylowOf 2 T ⊤) : layer Y ≤ fixedSubgroupOf σ ⊔ T := by
  rw [layer.eq_sSup]
  refine sSup_le fun K hK₀ => ?_
  have hK : IsComponent K := hK₀
  obtain ⟨n, hn⟩ := hcomp K hK
  obtain ⟨Q, hQ⟩ :=
    CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.YCfg.isSylowOf_inf_isSubnormal_top hT hK.2
  have hKσ : K.map σ.toMonoidHom = K := hinv K hK
  have hgen :=
    Sec16.kSzGen166 ↥K n hn (restrictAut σ K hKσ) (restrictAut_pow_three σ K hKσ hσ) Q
  have hle : (fixedSubgroupOf (restrictAut σ K hKσ) ⊔ (Q : Subgroup K)).map K.subtype
      ≤ fixedSubgroupOf σ ⊔ T := by
    rw [Subgroup.map_sup]
    refine sup_le ?_ ?_
    · rintro _ ⟨y, hy, rfl⟩
      exact Subgroup.mem_sup_left (coe_mem_fixedSubgroupOf_of_restrictAut σ K hKσ hy)
    · rw [hQ]
      exact inf_le_left.trans le_sup_right
  calc K = (⊤ : Subgroup K).map K.subtype := by
          rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    _ = (fixedSubgroupOf (restrictAut σ K hKσ) ⊔ (Q : Subgroup K)).map K.subtype := by
          rw [hgen]
    _ ≤ fixedSubgroupOf σ ⊔ T := hle

end Cert113

end CFSG.RankThree.PartTwo.Sec18.Item187Proof
