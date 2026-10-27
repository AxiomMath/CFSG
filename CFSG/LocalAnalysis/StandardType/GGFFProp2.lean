module

public import CFSG.LocalAnalysis.StandardType.GGFFP51
public import CFSG.LocalAnalysis.StandardType.GGFFModelSL
public import CFSG.LocalAnalysis.StandardType.GGResFFDefs
public import CFSG.LocalAnalysis.StandardType.GGTypeANbrLabels
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyAut
public import CFSG.Adapters.StatedSLTwoField
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowFWreath
public import CFSG.LocalAnalysis.StandardType.GGFFModelNDefs
import CFSG.LocalAnalysis.StandardType.GGFFModelN
import CFSG.LocalAnalysis.StandardType.GGFFModelSLN
import CFSG.LocalAnalysis.StandardType.GGFFEleven

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

public section

namespace CFSG.StandardType.GGFF

open CFSG.Assembly
open CFSG.RankThree.PartTwo.Sec21.FF79 (Cen)
open CFSG.RankThree.PartTwo.Sec21.FF81 (autOrder)
open CFSG.RankThree.PartTwo.Sec4.Item434Kit (vecElt)
open CFSG.RankThree.PartTwo.Sec4.RonanK429F
open scoped MatrixGroups

variable {G : Type} [Group G]

theorem card_ggAutomizer_top (B : Subgroup G) : Nat.card (ggAutomizer ⊤ B) = autOrder B := by
  have hr : B.normalizerMonoidHom.range = ggAutomizer ⊤ B := by
    ext φ
    rw [mem_ggAutomizer_iff, MonoidHom.mem_range]
    constructor
    · rintro ⟨u, rfl⟩
      exact ⟨u, Subgroup.mem_top _, u.2, fun x => rfl⟩
    · rintro ⟨g, -, hg, hφ⟩
      exact ⟨⟨g, hg⟩, MulEquiv.ext fun x => Subtype.ext (hφ x).symm⟩
  rw [← hr, autOrder, Subgroup.relIndex, ← Subgroup.normalizerMonoidHom_ker, Subgroup.index_ker]

theorem exists_model {K : Type} [Group K]
    (hK : GGHasLabel ⟨.A, 5, 1⟩ K ∨ GGHasLabel ⟨.A, 6, 1⟩ K) :
    ∃ z : Fin 3 → K, Model K z ∧ ModelN K z := by
  rcases hK with h5 | h6'
  · obtain ⟨e⟩ := CFSG.Open.StatedAPI.nonempty_mulEquiv_specialLinear_zmod_two_of_psl
      (statedClassicalModel_of_hasLabel_typeA (by simp [LargeEvenInLambda2]) h5)
    exact ⟨_, model_SL6.ofMulEquiv e.symm, modelN_SL6.ofMulEquiv e.symm⟩
  · obtain ⟨e⟩ := CFSG.Open.StatedAPI.nonempty_mulEquiv_specialLinear_zmod_two_of_psl
      (statedClassicalModel_of_hasLabel_typeA (by simp [LargeEvenInLambda2]) h6')
    exact ⟨_, model_SL7.ofMulEquiv e.symm, modelN_SL7.ofMulEquiv e.symm⟩

theorem ggFFLinearProp2Input_holds : GGFFLinearProp2Input := by
  intro G _ _ b K B₁ hb hKC hKN hlab hB₁K hB₁ hB₁card hcyc hmeet hchar
  obtain ⟨z₀, hz₀, hN₀⟩ := exists_model hlab
  have hFc : Nat.card (B₁.subgroupOf K) = 27 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hB₁K).toEquiv, hB₁card]
    norm_num
  obtain ⟨g, hg⟩ := hz₀.torus _ (hB₁.subgroupOf K) hFc
  set z : Fin 3 → K := fun i => g * z₀ i * g⁻¹ with hzdef
  have hnor : ∀ c ∈ Cen b, ∀ k ∈ K, c * k * c⁻¹ ∈ K := fun c hc k hk => by
    have := hKN.conj_mem ⟨k, hKC hk⟩ (Subgroup.mem_subgroupOf.mpr hk) ⟨c, hc⟩
    exact Subgroup.mem_subgroupOf.mp this
  have hset : Setting b K z := ⟨⟨hb, hKC, hnor, hz₀.conj g, hcyc⟩, hmeet⟩
  have hv : ∀ v, vecElt z v = g * vecElt z₀ v * g⁻¹ := fun v =>
    vecElt_map (MulAut.conj g) z₀ v
  have htor : tor (zs z) = B₁ := by
    ext x
    rw [hset.mem_torG]
    constructor
    · rintro ⟨v, rfl⟩
      have := (hg (g * vecElt z₀ v * g⁻¹)).mpr ⟨v, rfl⟩
      rw [Subgroup.mem_subgroupOf] at this
      rwa [SettingCore.vecElt_zs, hv]
    · intro hx
      obtain ⟨v, hxv⟩ := (hg ⟨x, hB₁K hx⟩).mp (Subgroup.mem_subgroupOf.mpr hx)
      refine ⟨v, ?_⟩
      rw [SettingCore.vecElt_zs, hv, ← hxv]
  have hBt : Subgroup.closure {b} ⊔ B₁ = Bt b z := by
    rw [← Subgroup.zpowers_eq_closure, ← htor]
    rfl
  rw [hBt, card_ggAutomizer_top]
  rcases hset.autOrder_cases with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exact absurd h (hset.autOrder_ne_1440 (hN₀.conj g) hchar)

end CFSG.StandardType.GGFF

end
