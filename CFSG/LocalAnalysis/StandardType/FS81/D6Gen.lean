module

public import CFSG.LocalAnalysis.StandardType.FS81.Defs
public import CFSG.LocalAnalysis.StandardType.FS81.FrameEm
public import CFSG.LocalAnalysis.StandardType.GGFrameFSxOrth
public import CFSG.ClassicalInvolution.WeakCT.SpinPlusTwo
public import CFSG.Adapters.LieModelOrders
public import CFSG.RankThree.PartOne.KF.ClsOmega

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Assembly CFSG.ClassicalInvolution.WeakCT CFSG.Timmesfeld CFSG.LieType
open CFSG.Blueprint

theorem iSup_eq_of_D6_frame {G : Type} [Group G] [Finite G] {K : Subgroup G}
    (hK : IsRow Row.D6 K) (hZ : Subgroup.center K = ⊥) (U : Fin 6 → Subgroup G)
    (hUK : ∀ k, U k ≤ K)
    (hcomm : ∀ i j : Fin 6, i ≠ j → ¬ CFSG.Timmesfeld.edgeD 6 i j →
      ¬ CFSG.Timmesfeld.edgeD 6 j i → ∀ a ∈ U i, ∀ b ∈ U j, a * b = b * a)
    (hpair : ∀ i j : Fin 6, CFSG.Timmesfeld.edgeD 6 i j →
      ∃ W, CFSG.ClassicalInvolution.WeakCT.LinearBlockStandardPair (ZMod 2) W (U i) (U j)) :
    ⨆ k, U k = K := by
  classical
  set Y := ⨆ k, U k with hY
  have hUY : ∀ k, U k ≤ Y := fun k => le_iSup U k
  have hYK : Y ≤ K := iSup_le hUK
  have hgen : ⨆ k, (U k).subgroupOf Y = ⊤ := by
    apply Subgroup.map_injective Y.subtype_injective
    rw [Subgroup.map_iSup, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    simp_rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left (hUY _)]
    exact hY.symm
  have hcommY : ∀ i j : Fin 6, i ≠ j → ¬ edgeD 6 i j → ¬ edgeD 6 j i →
      ∀ a ∈ (U i).subgroupOf Y, ∀ b ∈ (U j).subgroupOf Y, a * b = b * a :=
    fun i j hij h1 h2 a ha b hb => Subtype.ext (hcomm i j hij h1 h2 a ha b hb)
  have hpairY : ∀ i j : Fin 6, edgeD 6 i j →
      ∃ W, LinearBlockStandardPair (ZMod 2) W ((U i).subgroupOf Y) ((U j).subgroupOf Y) :=
    fun i j hij => by
      obtain ⟨W, hW⟩ := hpair i j hij
      exact ⟨_, linearBlockStandardPair_subgroupOf (hUY i) (hUY j) hW⟩
  obtain ⟨-, -, -, -, -, hlieY⟩ :=
    weakCT_spinPlus_two (n := 6) (by norm_num) (F := ZMod 2) (Nat.card_zmod 2)
      (fun k => (U k).subgroupOf Y) hgen hcommY hpairY
  have hYquot : Nat.card (↥Y ⧸ Subgroup.center ↥Y) =
      CFSG.EvenSmallLie.CatalogOrders.lieOrd .POmegaPlus 6 (2 ^ 1) :=
    hlieY.card_eq_lieOrd (by norm_num)
  have hm : LargeEvenMarking ↥K
      (fun lab _ _ _ _ _ => lab.tag = .D ∧ lab.rank = 6 ∧ lab.n = 1) := by
    refine CFSG.StandardType.largeEvenMarking_mono (fun lab R _ I F θ hlab => ?_) hK
    obtain ⟨hn, ⟨-, ht, hr⟩ | ⟨h, -⟩ | ⟨h, -⟩⟩ := hlab
    · exact ⟨ht, hr, hn⟩
    · exact absurd h (by decide)
    · exact absurd h (by decide)
  obtain ⟨eK⟩ := CFSG.StandardType.FrameRoute.nonempty_mulEquiv_omegaPlusSix_of_marking hm hZ
  have hbot : (CFSG.Open.StatedScalars (Fin 6 ⊕ Fin 6) (ZMod 2)).subgroupOf
      (CFSG.Open.StatedOmega (CFSG.Open.StatedQuadPlus 6 (ZMod 2))) = ⊥ :=
    CFSG.RankThree.PartOne.KFU.statedScalars_subgroupOf_statedOmega_quadPlus_eq_bot
      (K := ZMod 2) (n := 6) (by norm_num)
  have hSCOmega : CFSG.Open.StatedClassicalModel
      (CFSG.Open.StatedOmega (CFSG.Open.StatedQuadPlus 6 (ZMod 2)))
      .POmegaPlus 6 2 1 :=
    ⟨⟨Nat.prime_two, le_rfl, by norm_num⟩, ZMod 2, inferInstance, inferInstance,
      by rw [Nat.card_zmod]; norm_num,
      ⟨CFSG.RankThree.PartOne.KFU.equivProjOfScalarsBot _ hbot⟩⟩
  have hLieOmega : CFSG.Blueprint.LieModel
      (CFSG.Open.StatedOmega (CFSG.Open.StatedQuadPlus 6 (ZMod 2)))
      .POmegaPlus 6 2 1 := Or.inl ⟨by decide, hSCOmega⟩
  have hKlie : CFSG.Blueprint.LieModel ↥K .POmegaPlus 6 2 1 :=
    CFSG.Blueprint.LieModel.of_mulEquiv eK.symm hLieOmega
  have hKcard : Nat.card ↥K =
      CFSG.EvenSmallLie.CatalogOrders.lieOrd .POmegaPlus 6 (2 ^ 1) :=
    hKlie.card_eq_lieOrd (by norm_num)
  have hYle : Nat.card ↥K ≤ Nat.card ↥Y := by
    rw [hKcard, ← hYquot]
    exact Nat.card_le_card_of_surjective _ (QuotientGroup.mk'_surjective (Subgroup.center ↥Y))
  have hEq : Y = K := Subgroup.eq_of_le_of_card_ge hYK hYle
  simpa only [hY] using hEq

end CFSG.StandardType.FrameRoute.FS81
