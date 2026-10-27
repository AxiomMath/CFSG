module

public import CFSG.RankThree.GF2n.Smith81.TiFusion
public import CFSG.RankThree.GF2n.Tim81.FStarSimple
public import CFSG.RankThree.GF2n.Smith81.Bridge

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80
open scoped commutatorElement

variable {G : Type} [Group G]

section FStar

variable [Finite G] {M Q Z : Subgroup G}

private theorem inf_center_ne_bot_of_normalized {T U : Subgroup G} (hT : IsPGroup 2 T)
    (hUT : U ≤ T) (hUn : T ≤ Subgroup.normalizer (U : Set G)) (hU : U ≠ ⊥) :
    U ⊓ (T ⊓ Subgroup.centralizer (T : Set G)) ≠ ⊥ := by
  have : Group.IsNilpotent T := hT.isNilpotent
  have hnormal : (U.subgroupOf T).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hUn
  have hne : U.subgroupOf T ≠ ⊥ := by
    intro h
    apply hU
    rw [← Subgroup.map_subgroupOf_eq_of_le hUT, h, Subgroup.map_bot]
  obtain ⟨⟨y, hy⟩, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hne)
  have hyC : (y : G) ∈ Subgroup.centralizer (T : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hy.2 ⟨t, ht⟩)
  intro h
  have hmem : (y : G) ∈ U ⊓ (T ⊓ Subgroup.centralizer (T : Set G)) := ⟨hy.1, y.2, hyC⟩
  rw [h, Subgroup.mem_bot] at hmem
  exact hy1 (Subtype.ext (Subtype.ext hmem))

theorem exists_component_eq_generalizedFitting (H : StrothHyp M Q Z) :
    ∃ K : Subgroup G, IsComponent K ∧ generalizedFitting G = K ∧ Z ≤ K := by
  have hT := H.toTim81Hyp
  obtain ⟨T, hTM, hQT⟩ := hT.exists_sylow_le_M
  obtain ⟨K, hK⟩ := hT.exists_isComponent H.q4
  have hF : fittingSubgroup G = ⊥ := hT.fittingSubgroup_eq_bot H.q4
  have hlayer : generalizedFitting G = K := by
    rw [Tim81.generalizedFitting_eq_layer_of_fittingSubgroup_eq_bot hF]
    exact le_antisymm (sSup_le fun L hL => (hT.unique_component H.q4 hK hL).le)
      (CFSG.LocalCores.component_le_layer hK)
  have hKn : K.Normal := by
    rw [← hlayer]
    exact (CFSG.LocalCores.generalized_fitting_characteristic).2
  have hne : (T : Subgroup G) ⊓ K ≠ ⊥ := hT.sylow_inf_component_ne_bot H.q4 T hK
  have hTn : (T : Subgroup G) ≤
      Subgroup.normalizer (((T : Subgroup G) ⊓ K : Subgroup G) : Set G) := by
    intro t ht
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      exact Subgroup.mem_inf.mpr ⟨(T : Subgroup G).mul_mem ((T : Subgroup G).mul_mem ht
        (Subgroup.mem_inf.mp hx).1) ((T : Subgroup G).inv_mem ht),
        hKn.conj_mem x (Subgroup.mem_inf.mp hx).2 t⟩
    · intro hx
      obtain ⟨hxT, hxK⟩ := Subgroup.mem_inf.mp hx
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · have := (T : Subgroup G).mul_mem ((T : Subgroup G).mul_mem ((T : Subgroup G).inv_mem ht)
          hxT) ht
        simpa [mul_assoc] using this
      · have := hKn.conj_mem _ hxK t⁻¹
        simpa [mul_assoc] using this
  obtain ⟨⟨y, hy⟩, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (inf_center_ne_bot_of_normalized T.isPGroup' inf_le_left hTn hne)
  obtain ⟨⟨hyT, hyK⟩, hyTT, hyC⟩ := (by simpa [Subgroup.mem_inf] using hy :
    (y ∈ (T : Subgroup G) ∧ y ∈ K) ∧ y ∈ (T : Subgroup G) ∧
      y ∈ Subgroup.centralizer ((T : Subgroup G) : Set G))
  have hQT' : Q ≤ (T : Subgroup G) := H.hQ ▸ hQT
  have hyZ : y ∈ Z := by
    rw [← H.centralizer_Q]
    exact Subgroup.centralizer_le hQT' hyC
  have hy1' : y ≠ 1 := fun h => hy1 (Subtype.ext h)
  refine ⟨K, hK, hlayer, fun z hz => ?_⟩
  by_cases hz1 : z = 1
  · rw [hz1]; exact K.one_mem
  · obtain ⟨m, -, hm⟩ := Z_isConj H hyZ hy1' hz hz1
    rw [← hm]
    exact hKn.conj_mem y hyK m

theorem generalizedFitting_eq_normalClosure (H : StrothHyp M Q Z) {z : G} (hz : z ∈ Z)
    (hz1 : z ≠ 1) :
    generalizedFitting G = Subgroup.normalClosure ({z} : Set G) ∧
      IsComponent (Subgroup.normalClosure ({z} : Set G)) := by
  obtain ⟨K, hK, hFK, hZK⟩ := exists_component_eq_generalizedFitting H
  have hF : fittingSubgroup G = ⊥ := H.toTim81Hyp.fittingSubgroup_eq_bot H.q4
  have hsimple : IsSimpleGroup K := (Tim81.component_isSimple hF hK).1
  have hKn : K.Normal := by
    rw [← hFK]
    exact (CFSG.LocalCores.generalized_fitting_characteristic).2
  have hzK : z ∈ K := hZK hz
  have hUK : Subgroup.normalClosure ({z} : Set G) = K := by
    apply le_antisymm
    · exact Subgroup.normalClosure_le_normal (by simpa using hzK)
    · have hne : (Subgroup.normalClosure ({z} : Set G)).subgroupOf K ≠ ⊥ := by
        intro hbot
        have hmem : (⟨z, hzK⟩ : K) ∈ (Subgroup.normalClosure ({z} : Set G)).subgroupOf K :=
          Subgroup.mem_subgroupOf.mpr (Subgroup.subset_normalClosure rfl)
        rw [hbot, Subgroup.mem_bot] at hmem
        exact hz1 (congrArg Subtype.val hmem)
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
        ((Subgroup.normalClosure ({z} : Set G)).subgroupOf K) with h | h
      · exact absurd h hne
      · exact Subgroup.subgroupOf_eq_top.mp h
  rw [hUK]
  exact ⟨hFK, hK⟩

theorem center_normalClosure_eq_bot (H : StrothHyp M Q Z) {z : G} (hz : z ∈ Z) (hz1 : z ≠ 1) :
    Subgroup.center ↥(Subgroup.normalClosure ({z} : Set G)) = ⊥ :=
  Tim81.center_component_eq_bot (H.toTim81Hyp.fittingSubgroup_eq_bot H.q4)
    (generalizedFitting_eq_normalClosure H hz hz1).2

end FStar

end CFSG.RankThree.GF2n.Smith81
