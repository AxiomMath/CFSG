module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9P5Data2
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9Amalgam
public import CFSG.Quasithin.Recognition.GoldschmidtStatement

public section

namespace CFSG.Quasithin.Fan86

open CFSG.Quasithin

variable {G : Type*} [Group G]

theorem closure_eq_top_of_subtype {K : Subgroup G} {S' : Set K} {S : Set G}
    (hS : K.subtype '' S' = S) (h : Subgroup.closure S = K) : Subgroup.closure S' = ⊤ := by
  apply Subgroup.map_injective K.subtype_injective
  rw [MonoidHom.map_closure, hS, h, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

theorem closure_eq_edge_of_subtype {K L : Subgroup G} {S' : Set L} {S : Set G}
    (hS : L.subtype '' S' = S) (h : Subgroup.closure S = K ⊓ L) :
    Subgroup.closure S' = (GoldAmalgam.ofSubgroupPair K L).edgeB := by
  apply Subgroup.map_injective L.subtype_injective
  rw [MonoidHom.map_closure, hS, h]
  unfold GoldAmalgam.edgeB GoldAmalgam.ofSubgroupPair
  rw [Subgroup.inclusion_range, Subgroup.map_subgroupOf_eq_of_le inf_le_right]

theorem amalgamLink_ofSubgroupPair {K L : Subgroup G} (a : K) (b : L) (h : (a : G) = b) :
    AmalgamLink (GoldAmalgam.ofSubgroupPair K L) a b :=
  ⟨⟨a, a.2, h ▸ b.2⟩, Subtype.ext rfl, Subtype.ext h⟩

structure PresData11 (Gα Gβ : Subgroup G) (x w za : G) (y z : Fin 5 → G)
    (xb t w1 w2 ub : G) (zm ym za' : Fin 3 → G) : Prop where
  memA : ∀ g ∈ (({x, w, za} : Set G) ∪ Set.range y ∪ Set.range z), g ∈ Gα
  memB : ∀ g ∈ (({xb, t, w1, w2, ub} : Set G) ∪ Set.range zm ∪ Set.range ym ∪ Set.range za'),
    g ∈ Gβ
  memE : ∀ g ∈ (({t, w1, w2, ub} : Set G) ∪ Set.range zm ∪ Set.range ym ∪ Set.range za'),
    g ∈ Gα
  genA : Subgroup.closure (({x, w, za} : Set G) ∪ Set.range y ∪ Set.range z) = Gα
  genB : Subgroup.closure
    (({xb, t, w1, w2, ub} : Set G) ∪ Set.range zm ∪ Set.range ym ∪ Set.range za') = Gβ
  genE : Subgroup.closure
    (({t, w1, w2, ub} : Set G) ∪ Set.range zm ∪ Set.range ym ∪ Set.range za') = Gα ⊓ Gβ
  rA : P1Rel x w za y z
  rB1 : P2Rel912 xb t w1 w2 ub zm ym za'
  rB2 : P2Rel913 0 0 xb t w1 w2 ub zm ym za'
  l_t : y 0 = t
  l_w1 : w = w1
  l_w2 : y 3 * y 4 * z 3 = w2
  l_ub : z 0 * z 4 * (z 2 * za) = ub
  l_zm0 : z 0 = zm 0
  l_zm1 : y 0 * (w ^ 2 * za) * y 0 = zm 1
  l_zm2 : w ^ 2 * za = zm 2
  l_ym0 : z 0 * z 1 = ym 0
  l_ym1 : z 0 * z 1 * (y 2 * z 2) = ym 1
  l_ym2 : y 2 * z 2 = ym 2
  l_za0 : za = za' 0
  l_za1 : z 2 * za = za' 1
  l_za2 : z 2 = za' 2

structure PresData12 (Gα Gβ : Subgroup G) (x w za c : G) (y z : Fin 5 → G)
    (xb t w1 w2 ub cb : G) (zm ym za' : Fin 3 → G) : Prop where
  memA : ∀ g ∈ (({x, w, za, c} : Set G) ∪ Set.range y ∪ Set.range z), g ∈ Gα
  memB : ∀ g ∈ (({xb, t, w1, w2, ub, cb} : Set G) ∪ Set.range zm ∪ Set.range ym ∪
    Set.range za'), g ∈ Gβ
  memE : ∀ g ∈ (({t, w1, w2, ub, cb} : Set G) ∪ Set.range zm ∪ Set.range ym ∪ Set.range za'),
    g ∈ Gα
  genA : Subgroup.closure (({x, w, za, c} : Set G) ∪ Set.range y ∪ Set.range z) = Gα
  genB : Subgroup.closure
    (({xb, t, w1, w2, ub, cb} : Set G) ∪ Set.range zm ∪ Set.range ym ∪ Set.range za') = Gβ
  genE : Subgroup.closure
    (({t, w1, w2, ub, cb} : Set G) ∪ Set.range zm ∪ Set.range ym ∪ Set.range za') = Gα ⊓ Gβ
  rA : P1Rel x w za y z
  rAc : P1cRel x za c y z
  rAwc : fcomm w c = 1
  rB1 : P2Rel912 xb t w1 w2 ub zm ym za'
  rB1c : P2cRel912 ub cb zm ym za'
  rB2 : P2Rel913 0 0 xb t w1 w2 ub zm ym za'
  rB2c : P2cRel913 0 xb t w1 w2 cb zm ym za'
  l_t : y 0 = t
  l_w1 : w = w1
  l_w2 : y 3 * y 4 * z 3 = w2
  l_ub : z 0 * z 4 * (z 2 * za) = ub
  l_zm0 : z 0 = zm 0
  l_zm1 : y 0 * (w ^ 2 * za) * y 0 = zm 1
  l_zm2 : w ^ 2 * za = zm 2
  l_ym0 : z 0 * z 1 = ym 0
  l_ym1 : z 0 * z 1 * (y 2 * z 2) = ym 1
  l_ym2 : y 2 * z 2 = ym 2
  l_za0 : za = za' 0
  l_za1 : z 2 * za = za' 1
  l_za2 : z 2 = za' 2
  l_c : c = cb

theorem admitsPres11_of_data {Gα Gβ : Subgroup G} {x w za : G} {y z : Fin 5 → G}
    {xb t w1 w2 ub : G} {zm ym za' : Fin 3 → G}
    (hd : PresData11 Gα Gβ x w za y z xb t w1 w2 ub zm ym za') :
    AdmitsPres11 (GoldAmalgam.ofSubgroupPair Gα Gβ) := by
  have hx : x ∈ Gα := hd.memA x (by simp)
  have hw : w ∈ Gα := hd.memA w (by simp)
  have hza : za ∈ Gα := hd.memA za (by simp)
  have hy : ∀ j, y j ∈ Gα := fun j => hd.memA (y j) (by simp)
  have hz : ∀ j, z j ∈ Gα := fun j => hd.memA (z j) (by simp)
  have hxb : xb ∈ Gβ := hd.memB xb (by simp)
  have ht : t ∈ Gβ := hd.memB t (by simp)
  have hw1 : w1 ∈ Gβ := hd.memB w1 (by simp)
  have hw2 : w2 ∈ Gβ := hd.memB w2 (by simp)
  have hub : ub ∈ Gβ := hd.memB ub (by simp)
  have hzm : ∀ i, zm i ∈ Gβ := fun i => hd.memB (zm i) (by simp)
  have hym : ∀ i, ym i ∈ Gβ := fun i => hd.memB (ym i) (by simp)
  have hza' : ∀ i, za' i ∈ Gβ := fun i => hd.memB (za' i) (by simp)
  refine ⟨⟨x, hx⟩, ⟨w, hw⟩, ⟨za, hza⟩, fun j => ⟨y j, hy j⟩, fun j => ⟨z j, hz j⟩,
    ⟨xb, hxb⟩, ⟨t, ht⟩, ⟨w1, hw1⟩, ⟨w2, hw2⟩, ⟨ub, hub⟩, fun i => ⟨zm i, hzm i⟩,
    fun i => ⟨ym i, hym i⟩, fun i => ⟨za' i, hza' i⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact P1Rel.of_injective Gα.subtype_injective hd.rA
  · exact P2Rel912.of_injective Gβ.subtype_injective hd.rB1
  · exact P2Rel913.of_injective Gβ.subtype_injective hd.rB2
  · refine closure_eq_top_of_subtype ?_ hd.genA
    simp only [Set.image_union, Set.image_insert_eq, Set.image_singleton, ← Set.range_comp]
    rfl
  · refine closure_eq_top_of_subtype ?_ hd.genB
    simp only [Set.image_union, Set.image_insert_eq, Set.image_singleton, ← Set.range_comp]
    rfl
  · refine closure_eq_edge_of_subtype ?_ hd.genE
    simp only [Set.image_union, Set.image_insert_eq, Set.image_singleton, ← Set.range_comp]
    rfl
  · exact ⟨amalgamLink_ofSubgroupPair _ _ hd.l_t, amalgamLink_ofSubgroupPair _ _ hd.l_w1,
      amalgamLink_ofSubgroupPair _ _ hd.l_w2, amalgamLink_ofSubgroupPair _ _ hd.l_ub,
      amalgamLink_ofSubgroupPair _ _ hd.l_zm0, amalgamLink_ofSubgroupPair _ _ hd.l_zm1,
      amalgamLink_ofSubgroupPair _ _ hd.l_zm2, amalgamLink_ofSubgroupPair _ _ hd.l_ym0,
      amalgamLink_ofSubgroupPair _ _ hd.l_ym1, amalgamLink_ofSubgroupPair _ _ hd.l_ym2,
      amalgamLink_ofSubgroupPair _ _ hd.l_za0, amalgamLink_ofSubgroupPair _ _ hd.l_za1,
      amalgamLink_ofSubgroupPair _ _ hd.l_za2⟩

theorem admitsPres12_of_data {Gα Gβ : Subgroup G} {x w za c : G} {y z : Fin 5 → G}
    {xb t w1 w2 ub cb : G} {zm ym za' : Fin 3 → G}
    (hd : PresData12 Gα Gβ x w za c y z xb t w1 w2 ub cb zm ym za') :
    AdmitsPres12 (GoldAmalgam.ofSubgroupPair Gα Gβ) := by
  have hx : x ∈ Gα := hd.memA x (by simp)
  have hw : w ∈ Gα := hd.memA w (by simp)
  have hza : za ∈ Gα := hd.memA za (by simp)
  have hc : c ∈ Gα := hd.memA c (by simp)
  have hy : ∀ j, y j ∈ Gα := fun j => hd.memA (y j) (by simp)
  have hz : ∀ j, z j ∈ Gα := fun j => hd.memA (z j) (by simp)
  have hxb : xb ∈ Gβ := hd.memB xb (by simp)
  have ht : t ∈ Gβ := hd.memB t (by simp)
  have hw1 : w1 ∈ Gβ := hd.memB w1 (by simp)
  have hw2 : w2 ∈ Gβ := hd.memB w2 (by simp)
  have hub : ub ∈ Gβ := hd.memB ub (by simp)
  have hcb : cb ∈ Gβ := hd.memB cb (by simp)
  have hzm : ∀ i, zm i ∈ Gβ := fun i => hd.memB (zm i) (by simp)
  have hym : ∀ i, ym i ∈ Gβ := fun i => hd.memB (ym i) (by simp)
  have hza' : ∀ i, za' i ∈ Gβ := fun i => hd.memB (za' i) (by simp)
  refine ⟨⟨x, hx⟩, ⟨w, hw⟩, ⟨za, hza⟩, ⟨c, hc⟩, fun j => ⟨y j, hy j⟩, fun j => ⟨z j, hz j⟩,
    ⟨xb, hxb⟩, ⟨t, ht⟩, ⟨w1, hw1⟩, ⟨w2, hw2⟩, ⟨ub, hub⟩, ⟨cb, hcb⟩, fun i => ⟨zm i, hzm i⟩,
    fun i => ⟨ym i, hym i⟩, fun i => ⟨za' i, hza' i⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · exact P1Rel.of_injective Gα.subtype_injective hd.rA
  · exact P1cRel.of_injective Gα.subtype_injective hd.rAc
  · exact Gα.subtype_injective (by rw [map_fcomm, map_one]; exact hd.rAwc)
  · exact P2Rel912.of_injective Gβ.subtype_injective hd.rB1
  · exact P2cRel912.of_injective Gβ.subtype_injective hd.rB1c
  · exact P2Rel913.of_injective Gβ.subtype_injective hd.rB2
  · exact P2cRel913.of_injective Gβ.subtype_injective hd.rB2c
  · refine closure_eq_top_of_subtype ?_ hd.genA
    simp only [Set.image_union, Set.image_insert_eq, Set.image_singleton, ← Set.range_comp]
    rfl
  · refine closure_eq_top_of_subtype ?_ hd.genB
    simp only [Set.image_union, Set.image_insert_eq, Set.image_singleton, ← Set.range_comp]
    rfl
  · refine closure_eq_edge_of_subtype ?_ hd.genE
    simp only [Set.image_union, Set.image_insert_eq, Set.image_singleton, ← Set.range_comp]
    rfl
  · exact ⟨amalgamLink_ofSubgroupPair _ _ hd.l_t, amalgamLink_ofSubgroupPair _ _ hd.l_w1,
      amalgamLink_ofSubgroupPair _ _ hd.l_w2, amalgamLink_ofSubgroupPair _ _ hd.l_ub,
      amalgamLink_ofSubgroupPair _ _ hd.l_zm0, amalgamLink_ofSubgroupPair _ _ hd.l_zm1,
      amalgamLink_ofSubgroupPair _ _ hd.l_zm2, amalgamLink_ofSubgroupPair _ _ hd.l_ym0,
      amalgamLink_ofSubgroupPair _ _ hd.l_ym1, amalgamLink_ofSubgroupPair _ _ hd.l_ym2,
      amalgamLink_ofSubgroupPair _ _ hd.l_za0, amalgamLink_ofSubgroupPair _ _ hd.l_za1,
      amalgamLink_ofSubgroupPair _ _ hd.l_za2⟩
  · exact amalgamLink_ofSubgroupPair _ _ hd.l_c

end CFSG.Quasithin.Fan86
