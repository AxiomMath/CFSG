module

public import Certificates.Certificate7900
public import Certificates.Certificate7901
public import Certificates.Certificate7902
public import Certificates.Certificate7903
public import Certificates.Certificate7904

public section

namespace CFSG.ASVolI

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT CFSG.J4Tree.Native CFSG.J4Tree.Native.Col

theorem burnsideJ4NP_colIds0_eq : colChunk0.map VNode.k = burnsideJ4NP_colIds0 := by
  decide +kernel

theorem burnsideJ4NP_colIds1_eq : colChunk1.map VNode.k = burnsideJ4NP_colIds1 := by
  decide +kernel

theorem burnsideJ4NP_colIds2_eq : colChunk2.map VNode.k = burnsideJ4NP_colIds2 := by
  decide +kernel

theorem burnsideJ4NP_colIds3_eq : colChunk3.map VNode.k = burnsideJ4NP_colIds3 := by
  decide +kernel

section Chunks


theorem burnsideJ4NP_verdictW_col :
    ∀ d ∈ colNodes, burnsideJ4NP_VerdictW (burnsideJ4NP_Wv d.k) := by
  intro d hd
  unfold colNodes at hd
  simp only [List.mem_append] at hd
  rcases hd with ((h0 | h1) | h2) | h3
  · refine Certificates.certificate7900 d.k ?_
    rw [← burnsideJ4NP_colIds0_eq]
    exact List.mem_map_of_mem h0
  · refine Certificates.certificate7901 d.k ?_
    rw [← burnsideJ4NP_colIds1_eq]
    exact List.mem_map_of_mem h1
  · refine Certificates.certificate7902 d.k ?_
    rw [← burnsideJ4NP_colIds2_eq]
    exact List.mem_map_of_mem h2
  · refine Certificates.certificate7903 d.k ?_
    rw [← burnsideJ4NP_colIds3_eq]
    exact List.mem_map_of_mem h3

end Chunks

@[expose] def burnsideJ4NP_colIds : List ℕ := colNodes.map VNode.k

section Ids


theorem burnsideJ4NP_verdictW_colIds :
    ∀ k ∈ burnsideJ4NP_colIds, burnsideJ4NP_VerdictW (burnsideJ4NP_Wv k) := by
  intro k hk
  obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hk
  exact burnsideJ4NP_verdictW_col d hd

theorem burnsideJ4NP_verdictWH_colIds :
    ∀ k ∈ burnsideJ4NP_colIds, burnsideJ4NP_VerdictWH (burnsideJ4NP_Wv k) := fun k hk =>
  burnsideJ4NP_verdictWH_of_verdictW (burnsideJ4NP_verdictW_colIds k hk)

end Ids

section Union


theorem burnsideJ4NP_normalizer_le_union :
    ∀ d ∈ colUnionNodes, Subgroup.normalizer (burnsideJ4NP_Wv d.k : Set J) ≤
      Subgroup.normalizer ((Subgroup.closure (burnsideJ4NP_colO d) : Subgroup J) : Set J) :=
  Certificates.certificate7904

theorem burnsideJ4NP_normalizer_le_union136 :
    Subgroup.normalizer (burnsideJ4NP_Wv 136 : Set J) ≤
      Subgroup.normalizer ((Subgroup.closure
        ((fun o => eta (burnsideJ4NP_colBasis 136) (treeWv 136).length o) ''
          {o | o ∈ [2, 8, 10, 16, 18, 24, 26, 128, 130, 136, 138, 144, 146, 152, 154]}) :
        Subgroup J) : Set J) :=
  burnsideJ4NP_normalizer_le_union
    ⟨136, 1, 0, [2, 8, 10, 16, 18, 24, 26, 128, 130, 136, 138, 144, 146, 152, 154], ""⟩
    (by unfold colUnionNodes; exact List.mem_cons_self ..)

theorem burnsideJ4NP_normalizer_le_union266 :
    Subgroup.normalizer (burnsideJ4NP_Wv 266 : Set J) ≤
      Subgroup.normalizer ((Subgroup.closure
        ((fun o => eta (burnsideJ4NP_colBasis 266) (treeWv 266).length o) ''
          {o | o ∈ [31, 36, 59, 76, 83, 104, 119, 139, 148, 175, 176, 199, 216, 227, 252]}) :
        Subgroup J) : Set J) :=
  burnsideJ4NP_normalizer_le_union
    ⟨266, 1, 0, [31, 36, 59, 76, 83, 104, 119, 139, 148, 175, 176, 199, 216, 227, 252], ""⟩
    (by unfold colUnionNodes; exact List.mem_cons_of_mem _ (List.mem_cons_self ..))

end Union

end CFSG.ASVolI
