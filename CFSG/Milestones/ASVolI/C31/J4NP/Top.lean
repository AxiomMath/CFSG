module

public import CFSG.Milestones.ASVolI.C31.J4NP.TopNode
public import CFSG.Milestones.ASVolI.C31.J4NP.Is2AGlue
public import Certificates.Certificate7890
public import Certificates.Certificate7891
public import Certificates.Certificate7892
public import Certificates.Certificate7893
public import Certificates.Certificate7894
public import Certificates.Certificate7895
public import Certificates.Certificate7896
public import Certificates.Certificate7897
public import Certificates.Certificate7898
public import CFSG.Milestones.ASVolI.C31.J4NP.Base
public import CFSG.Milestones.ASVolI.C31.J4NP.Is2A

public section

namespace CFSG.ASVolI

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2 CFSG.J4Tree.Native

theorem burnsideJ4NP_top_card_C_Rep_one :
    Nat.card ↥(Hj ⊓ Subgroup.centralizer (burnsideJ4NP_Rep 1 : Set J)) = 283115520 := by
  have hF := j4Facts
  have hM := hF.mat
  have hb : treeBasis 1 = [(1131, 0)] := by decide +kernel
  have hR : burnsideJ4NP_Rep 1 = Subgroup.closure {eta uJ 11 1131} := by
    rw [burnsideJ4NP_top_Rep_eq]
    refine congrArg Subgroup.closure (Set.ext fun g => ?_)
    simp only [burnsideJ4NP_topRepElts, hb, List.map_cons, List.map_nil, List.mem_singleton,
      Set.mem_setOf_eq, Set.mem_singleton_iff, burnsideJ4NP_treeElt, burnsideJ4NP_Kel_zero, mul_one]
  rw [hR, Subgroup.centralizer_closure, inf_comm]
  have h := card_eq_card_mul_centralizer Hj (eta uJ 11 1131) Zl z0_mem_Zl
    (fun h hh x hx => (Zl_conj hM h hh).1 x hx) (fun x hx => Zl_trans hM _ z0_mem_Zl x hx)
  rw [card_Hj hF, card_Zl hM] at h
  omega

theorem burnsideJ4NP_treeTopKids_cover :
    ∀ k ∈ treeTopKids, ∃ t ∈ treeTopIds, k ∈ burnsideJ4NP_topKids t := by decide

theorem burnsideJ4NP_aff2A :
    burnsideJ4NP_Aff2A := by
  intro x hx hne h2A
  have hsq : x * x = 1 := by
    obtain ⟨g, rfl⟩ := h2A
    calc g * CFSG.Quasithin.J4Loc.z0 * g⁻¹ * (g * CFSG.Quasithin.J4Loc.z0 * g⁻¹)
        = g * (CFSG.Quasithin.J4Loc.z0 * CFSG.Quasithin.J4Loc.z0) * g⁻¹ := by group
      _ = 1 := by rw [burnsideJ4NP_z0_sq]; group
  have := (burnsideJ4NP_Is2A_iff_affine_H hx hsq hne).mp h2A
  rw [burnsideJ4NP_affine2A_eq_with] at this
  rw [burnsideJ4NP_encJ_of_mem hx]
  exact this

section Facts


theorem burnsideJ4NP_top_nodes :
    ∀ k ∈ treeTopIds, burnsideJ4NP_TreeStep k ∧
      ∀ k' ∈ burnsideJ4NP_topKids k,
        Nat.card ↥(Hj ⊓ Subgroup.centralizer (burnsideJ4NP_Rep k' : Set J)) = treeOrd k' := by
  have ha := burnsideJ4NP_aff2A
  have n1 := Certificates.certificate7890 ha
    (burnsideJ4NP_top_card_C_Rep_one.trans (by decide +kernel))
  have n2 := Certificates.certificate7891 ha (n1.2 2 (by decide))
  have n3 := Certificates.certificate7892 ha (n1.2 3 (by decide))
  have n4 := Certificates.certificate7893 ha (n1.2 4 (by decide))
  have n7 := Certificates.certificate7894 ha (n1.2 7 (by decide))
  have n107 := Certificates.certificate7895 ha (n3.2 107 (by decide))
  have n124 := Certificates.certificate7896 ha (n2.2 124 (by decide))
  have n129 := Certificates.certificate7897 ha (n2.2 129 (by decide))
  have n134 := Certificates.certificate7898 ha (n4.2 134 (by decide))
  intro k hk
  simp only [treeTopIds, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact n1
  · exact n2
  · exact n3
  · exact n4
  · exact n7
  · exact n107
  · exact n124
  · exact n129
  · exact n134

theorem burnsideJ4NP_topFacts : burnsideJ4NP_TopFacts := by
  refine ⟨fun k hk => (burnsideJ4NP_top_nodes k hk).1, fun k hk => ?_⟩
  obtain ⟨t, ht, hkt⟩ := burnsideJ4NP_treeTopKids_cover k hk
  exact (burnsideJ4NP_top_nodes t ht).2 k hkt

end Facts

end CFSG.ASVolI
