module

public import CFSG.LocalAnalysis.StandardType.GGQTwoD6CardALDefs
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyAut

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module QTwoLin

private theorem ggQ2d6l_false_of_int_cartan {Γ : Type} {M : CoxeterMatrix Γ}
    {C : Matrix Γ Γ ℤ} (hC : GGIntCartan M C) {j k : Γ} (hjk : j ≠ k) (hCne0 : C j k ≠ 0)
    (hajk : (C j k : ZMod 3) = 0) (hakj : (C k j : ZMod 3) = 0) : False := by
  have hdvd_jk : (3 : ℤ) ∣ C j k := (ZMod.intCast_zmod_eq_zero_iff_dvd (C j k) 3).mp hajk
  have hdvd_kj : (3 : ℤ) ∣ C k j := (ZMod.intCast_zmod_eq_zero_iff_dvd (C k j) 3).mp hakj
  rcases hC.2 j k hjk with ⟨-, h1, -⟩ | ⟨-, h1, -⟩ | ⟨-, hprod, -, -⟩ | ⟨-, hprod, -, -⟩
  · exact hCne0 h1
  · rw [h1] at hdvd_jk
    exact absurd hdvd_jk (by norm_num)
  · have h9 : (3 * 3 : ℤ) ∣ 2 := by
      have h : (3 * 3 : ℤ) ∣ C j k * C k j := mul_dvd_mul hdvd_jk hdvd_kj
      rwa [hprod] at h
    exact absurd h9 (by norm_num)
  · have h9 : (3 * 3 : ℤ) ∣ 3 := by
      have h : (3 * 3 : ℤ) ∣ C j k * C k j := mul_dvd_mul hdvd_jk hdvd_kj
      rwa [hprod] at h
    exact absurd h9 (by norm_num)

theorem ggQ2d6l_adjacent_noncomm {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} [Fact (Nat.Prime 3)] (hS : GGQTwoSetting 3 B Bs x L D J) {y' : G}
    {K' : Subgroup G} (M' : GGQTwoModel 3 Bs x y' D L J K') (j k : M'.ι) (hj : j ≠ M'.a)
    (hk : k ≠ M'.a) (hjk : j ≠ k) (hC : M'.cartan j k ≠ 0) (hne : M'.simple j ≠ M'.simple k) :
    M'.simple j * M'.simple k ≠ M'.simple k * M'.simple j := by
  intro hcomm
  have hfj : M'.root j (M'.coroot j) = 2 := by
    rw [M'.pairing j j, M'.isCartan.1 j]
    norm_num
  have hfk : M'.root k (M'.coroot k) = 2 := by
    rw [M'.pairing k k, M'.isCartan.1 k]
    norm_num
  have hLj : ggLin (p := 3) M'.model (M'.simple j) = reflection hfj :=
    ggLin_eq_reflection M'.model hfj (fun v => M'.simple_apply j v)
  have hLk : ggLin (p := 3) M'.model (M'.simple k) = reflection hfk :=
    ggLin_eq_reflection M'.model hfk (fun v => M'.simple_apply k v)
  have hcommLin : reflection hfj * reflection hfk = reflection hfk * reflection hfj := by
    have h := congrArg (ggLin (p := 3) M'.model) hcomm
    simpa only [map_mul, hLj, hLk] using h
  have hmem_j : M'.simple j ∈ ggAutomizer L Bs := by
    rw [M'.automizer_L]
    exact Subgroup.subset_closure ⟨j, hj, rfl⟩
  have hmem_k : M'.simple k ∈ ggAutomizer L Bs := by
    rw [M'.automizer_L]
    exact Subgroup.subset_closure ⟨k, hk, rfl⟩
  have hφ : M'.simple j ∈ ggInduced ⊤ Bs := by
    obtain ⟨g, hgL, hgN, hg⟩ := mem_ggAutomizer_iff.mp hmem_j
    exact ⟨g, Subgroup.mem_top g, hgN, hg⟩
  have hψ : M'.simple k ∈ ggInduced ⊤ Bs := by
    obtain ⟨g, hgL, hgN, hg⟩ := mem_ggAutomizer_iff.mp hmem_k
    exact ⟨g, Subgroup.mem_top g, hgN, hg⟩
  by_cases hind : LinearIndependent (ZMod 3) ![M'.coroot j, M'.coroot k]
  ·
    have hajk : M'.root j (M'.coroot k) = 0 :=
      ggReflection_comm_cross_eq_zero (p := 3) (V := M'.V) (by decide) hfj hfk hind hcommLin
    have hind' : LinearIndependent (ZMod 3) ![M'.coroot k, M'.coroot j] := by
      rw [LinearIndependent.pair_iff] at hind ⊢
      intro a b h
      obtain ⟨hb, ha⟩ := hind b a (by rw [add_comm]; exact h)
      exact ⟨ha, hb⟩
    have hakj : M'.root k (M'.coroot j) = 0 :=
      ggReflection_comm_cross_eq_zero (p := 3) (V := M'.V) (by decide) hfk hfj hind'
        hcommLin.symm
    have hajk' : (M'.cartan j k : ZMod 3) = 0 := by
      rw [← M'.pairing j k]
      exact hajk
    have hakj' : (M'.cartan k j : ZMod 3) = 0 := by
      rw [← M'.pairing k j]
      exact hakj
    exact ggQ2d6l_false_of_int_cartan M'.isCartan hjk hC hajk' hakj'
  ·
    have hNT : GGNoTransvection 3 Bs := hS.1.2.2.2.1
    have hindep := (ggReflection_linearIndependent_of_noTransvection (p := 3) (by decide)
      hNT M'.model hφ hψ hne hfj hfk hLj hLk).1
    exact hind hindep

end CFSG.StandardType

end

