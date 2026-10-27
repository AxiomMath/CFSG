module

public import CFSG.Quasithin.Vol2.Ch11SecKGBCa
public import CFSG.Quasithin.Background.E2Two
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.C25RankOne
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKBender

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB.C10KG

open CFSG.Open CFSG.QuasithinUnique

variable {Y Y' : Type} [Group Y] [Group Y']

theorem exists_sylow_of_isSylowTwoOf {S : Subgroup Y'} (hS : IsSylowTwoOf S ⊤) :
    ∃ Q : Sylow 2 Y', (Q : Subgroup Y') = S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hidx : ¬ 2 ∣ S.index := by
    have h : ¬ 2 ∣ (S.subgroupOf ⊤).index := hS.2.2
    rwa [show (S.subgroupOf ⊤).index = S.index from Subgroup.relIndex_top_right _] at h
  exact ⟨hS.2.1.toSylow hidx, rfl⟩

theorem fusionIsBenderGroup_of_isBenderOf {n : ℕ} (h : E2.IsBenderOf n Y') :
    fusionIsBenderGroup Y' := by
  obtain ⟨hn, h | h | h⟩ := h
  · exact A5.C25.fusionIsBenderGroup_of_isPSL h
  · exact A5.C25.fusionIsBenderGroup_of_isSz h
  · exact K1.fusionIsBenderGroup_of_stated_psu_three hn h

theorem isPGroup_commutator_bender [Finite Y] [Finite Y'] (φ : Y →* Y')
    (hφ : Function.Surjective φ) (hZ : φ.ker ≤ Subgroup.center Y) (hodd : Odd (Nat.card φ.ker))
    {n : ℕ} (hY' : E2.IsBenderOf n Y') {S' : Subgroup Y'} (hS : IsSylowTwoOf S' ⊤) :
    IsPGroup 2 ↥⁅(Subgroup.normalizer (S' : Set Y')).comap φ,
      (Subgroup.normalizer (S' : Set Y')).comap φ⁆ := by
  obtain ⟨q, k, hB⟩ :=
    Lin2.exists_fusionBenderBorel_of_fusionIsBenderGroup (fusionIsBenderGroup_of_isBenderOf hY')
  obtain ⟨Q, rfl⟩ := exists_sylow_of_isSylowTwoOf hS
  obtain ⟨-, ⟨D, hDc, -, -, hQD⟩, -⟩ := hB Q
  have hDN : D ≤ Subgroup.normalizer ((Q : Subgroup Y') : Set Y') := hQD ▸ le_sup_right
  refine isPGroup_commutator_comap φ hφ hZ hodd Q.isPGroup' le_rfl hDN (fun b hb => ?_)
    (comap_comm_of_isCyclic φ hZ hDc)
  have hb' : b ∈ ((Q : Subgroup Y') ⊔ D : Subgroup Y') := hQD ▸ hb
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left _ _ hDN] at hb'
  obtain ⟨s, hs, t, ht, rfl⟩ := hb'
  exact ⟨s, hs, t, ht, rfl⟩

end CFSG.Quasithin.Vol2.Ch11.SecB.C10KG
