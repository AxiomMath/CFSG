module

public import CFSG.Quasithin.Background.G6Basic

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG.Quasithin

theorem pResidual_two_idem (G : Type) [Group G] [Finite G] (N : Subgroup ↥(pResidual 2 G))
    [N.Normal] (hN : IsPGroup 2 (↥(pResidual 2 G) ⧸ N)) : N = ⊤ := by
  haveI : (pResidual 2 G).Normal := G6.pResidual_normal_aux 2
  obtain ⟨n, hn⟩ := hN.exists_card_eq
  have hK : ∀ x : G, ∃ k : ℕ, x ^ 2 ^ k ∈ (N.map (pResidual 2 G).subtype).normalCore := by
    intro x
    obtain ⟨a, ha⟩ := G6.exists_pow_mem_pResidual 2 x
    refine ⟨a + n, ?_⟩
    rw [pow_add, pow_mul, Subgroup.normalCore_eq_iInf_comap_conj, Subgroup.mem_iInf]
    intro g
    have hconj : g * (x ^ 2 ^ a) * g⁻¹ ∈ pResidual 2 G :=
      Subgroup.Normal.conj_mem inferInstance _ ha g
    have hz : (⟨_, hconj⟩ : ↥(pResidual 2 G)) ^ 2 ^ n ∈ N := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, ← hn]
      exact pow_card_eq_one'
    have hmem := Subgroup.mem_map_of_mem (pResidual 2 G).subtype hz
    rw [map_pow, Subgroup.subtype_apply, conj_pow] at hmem
    rw [Subgroup.mem_comap]
    simpa [MulAut.conj_apply] using hmem
  have hle : pResidual 2 G ≤ (N.map (pResidual 2 G).subtype).normalCore := pResidual_le hK
  rw [eq_top_iff]
  intro y _
  obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.1 (Subgroup.normalCore_le _ (hle y.2))
  obtain rfl : z = y := Subtype.ext (by simpa using hzy)
  exact hz

end CFSG.RankThree.GF2n.Tim79a
