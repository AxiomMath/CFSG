module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenInvolutions

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG.Blueprint.Chevalley CFSG.ComponentClassification.UnbalancedCatalog


section ShortPair

variable {K : Type} [Field K] [CharP K 2]

theorem g2_short_pair_mul :
    pinnedX .G2 K g2r 1 *
        (pinnedX .G2 K g2nr 1 * pinnedX .G2 K g2v 1 * (pinnedX .G2 K g2nr 1)⁻¹) =
      g2N (1 : K) 1 0 1 0 1 := by
  rw [pinnedX_inv_eq, pinnedX_v_eq_g2N, conj_nr_av]
  simp only [g2N, pinnedX_zero, one_mul, mul_one, mul_assoc, zero_add, one_pow]

theorem g2N_short_pair_pow_four :
    (g2N (1 : K) 1 0 1 0 1) ^ 4 = pinnedX .G2 K g2c 1 := by
  have h2 : (g2N (1 : K) 1 0 1 0 1) ^ 2 = g2N 0 0 1 1 0 1 := by
    rw [sq, g2N_mul_self]
    exact g2N_eq_g2N rfl rfl (by ring) (by ring) (by char2_ring) (by char2_ring)
  have h4 : (g2N (1 : K) 1 0 1 0 1) ^ 4 = ((g2N (1 : K) 1 0 1 0 1) ^ 2) ^ 2 := by
    rw [← pow_mul]
  rw [h4, h2, sq, g2N_mul_self, pinnedX_c_eq_g2N]
  exact g2N_eq_g2N (by ring) (by ring) (by ring) (by ring) (by ring) (by ring)

end ShortPair

theorem g2_short_class_not_admissible (K : Type) [Field K] [CharP K 2] :
    ∃ s t : ↥(adjointGroup .G2 K),
      IsConj s ⟨pinnedX .G2 K g2v 1, pinnedX_mem_adjointGroup g2v 1⟩ ∧
      IsConj t ⟨pinnedX .G2 K g2v 1, pinnedX_mem_adjointGroup g2v 1⟩ ∧
      (s * t) ^ 4 ≠ 1 ∧ (s * t) ^ 8 = 1 := by
  obtain ⟨g, hg, hgs⟩ := G2Conj.r_one (K := K) one_ne_zero
  let c : ↥(adjointGroup .G2 K) := ⟨pinnedX .G2 K g2nr 1, pinnedX_mem_adjointGroup g2nr 1⟩
  let v : ↥(adjointGroup .G2 K) := ⟨pinnedX .G2 K g2v 1, pinnedX_mem_adjointGroup g2v 1⟩
  let s : ↥(adjointGroup .G2 K) := ⟨pinnedX .G2 K g2r 1, pinnedX_mem_adjointGroup g2r 1⟩
  have hst : ((s * (c * v * c⁻¹) : ↥(adjointGroup .G2 K)) : ModGL .G2 K) =
      g2N 1 1 0 1 0 1 := g2_short_pair_mul
  have h4 : (s * (c * v * c⁻¹)) ^ 4 =
      ⟨pinnedX .G2 K g2c 1, pinnedX_mem_adjointGroup g2c 1⟩ :=
    Subtype.ext (by rw [Subgroup.coe_pow, hst, g2N_short_pair_pow_four])
  refine ⟨s, c * v * c⁻¹, ?_, ?_, ?_, ?_⟩
  · exact isConj_iff.2 ⟨⟨g, hg⟩, Subtype.ext hgs⟩
  · exact (isConj_iff.2 ⟨c, rfl⟩).symm
  · rw [h4]
    intro h
    have h1 : pinnedX .G2 K g2c (1 : K) = pinnedX .G2 K g2c 0 := by
      rw [pinnedX_zero]
      exact congrArg Subtype.val h
    exact one_ne_zero (pinnedX_injective .G2 K g2c h1)
  · have h8 : (s * (c * v * c⁻¹)) ^ 8 = ((s * (c * v * c⁻¹)) ^ 4) ^ 2 := by
      rw [← pow_mul]
    rw [h8, h4, sq]
    exact Subtype.ext (pinnedX_mul_self g2c 1)

end CFSG.RankThree.GF2n.Stroth80
