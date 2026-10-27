module

public import CFSG.RankThree.SubgroupLists.QuasisimpleRankTwo

public section

namespace CFSG.RankThree.SubgroupLists

open Subgroup CFSG CFSG.Assembly.LowTwoRank

theorem twoRank_statedProj_statedSU_three_le_two {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = (p ^ f) ^ 2) :
    CFSG.Assembly.twoRank (StatedProj (StatedSU 3 (p ^ f) K)) ≤ 2 := by
  classical
  have hodd : Odd (Nat.card K) := by rw [hK]; exact ((hp.odd_of_ne_two hp2).pow).pow
  have hdet : ∀ g ∈ StatedSU 3 (p ^ f) K, (g : Matrix (Fin 3) (Fin 3) K).det = 1 := by
    intro g hg
    have h1 : g ∈ (Matrix.GeneralLinearGroup.det : GL (Fin 3) K →* Kˣ).ker := by
      refine (Subgroup.closure_le _).2 ?_ hg
      intro A hA
      rw [SetLike.mem_coe, MonoidHom.mem_ker]
      apply Units.ext
      rw [Matrix.GeneralLinearGroup.val_det_apply]
      exact hA.1
    have h2 := congrArg Units.val (MonoidHom.mem_ker.1 h1)
    rwa [Matrix.GeneralLinearGroup.val_det_apply] at h2
  set H := StatedSU 3 (p ^ f) K with hH
  let N : Subgroup ↥H := (StatedScalars (Fin 3) K).subgroupOf H
  have hN : ¬ 2 ∣ Nat.card N := by
    intro h2
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' 2 h2
    have hg3 : g ^ 3 = 1 := by
      obtain ⟨c, hc⟩ := (Subgroup.mem_subgroupOf.1 g.2 : ((g : ↥H) : GL (Fin 3) K) ∈
        StatedScalars (Fin 3) K)
      have hdg := hdet (g : ↥H) (g : ↥H).2
      rw [← hc] at hdg
      have hc3 : c ^ 3 = 1 := by
        apply Units.ext
        have : (((Matrix.GeneralLinearGroup.scalar (Fin 3) c : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)).det =
            (c : K) ^ 3 := by
          simp
        rw [this] at hdg
        simpa using hdg
      apply Subtype.ext
      apply Subtype.ext
      rw [Subgroup.coe_pow, Subgroup.coe_pow]
      show (((g : ↥H) : GL (Fin 3) K)) ^ 3 = 1
      rw [← hc, ← map_pow, hc3, map_one]
    have := orderOf_dvd_of_pow_eq_one hg3
    rw [hg] at this
    omega
  unfold CFSG.Assembly.twoRank
  rw [CFSG.GroupTheory.PRankCoprimeQuotient.assembly_pRank_quotient_eq_of_not_dvd Nat.prime_two N hN]
  exact CFSG.RankThree.SubgroupLists.twoRank_le_two_of_det_eq_one hodd hdet

end CFSG.RankThree.SubgroupLists
