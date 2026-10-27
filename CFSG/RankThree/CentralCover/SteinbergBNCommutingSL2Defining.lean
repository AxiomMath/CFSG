module

public import CFSG.RankThree.CentralCover.SteinbergBNCommutingSL2DefiningCore

public section

namespace CFSG.RankThree.CentralCover

open CFSG.Assembly CFSG.Assembly.RankThreeEven
open scoped MatrixGroups

theorem three_lt_pow_and_ne_nine {p f : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hf : 1 ≤ f) :
    3 < p ^ f ∧ p ^ f ≠ 9 := by
  refine ⟨lt_of_lt_of_le hp3 (Nat.le_self_pow (by omega) p), fun h9 => ?_⟩
  have hdvd : p ∣ 3 ^ 2 := by
    rw [show (3 : ℕ) ^ 2 = 9 by norm_num, ← h9]
    exact dvd_pow_self p (by omega)
  have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (hp.dvd_of_dvd_pow hdvd)
  omega

theorem commuting_SL2_actual_central_cover_defining_local_rank {G : Type*} [Group G] [Finite G]
    (Y : Subgroup G) {H : Type*} [Group H] {p f m : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hf : 1 ≤ f) (hm : 1 ≤ m) {K : Type*} [Field K] [Fintype K] (hK : Fintype.card K = p ^ f)
    (φ : Y →* H) (hφ : Function.Surjective φ) (hker : φ.ker ≤ Subgroup.center Y)
    (ι : Fin m → SL(2, K) →* H) (hι : ∀ i, Function.Injective (ι i))
    (hcomm : ∀ i j, i ≠ j → ∀ A B : SL(2, K), ι i A * ι j B = ι j B * ι i A) :
    ∃ u : G, u ∈ Y ∧ orderOf u = 2 ∧ ∃ A : Subgroup G, A ≤ Y ⊓ Subgroup.centralizer {u} ∧
      IsElemAbelian p A ∧ Nat.card A = p ^ (m * f) ∧ m * f ≤ localRank p G := by
  obtain ⟨h3, h9⟩ := three_lt_pow_and_ne_nine hp hp3 hf
  have hsum : ∑ _i : Fin m, f = m * f := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  have := commuting_SL2_defining_witness Y hφ hker hp (by omega) hm (K := fun _ => K)
    (fun _ => f) (fun _ => hK) (fun _ => h3) (fun _ => h9) ι hι hcomm
  rwa [hsum] at this

end CFSG.RankThree.CentralCover
