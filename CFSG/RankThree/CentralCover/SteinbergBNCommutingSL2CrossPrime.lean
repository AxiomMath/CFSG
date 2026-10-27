module

public import CFSG.RankThree.CentralCover.SteinbergBNSL2InversionBasis
public import CFSG.RankThree.CentralCover.SteinbergBNSL2Elements

public section

namespace CFSG.RankThree.CentralCover

open CFSG.Assembly CFSG.Assembly.RankThreeEven
open scoped MatrixGroups

theorem commuting_SL2_actual_central_cover_cross_prime_local_rank {G : Type*} [Group G]
    [Finite G] (Y : Subgroup G) {H : Type*} [Group H] {K : Type*} [Field K] [Fintype K]
    (hq : Odd (Fintype.card K)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Fintype.card K ^ 2 - 1) {m : ℕ} (hm : 1 ≤ m) (φ : Y →* H)
    (hφ : Function.Surjective φ) (hker : φ.ker ≤ Subgroup.center Y)
    (ι : Fin m → SL(2, K) →* H) (hι : ∀ i, Function.Injective (ι i))
    (hcomm : ∀ i j, i ≠ j → ∀ A B : SL(2, K), ι i A * ι j B = ι j B * ι i A) :
    ∃ u : G, u ∈ Y ∧ orderOf u = 2 ∧ ∃ A : Subgroup G, A ≤ Y ⊓ Subgroup.centralizer {u} ∧
      IsElemAbelian p A ∧ Nat.card A = p ^ m ∧ m ≤ localRank p G := by
  have hK : ringChar K ≠ 2 := by
    intro h
    have := FiniteField.even_card_iff_char_two.1 h
    rw [Nat.odd_iff] at hq
    omega
  obtain ⟨h₀, w₀, hord₀, hinv₀⟩ := exists_inverted_of_dvd_card_sq_sub_one hK hp hp2 hpq
  obtain ⟨hDab, hDcard, hF⟩ := commuting_SL2_inversion_package hφ hker ι hι hcomm hp hp2 hord₀
    hinv₀
  set i₀ : Fin m := ⟨0, hm⟩
  have hz : orderOf (ι i₀ (sl2Diag (-1))) = 2 := by
    rw [orderOf_injective _ (hι i₀), orderOf_sl2Diag_neg_one hK]
  have hzh : ∀ i, Commute (ι i₀ (sl2Diag (-1))) (ι i h₀) := fun i => by
    by_cases hi : i = i₀
    · rw [hi]
      exact (sl2Diag_neg_one_commute h₀).map (ι i₀)
    · exact hcomm i₀ i (Ne.symm hi) _ _
  obtain ⟨u, huY, hu, A, hA, hAab, hAcard, -, -, hrank⟩ :=
    central_cover_involution_witness Y hφ hker hp hp2 hDab.2 hF hDcard.ge hz
      (fun _ hx => commute_of_mem_closure_range hzh hx)
  exact ⟨u, huY, hu, A, hA, hAab, hAcard, hrank⟩

end CFSG.RankThree.CentralCover
