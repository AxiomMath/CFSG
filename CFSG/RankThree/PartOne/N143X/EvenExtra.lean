module

public import CFSG.RankThree.PartOne.N143X.EvenOrders
import CFSG.Sporadic.Schreier.TitsOuter
public import CFSG.RankThree.PartOne.N143X.EvenSmall

public section

namespace CFSG.RankThree.PartOne.N143X

open CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank

theorem factorization_three_suzuki {T : Type} [Group T] {f : ℕ} (hmod : SuzukiModel T 2 f)
    {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p) {E : Subgroup T} (hE : IsElementaryAbelian p E) :
    (Nat.card E.normalizerMonoidHom.range).factorization 3 ≤ 1 := by
  obtain ⟨-, a, ha, K, _, _, hf, hK, ⟨e⟩⟩ := hmod
  have hpK : (p : K) ≠ 0 := natCast_ne_zero_of_card_two_pow hK hp (by omega)
  exact factorization_three_le_one_of_embedding
    ((suzukiGroup a K).subtype.comp e.toMonoidHom)
    (Subtype.val_injective.comp e.injective) hp hpK hE (by simp)

theorem not_pow_three_dvd_titsD {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p) :
    ¬ p ^ 3 ∣ 17971200 := by
  intro h
  have h13 : p ^ 3 ∣ 13 := pow_three_dvd_of_dvd_mul hp hp7 (a := 11) (b := 3) (c := 2) (m := 13)
    (dvd_of_eq (by norm_num)) h
  have := Nat.le_of_dvd (by norm_num) h13
  have h343 : 7 ^ 3 ≤ p ^ 3 := Nat.pow_le_pow_left hp7 3
  omega

theorem false_of_pow_three_tits
    {T : Type} [Group T] {f : ℕ} (hmod : ReeTitsModel T .Tits 2 f) {p : ℕ} (hp : p.Prime)
    (hp7 : 7 ≤ p) {E : Subgroup T} (hcard : Nat.card E = p ^ 3) : False := by
  obtain ⟨e⟩ := CFSG.Sporadic.Schreier.Tits.titsModelEquiv T 2 f hmod
  have hT : Nat.card T = 17971200 := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.Sporadic.Schreier.Tits.card_titsD
  have hdvd : p ^ 3 ∣ 17971200 := by
    rw [← hT, ← hcard]
    exact Subgroup.card_subgroup_dvd_card E
  exact not_pow_three_dvd_titsD hp hp7 hdvd

end CFSG.RankThree.PartOne.N143X
