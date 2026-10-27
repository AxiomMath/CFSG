module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148LRowCover
public import CFSG.Models.PGLOrders

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148L

open CFSG CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.KFacts
open CFSG.Blueprint
open CFSG.Assembly.RankThreeEven (projSU)

section Sz


theorem rowU3_Sz {S : Type} [Group S] [Finite S] {f : ℕ} (hm : SuzukiModel S 2 f)
    {σ : MulAut S} (_hσ3 : σ ^ 3 = 1) (_hσ1 : σ ≠ 1) {Y : Subgroup S}
    (_hYC : Y ≤ Sec4.autFix σ) [Group.IsPerfect Y]
    (_hsub : (Y.subgroupOf (Sec4.autFix σ)).IsSubnormal) {m : ℕ} (hmo : Odd m) (hm1 : 1 < m)
    (π : Y →* projSU 3 2 m) (hπ : Function.Surjective π)
    (hker : Nat.Coprime (Nat.card π.ker) 3) : False := by
  obtain ⟨-, a, -, F, _, _, hf, hK', ⟨θ⟩⟩ := hm
  have hK : Nat.card F = 2 ^ (2 * a + 1) := by rw [hK', hf]
  have h3 : ¬ 3 ∣ Nat.card S := by
    rw [Nat.card_congr θ.toEquiv]
    exact not_three_dvd_card_suzukiGroup hK
  obtain ⟨E, -, -, -, hE9, -⟩ := exists_e9_of_cover hmo hm1 π hπ hker
  apply h3
  have h9 : 9 ∣ Nat.card S := hE9 ▸ Subgroup.card_subgroup_dvd_card E
  exact (show 3 ∣ 9 by norm_num).trans h9

end Sz

section Tits


theorem rowU3_Tits {S : Type} [Group S] [Finite S] {f : ℕ} (hm : ReeTitsModel S .Tits 2 f)
    {σ : MulAut S} (_hσ3 : σ ^ 3 = 1) (_hσ1 : σ ≠ 1) {Y : Subgroup S}
    (_hYC : Y ≤ Sec4.autFix σ) [Group.IsPerfect Y]
    (_hsub : (Y.subgroupOf (Sec4.autFix σ)).IsSubnormal) {m : ℕ} (hmo : Odd m) (hm1 : 1 < m)
    (π : Y →* projSU 3 2 m) (hπ : Function.Surjective π)
    (_hker : Nat.Coprime (Nat.card π.ker) 3) : False := by
  obtain ⟨e⟩ := CFSG.Sporadic.Schreier.Tits.titsModelEquiv S 2 f hm
  have hS : Nat.card S = 17971200 := by
    rw [Nat.card_congr e.toEquiv, CFSG.Sporadic.Schreier.Tits.card_titsD]
  have hU := padicValNat_card_projSU (by omega : 1 ≤ m)
  have hdU : Nat.card (projSU 3 2 m) ∣ Nat.card Y := Subgroup.card_dvd_of_surjective hπ
  have hdY : Nat.card Y ∣ Nat.card S := Subgroup.card_subgroup_dvd_card Y
  have h := hdU.trans hdY
  rw [hS] at h
  have h2 : 2 ^ (3 * m) ∣ Nat.card (projSU 3 2 m) := hU ▸ pow_padicValNat_dvd
  have hm3 : m = 3 := by
    by_contra hne
    have hm5 : 5 ≤ m := by
      obtain ⟨j, rfl⟩ := hmo
      omega
    have h15 : 2 ^ 15 ∣ 2 ^ (3 * m) := pow_dvd_pow 2 (by omega)
    have := (h15.trans h2).trans h
    norm_num at this
  subst hm3
  rw [CFSG.PGLModel.card_projSU_three_eight] at h
  norm_num at h

end Tits

end CFSG.RankThree.PartTwo.Sec4.Ronan148L
