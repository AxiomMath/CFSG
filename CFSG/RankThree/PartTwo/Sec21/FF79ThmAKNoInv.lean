module

public import CFSG.RankThree.PartTwo.Sec21.FF79ThmADefs
import CFSG.RankThree.PartTwo.Sec21.FF79ThmAKNoInvMat

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79

open CFSG CFSG.Open CFSG.Open.StatedAPI CFSG.RankThree.PartTwo.Sec21
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

theorem exists_orderOf_five_of_l24 {Y : Type} [Group Y] [Finite Y] (K : Subgroup Y)
    (hK : StatedClassicalModel K .PSL 2 2 2) : ∃ z : Y, z ∈ K ∧ orderOf z = 5 := by
  obtain ⟨-, F, _, _, hcard, ⟨e⟩⟩ := hK
  haveI : Fintype F := Fintype.ofFinite F
  obtain ⟨p, hp, n, hpp, hpn⟩ := FiniteField.card' (K := F)
  have hcard4 : Fintype.card F = 4 := by
    rw [← Nat.card_eq_fintype_card, hcard]; norm_num
  have hp2 : p = 2 := by
    have h1 : p ∣ 4 := by
      rw [← hcard4, hpn]; exact dvd_pow_self p n.ne_zero
    have h2 : p ∣ 2 ^ 2 := by simpa using h1
    exact (Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).1 (hpp.dvd_of_dvd_pow h2)
  subst hp2
  haveI : CharP F 2 := hp
  have hN := statedScalars_subgroupOf_statedSL_two_eq_bot (K := F)
  have hKcard : Nat.card K = 60 := by
    have h1 : Nat.card K = Nat.card (StatedProj (StatedSL 2 F)) := Nat.card_congr e.toEquiv
    have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup
      ((StatedScalars (Fin 2) F).subgroupOf (StatedSL 2 F))
    have hNc : Nat.card ((StatedScalars (Fin 2) F).subgroupOf (StatedSL 2 F)) = 1 := by
      rw [hN]; exact Subgroup.card_bot
    rw [hNc, mul_one, card_statedSL_two] at h2
    have h3 : Nat.card F = 4 := by rw [Nat.card_eq_fintype_card]; exact hcard4
    rw [h1, ← h2, h3]
    norm_num
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨k, hk⟩ := exists_prime_orderOf_dvd_card' (G := K) 5 (by rw [hKcard]; norm_num)
  exact ⟨k, k.2, by rw [Subgroup.orderOf_coe]; exact hk⟩

theorem statedScalars_subgroupOf_card_two {F : Type} [Field F] (hF : Nat.card F = 2) (n : ℕ) :
    (StatedScalars (Fin n) F).subgroupOf (StatedSL n F) = ⊥ := by
  obtain ⟨y, hy, huniq⟩ := (Nat.card_eq_two_iff' (0 : F)).1 hF
  rw [eq_bot_iff]
  intro g hg
  obtain ⟨c, hc⟩ := Subgroup.mem_subgroupOf.1 hg
  have hc1 : c = 1 := by
    apply Units.ext
    rw [huniq c.val c.ne_zero, ← huniq 1 one_ne_zero]; rfl
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  rw [← hc, hc1, map_one]
  rfl

theorem ff79KNoInvA5_holds : FF79KNoInvA5 := by
  intro Y _ _ n hn hY K hK t ht hKt
  obtain ⟨z, hzK, hz⟩ := exists_orderOf_five_of_l24 K hK
  have htz : t * z = z * t := Subgroup.mem_centralizer_iff.1 (hKt hzK) t rfl
  obtain ⟨-, F, _, _, hcard, ⟨e⟩⟩ := hY
  have hF : Nat.card F = 2 := by simpa using hcard
  let ψ : StatedProj (StatedSL n F) ≃* StatedSL n F :=
    (QuotientGroup.quotientMulEquivOfEq (statedScalars_subgroupOf_card_two hF n)).trans
      QuotientGroup.quotientBot
  let φ : Y →* GL (Fin n) F := (StatedSL n F).subtype.comp (e.trans ψ).toMonoidHom
  have hφ : Function.Injective φ := Subtype.val_injective.comp (e.trans ψ).injective
  have hz5 : z ^ 5 = 1 := hz ▸ pow_orderOf_eq_one z
  have ht2 : t ^ 2 = 1 := ht ▸ pow_orderOf_eq_one t
  have hz1 : z ≠ 1 := by
    rintro rfl; rw [orderOf_one] at hz; omega
  have ht1 : t ≠ 1 := by
    rintro rfl; rw [orderOf_one] at ht; omega
  refine ff79_noInv_gl hF n hn (φ z) (φ t) ?_ ?_ ?_ ?_ ?_
  · rw [← map_pow, hz5, map_one]
  · intro h; exact hz1 (hφ (h.trans (map_one φ).symm))
  · rw [← map_pow, ht2, map_one]
  · intro h; exact ht1 (hφ (h.trans (map_one φ).symm))
  · rw [← map_mul, ← map_mul, htz]

end CFSG.RankThree.PartTwo.Sec21.FF79
