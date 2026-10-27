module

public import CFSG.Quasithin.H13.GoldschmidtC137SQRk
public import CFSG.Quasithin.H13.GoldschmidtC137SQA6
public import CFSG.Quasithin.H13.GoldschmidtC137H6Alg

public section

namespace CFSG.Quasithin.H13.U3.GC137.SQ

open CFSG.Open

theorem card_hatA6 {Y : Type} [Group Y] [Finite Y] (hZ : Nat.card (Subgroup.center Y) = 3)
    (e : (Y ⧸ Subgroup.center Y) ≃* alternatingGroup (Fin 6)) : Nat.card Y = 1080 := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center Y)
  rw [hZ, Nat.card_congr e.toEquiv, card_alternatingGroup_six] at h
  omega

theorem rankLeTwo_of_hatA6 {Y : Type} [Group Y] [Finite Y] (hperf : Group.IsPerfect Y)
    (hZ : Nat.card (Subgroup.center Y) = 3)
    (e : (Y ⧸ Subgroup.center Y) ≃* alternatingGroup (Fin 6)) : RankLeTwo Y := by
  have hcard := card_hatA6 hZ e
  refine rankLeTwo_of_three (Or.inr (Or.inr (Or.inl hcard))) fun E hE => ?_
  obtain ⟨n, hn⟩ := (isPGroup_of_isElemAbelian (p := 3) hE).exists_card_eq
  have hdvd : 3 ^ n ∣ 1080 := hcard ▸ hn ▸ Subgroup.card_subgroup_dvd_card E
  have hn3 : n ≤ 3 := by
    by_contra h
    have h4 : 3 ^ 4 ∣ 1080 := (pow_dvd_pow 3 (by omega)).trans hdvd
    norm_num at h4
  rw [hn]
  by_cases h3 : n = 3
  · exfalso
    have hmul := E.card_mul_index
    rw [hn, h3, hcard] at hmul
    have hidx : ¬ 3 ∣ E.index := by
      have : E.index = 40 := by omega
      omega
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center Y) 3
      (by rw [hZ])
    refine no_abelian_of_perfect_central_gc hperf (S := E)
      (fun a ha b hb => ?_) x.2 (by rw [Subgroup.orderOf_coe]; exact hx) hidx
    exact congrArg Subtype.val (hE.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  · exact Nat.pow_le_pow_right (by norm_num) (by omega)

end CFSG.Quasithin.H13.U3.GC137.SQ
