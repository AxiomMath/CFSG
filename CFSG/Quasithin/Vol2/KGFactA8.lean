module

public import Certificates.Certificate7154
public import CFSG.Quasithin.Vol2.Ch12Sec6L19

public section

namespace CFSG.Quasithin.H13.KGA8

open Equiv

theorem card_alternating : Nat.card (alternatingGroup (Fin 8)) = 20160 := by
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  decide

theorem factA8SolvNormPartition_holds :
    FactA8SolvNormPartition := by
  intro Y P hYA h9 h5 hPA hP2 h32 hPN
  set N := Subgroup.normalizer (Y : Set (Perm (Fin 8))) ⊓ alternatingGroup (Fin 8) with hN
  have hYN : Y ≤ N := le_inf Subgroup.le_normalizer hYA
  have h288 : 288 ∣ Nat.card N := by
    have h9' : 9 ∣ Nat.card N := h9.trans (Subgroup.card_dvd_of_le hYN)
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hP2
    have hk5 : 5 ≤ k := by
      by_contra h
      have : 2 ^ k < 2 ^ 5 := Nat.pow_lt_pow_right (by norm_num) (by omega)
      omega
    have h32' : 32 ∣ Nat.card N := by
      have h1 : 32 ∣ Nat.card P := by
        rw [hk, show 32 = 2 ^ 5 by norm_num]
        exact pow_dvd_pow 2 hk5
      exact h1.trans (Subgroup.card_dvd_of_le (le_inf hPN hPA))
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 9 32) h9' h32'
  have hne : N ≠ alternatingGroup (Fin 8) := by
    intro hNA
    have : IsSimpleGroup (alternatingGroup (Fin 8)) := alternatingGroup.isSimpleGroup (by simp)
    have hnorm : (Y.subgroupOf (alternatingGroup (Fin 8))).Normal := by
      constructor
      intro y hy a
      rw [Subgroup.mem_subgroupOf] at hy ⊢
      have ha : (a : Perm (Fin 8)) ∈ N := by
        rw [hNA]
        exact a.2
      exact (Subgroup.mem_normalizer_iff.mp (Subgroup.mem_inf.mp ha).1 y).mp hy
    have hYeq : Nat.card (Y.subgroupOf (alternatingGroup (Fin 8))) = Nat.card Y :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYA).toEquiv
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (Y.subgroupOf (alternatingGroup (Fin 8))) with hb | ht
    · rw [hb, Subgroup.card_bot] at hYeq
      rw [← hYeq] at h9
      norm_num at h9
    · rw [ht, Subgroup.card_top, card_alternating] at hYeq
      rw [← hYeq] at h5
      norm_num at h5
  obtain ⟨S, hS, hSN⟩ := Certificates.certificate7154.1 N inf_le_right h288 hne
  exact ⟨S, hS, fun y hy => hSN y (hYN hy)⟩

end CFSG.Quasithin.H13.KGA8
