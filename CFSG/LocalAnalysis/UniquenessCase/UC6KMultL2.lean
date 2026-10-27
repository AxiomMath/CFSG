module

public import CFSG.LocalAnalysis.UniquenessCase.UC6DispMult

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open Subgroup CFSG.Open
open scoped MatrixGroups

section KMultL2


theorem kMultL2_holds : KMultL2 := by
  intro J _ _ hq N _ hN hlist hodd
  obtain ⟨r, hr, hr5, hL⟩ := hlist
  have hr2 : r ≠ 2 := by omega
  obtain ⟨F, _, _, e, -, hFq⟩ := CFSG.GH74.GLS.EvenSelP.exists_l2Field_of_lieModel' hr hr2 hL
  haveI : Fintype F := Fintype.ofFinite F
  let φ : J ⧸ N ≃* PSL(2, F) := CFSG.GH74.GLS.IVK.toPSL e
  have hcenQ : center (J ⧸ N) = ⊥ :=
    CFSG.GorensteinWalter.center_eq_bot_of_mulEquiv φ (CFSG.GorensteinWalter.psl2_center_eq_bot F)
  have hCN : center J = N := by
    refine le_antisymm (fun z hz => ?_) hN
    have hc : (QuotientGroup.mk' N z) ∈ center (J ⧸ N) := by
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨y', rfl⟩ := QuotientGroup.mk'_surjective N y
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hz y']
    rw [hcenQ, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hc
    exact hc
  have e' : J ⧸ center J ≃* PSL(2, F) := (QuotientGroup.quotientMulEquivOfEq hCN).trans φ
  have hdvd := CFSG.Sporadic.Recognition.HeMultiplier.card_center_dvd_griess (S := PSL(2, F))
    ⟨hq.1⟩ e'
  have hcard : Fintype.card F = r ^ 2 := by rw [← Nat.card_eq_fintype_card, hFq]
  have h25 : 5 ≤ Fintype.card F := by
    rw [hcard]
    nlinarith
  have h9 : Fintype.card F ≠ 9 := by
    rw [hcard]
    intro h
    have : r ≤ 3 := by nlinarith
    omega
  obtain ⟨-, ⟨hM⟩⟩ := CFSG.LieType.Steinberg.CentralExt.SL2Closed.psl_two_hopfMultiplier (k := F)
    h25 h9
  have hodd2 : Odd r := hr.odd_of_ne_two hr2
  have hgcd : Nat.gcd 2 (Fintype.card F - 1) = 2 := by
    rw [hcard]
    refine Nat.gcd_eq_left (even_iff_two_dvd.1 ?_)
    obtain ⟨k, hk⟩ := hodd2
    rw [hk]
    exact ⟨2 * k * k + 2 * k, by
      have h1 : 1 ≤ (2 * k + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
      zify [h1]
      ring⟩
  have hMcard : Nat.card (griessHopfMultiplier PSL(2, F)) = 2 := by
    rw [Nat.card_congr hM.toEquiv, hgcd]
    simp
  rw [hMcard] at hdvd
  have h12 : Nat.card (center J) = 1 ∨ Nat.card (center J) = 2 :=
    (Nat.dvd_prime Nat.prime_two).1 hdvd
  have hcard1 : Nat.card (center J) = 1 := by
    rcases h12 with h | h
    · exact h
    · rw [h] at hodd
      exact absurd hodd (by decide)
  exact Subgroup.eq_bot_of_card_eq _ hcard1

end KMultL2

end CFSG.LocalAnalysis.UniquenessCase.UCK
