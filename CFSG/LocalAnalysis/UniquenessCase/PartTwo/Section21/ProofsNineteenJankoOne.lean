module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
import CFSG.Quasithin.H13.NQCatC2JH
import CFSG.Walter.J1Props.Hyp
import CFSG.Walter.Models

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup

theorem exists_orderOf_eq_three_mem_normalizer_of_isJ1 {X : Type} [Group X] [Finite X]
    (hX : IsJ1 X) (S : Sylow 2 X) :
    ∃ y ∈ Subgroup.normalizer ((S : Subgroup X) : Set X), orderOf y = 3 := by
  classical
  obtain ⟨e⟩ := hX
  let h : CFSG.Walter.J1.JankoHyp X :=
    CFSG.Quasithin.H13.NQCat.C2.jankoHypOfMulEquiv CFSG.Walter.J1Props.jankoHyp
      (e.trans CFSG.Walter.walterJ1EquivNative.symm)
  have hcard : Nat.card X = 175560 := by
    rw [Nat.card_congr (e.trans CFSG.Walter.walterJ1EquivNative.symm).toEquiv]
    exact CFSG.Walter.J1Props.card_walterJ1
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2dvd : 2 ∣ Nat.card X := by rw [hcard]; norm_num
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥S) 2
    (Sylow.dvd_card_of_dvd_card S h2dvd)
  have hxS : (x : X) ∈ S := x.2
  have hx2 : orderOf (x : X) = 2 := by rw [Subgroup.orderOf_coe]; exact hx
  obtain ⟨g, hg⟩ := h.exists_conj_eq_t hx2
  have ht : (h.conj g⁻¹).t = (x : X) := by
    rw [CFSG.Walter.J1.JankoHyp.conj_t, ← hg]
    group
  have hN : Nat.card (Subgroup.normalizer ((S : Subgroup X) : Set X)) = 168 :=
    (h.conj g⁻¹).card_normalizer_sylow S (by rw [ht]; exact hxS)
  have h3dvd : 3 ∣ Nat.card (Subgroup.normalizer ((S : Subgroup X) : Set X)) := by
    rw [hN]; norm_num
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card'
    (G := Subgroup.normalizer ((S : Subgroup X) : Set X)) 3 h3dvd
  exact ⟨y, y.2, by rw [Subgroup.orderOf_coe]; exact hy⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22
