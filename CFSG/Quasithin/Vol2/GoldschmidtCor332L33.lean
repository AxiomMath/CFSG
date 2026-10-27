module

public import CFSG.CharacterTheory.Wreathed.OddLinearThreeCentralizerCore
public import CFSG.RankThree.PartOne.KFOUT3.SLCard
public import CFSG.Quasithin.Vol2.GoldschmidtCor332Gen

public section

namespace CFSG.Quasithin.H13.Cor332

open scoped MatrixGroups
open CFSG.Wreathed.OddLinearThreeCentralizerCore

section Centralizer

variable {F : Type} [Field F] [Finite F]

theorem card_centralizer_dvd (hF : Odd (Nat.card F)) (D : Subgroup (SL3 F)) [D.Normal]
    (hD : D ≤ Subgroup.center (SL3 F)) (z : SL3 F) (hz : orderOf z = 2) :
    Nat.card (Subgroup.centralizer ({QuotientGroup.mk' D z} : Set (SL3 F ⧸ D))) ∣
      Nat.card F * (Nat.card F - 1) ^ 2 * (Nat.card F + 1) := by
  have hc := Subgroup.card_ker_mul_card_of_surjective
    (matrixQuotientCentralizer_surjective F hF D hD z hz)
  rw [matrixQuotientKernel_card F hF D hD z hz,
    CFSG.Wreathed.OddLinearTwoAutomorphisms.card_automorphisms F
      (minusSpace (matrixAction F z).toLinearMap) (matrixAction_finrank F hF z hz).1] at hc
  exact Dvd.intro_left _ hc

theorem orderOf_dvd_of_commute_involution (hF : Odd (Nat.card F)) {x t : PSL(3, F)}
    (ht : orderOf t = 2) (hxt : x * t = t * x) :
    orderOf x ∣ Nat.card F * (Nat.card F - 1) ^ 2 * (Nat.card F + 1) := by
  obtain ⟨z, ⟨hz, hzt⟩, -⟩ := unique_involution_lift F (Subgroup.center (SL3 F)) le_rfl t ht
  have hx : x ∈ Subgroup.centralizer ({t} : Set PSL(3, F)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff.mp hh]
    exact hxt.symm
  have hdvd := card_centralizer_dvd hF (Subgroup.center (SL3 F)) le_rfl z hz
  rw [hzt] at hdvd
  have h1 := orderOf_dvd_natCard (⟨x, hx⟩ : Subgroup.centralizer ({t} : Set PSL(3, F)))
  rw [Subgroup.orderOf_mk] at h1
  exact h1.trans hdvd

end Centralizer

theorem card_psl33_dvd : Nat.card PSL(3, ZMod 3) ∣ 5616 := by
  have h1 : Nat.card (SL(3, ZMod 3)) = 5616 := by
    rw [CFSG.RankThree.PartOne.KFOUT3.card_SL3_eq (K := ZMod 3), Nat.card_zmod]
    norm_num
  rw [← h1]
  exact Subgroup.card_quotient_dvd_card _

theorem twoLocalsSolvable_psl33 : TwoLocalsSolvable PSL(3, ZMod 3) := by
  have h2p : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite PSL(3, ZMod 3) := inferInstance
  refine twoLocalsSolvable_of 4 ?_ ?_ ?_
  · intro E hE
    have hEp : IsPGroup 2 E := fun g => ⟨1, Subtype.ext (by simpa using hE.2 g g.2)⟩
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hEp
    have hdvd : 2 ^ n ∣ 5616 :=
      hn ▸ (Subgroup.card_subgroup_dvd_card E).trans card_psl33_dvd
    by_contra hlt
    have h5 : 2 ^ 5 ∣ 2 ^ n := Nat.pow_dvd_pow 2 (by
      by_contra h
      have : n ≤ 4 := by omega
      have : 2 ^ n ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) this
      omega)
    have := h5.trans hdvd
    omega
  · intro r hr h5 hrG d hd1 hdk h
    have hr5616 : r ∣ 5616 := hrG.trans card_psl33_dvd
    have hpos : 0 < 2 ^ d - 1 := by
      have : 2 ^ 1 ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) hd1
      omega
    have hle := Nat.le_of_dvd hpos h
    have h16 : 2 ^ d ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) hdk
    have : r ≤ 15 := by omega
    interval_cases r <;> interval_cases d <;> omega
  · intro x z hz hxz r hr h5 hxo
    have hdvd := orderOf_dvd_of_commute_involution (F := ZMod 3)
      (by rw [Nat.card_zmod]; decide) hz hxz
    rw [hxo, Nat.card_zmod] at hdvd
    have h48 : r ∣ 2 ^ 4 * 3 := by simpa using hdvd
    rcases (Nat.Prime.dvd_mul hr).mp h48 with h | h
    · have := (Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp (hr.dvd_of_dvd_pow h)
      omega
    · have := (Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).mp h
      omega

end CFSG.Quasithin.H13.Cor332
