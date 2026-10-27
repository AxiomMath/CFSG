module

public import CFSG.RankThree.PartTwo.Sec8.Item86Res2ProofIndep
import CFSG.RankThree.PartTwo.Sec11.KS11Lie3ProofEight
import CFSG.Quasithin.Background.P3G2Iso
public import CFSG.Quasithin.Background.G2UCodes

public section

namespace CFSG.RankThree.PartTwo.Sec8.Item86ResProof

open CFSG.Blueprint.Chevalley

theorem pow_three_eq_one_of_pow_nine {F : Type*} [Field F] [CharP F 3] (u : GL (Fin 3) F)
    (h9 : u ^ 9 = 1) : u ^ 3 = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set M : Matrix (Fin 3) (Fin 3) F := (u : Matrix (Fin 3) (Fin 3) F) - 1 with hMdef
  have hcomm : Commute (u : Matrix (Fin 3) (Fin 3) F) 1 := Commute.one_right _
  have hM9 : M ^ 9 = 0 := by
    have h := sub_pow_char_pow_of_commute (p := 3) (n := 2) hcomm
    rw [show (3 : ℕ) ^ 2 = 9 by norm_num] at h
    rw [hMdef, h, one_pow, ← Units.val_pow_eq_pow_val, h9, Units.val_one, sub_self]
  have hnil : IsNilpotent M := ⟨9, hM9⟩
  have h1 := Matrix.isNilpotent_charpoly_sub_pow_of_isNilpotent hnil
  have h2 : M.charpoly = Polynomial.X ^ 3 := by
    have h := h1.eq_zero
    rw [Fintype.card_fin, sub_eq_zero] at h
    exact h
  have h3 := Matrix.aeval_self_charpoly M
  rw [h2, map_pow, Polynomial.aeval_X] at h3
  have h4 := sub_pow_char_of_commute (p := 3) hcomm
  rw [← hMdef, h3, one_pow] at h4
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, Units.val_one]
  exact (sub_eq_zero.mp h4.symm)

theorem kF83GTwoTwo_holds : KF83GTwoTwo := by
  intro K _ _ hK g hg
  have : Fintype K := Fintype.ofFinite K
  have hF : Fintype.card K = 2 := by rw [← Nat.card_eq_fintype_card, hK]
  set F := GaloisField 2 1
  have : Fintype F := Fintype.ofFinite F
  have hFc : Nat.card F = 2 := by rw [GaloisField.card 2 1 (by norm_num), pow_one]
  have hF2 : Fintype.card F = 2 := by rw [← Nat.card_eq_fintype_card, hFc]
  let ε : K ≃+* F := (ZMod.ringEquivOfPrime K Nat.prime_two hF).symm.trans
    (ZMod.ringEquivOfPrime F Nat.prime_two hF2)
  obtain ⟨e₁⟩ :=
    CFSG.RankThree.PartTwo.Sec11.KS11Lie3Proof.nonempty_adjointGroup_g2_mulEquiv_quasithinG2 hFc
  let e : adjointGroup .G2 K ≃* CFSG.Open.quasithinG2 F :=
    (CFSG.TauCetiBridge.adjointGroupCongr ε).trans e₁
  set Q := CFSG.Open.quasithinG2 F
  set h := e g with hh
  have hh9 : orderOf h = 9 := by rw [hh, MulEquiv.orderOf_eq, hg]
  have hQ : Nat.card Q = 12096 := by
    rw [← Nat.card_congr e.toEquiv, CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_G2, hK]
    rfl
  have hC : Nat.card ↥⁅Q, Q⁆ = 6048 := CFSG.Quasithin.G11.P3G2.card_commutatorG2
  have hle : ⁅Q, Q⁆ ≤ Q := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    rw [commutatorElement_def]
    exact Q.mul_mem (Q.mul_mem (Q.mul_mem ha hb) (Q.inv_mem ha)) (Q.inv_mem hb)
  set H := (⁅Q, Q⁆).subgroupOf Q
  have hH : Nat.card H = 6048 := by
    rw [← hC]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
  have hidx : H.index = 2 := by
    have h1 := H.index_mul_card
    rw [hH, hQ] at h1
    omega
  have hmem : h ∈ H := by
    have h1 := Subgroup.sq_mem_of_index_two hidx (h ^ 5)
    have h2 : (h ^ 5) ^ 2 = h := by
      rw [← pow_mul]
      have : h ^ 9 = 1 := by rw [← hh9]; exact pow_orderOf_eq_one h
      calc h ^ (5 * 2) = h ^ 9 * h := by rw [← pow_succ]
        _ = h := by rw [this, one_mul]
    rwa [h2] at h1
  set u := CFSG.Quasithin.G11.P3G2.commutatorG2EquivSU ⟨(h : _), hmem⟩ with hu
  have hu9 : orderOf u = 9 := by
    rw [hu, MulEquiv.orderOf_eq, ← Subgroup.orderOf_coe, ← hh9]
    exact Subgroup.orderOf_coe h
  have : CharP CFSG.Quasithin.G2U.F9 3 :=
    charP_of_injective_algebraMap (algebraMap (ZMod 3) CFSG.Quasithin.G2U.F9).injective 3
  have hv9 : (u : GL (Fin 3) CFSG.Quasithin.G2U.F9) ^ 9 = 1 := by
    rw [← Subgroup.coe_pow, ← hu9, pow_orderOf_eq_one, Subgroup.coe_one]
  have hv3 := pow_three_eq_one_of_pow_nine _ hv9
  have : u ^ 3 = 1 := Subtype.ext (by rw [Subgroup.coe_pow, hv3, Subgroup.coe_one])
  have := orderOf_dvd_of_pow_eq_one this
  rw [hu9] at this
  norm_num at this

theorem kF83IndepGTwo_holds : KF83IndepGTwo :=
  kF83IndepGTwo_of_two kF83GTwoTwo_holds

end CFSG.RankThree.PartTwo.Sec8.Item86ResProof
