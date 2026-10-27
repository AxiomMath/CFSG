
module

public import CFSG.Quasithin.H13.HSLocBaseBase

public section

namespace CFSG.Quasithin.H13.LocDbl.HSLoc

open CFSG.QuasithinUnique.K1.SporadicPerm hiding img keyNat
open CFSG.Quasithin.H13.LocDbl.DcNative CFSG.Quasithin.H13.LocDbl.DcRank CFSG.Quasithin.H13.LocDbl.Dc
open CFSG.RankThree.Native

theorem exists_conj_mem_sylow {G : Type*} [Group G] [Finite G] {Q : Subgroup G} {p : ℕ}
    [hp : Fact p.Prime] (hQ : Nat.card Q = p ^ (Nat.card G).factorization p) {a : G}
    (hap : orderOf a = p) : ∃ g : G, g⁻¹ * a * g ∈ Q := by
  let S₀ : Sylow p G := Sylow.ofCard Q hQ
  have hS₀ : (S₀ : Subgroup G) = Q := Sylow.coe_ofCard _ _
  have hpgrp : IsPGroup p (Subgroup.zpowers a) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hap, pow_one])
  obtain ⟨S, hS⟩ := hpgrp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S₀ S
  have haS : a ∈ (S : Subgroup G) := hS (Subgroup.mem_zpowers _)
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at haS
  rw [hS₀] at haS
  refine ⟨g, ?_⟩
  simpa [MulAut.smul_def, ← map_inv, MulAut.conj_apply, mul_assoc] using haS

theorem factorization_PG_two : (Nat.card PG).factorization 2 = 9 := by
  rw [show Nat.card PG = 44352000 from card_hs100P, show (44352000 : ℕ) = 2 ^ 9 * 86625 by norm_num,
    Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  simp

theorem factorization_PG_five : (Nat.card PG).factorization 5 = 3 := by
  rw [show Nat.card PG = 44352000 from card_hs100P, show (44352000 : ℕ) = 5 ^ 3 * 354816 by norm_num,
    Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow (by norm_num), Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  simp

end CFSG.Quasithin.H13.LocDbl.HSLoc
