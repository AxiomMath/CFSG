module

public import CFSG.Quasithin.H13.L32AC43d
public import CFSG.Quasithin.Background.B69Iso

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open hiding StatedSL StatedSU StatedSp StatedProj StatedClassicalModel StatedScalars
open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin
open CFSG.Assembly.LowTwoRank
open scoped IsMulCommutative

theorem card_psl34 {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2 ^ 2) :
    Nat.card (StatedProj (StatedSL 3 F)) = 20160 := by
  rw [CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL (by norm_num), hF]
  decide

theorem d310Two_psl34 {W : Type} [CommGroup W] [Finite W] {T L : Subgroup (MulAut W)}
    {U : Subgroup W} (h : D310Two T L U) {z : ℕ} (hz : Odd z)
    (hc : Nat.card L = z * 20160) (hZ : Nat.card (Subgroup.center ↥L) = z)
    (hP : IsPSL 3 2 2 (↥L ⧸ Subgroup.center ↥L)) :
    z = 3 ∧ BinaryNaturalSL L U (U ⊓ fixV L) 3 2 := by
  have hv : padicValNat 2 (Nat.card L) = 6 := by
    rw [hc, show z * 20160 = 2 ^ 6 * (z * 315) by ring]
    exact padicValNat_two_pow_mul_odd (hz.mul (by decide))
  have hz1 : 1 ≤ z := hz.pos
  have hz2 : z % 2 = 1 := Nat.odd_iff.mp hz
  obtain ⟨hcases, -, -⟩ := h
  rcases hcases with ⟨n, hn⟩ | ⟨n, K, _, _, hK, π, hπ⟩ | ⟨π, hπ⟩ |
    ⟨K, _, _, hK, π, hπ⟩ | ⟨K, _, _, hK, π, hπ⟩ | ⟨α, π, hπ⟩
  ·
    obtain ⟨K, _, _, hK, π, hπ⟩ := hn
    have hn := one_le_of_card_field hK
    have hinj := G64.RealizesVia.injective_of_faithful' (FFModel.nat_faithful _) hπ
    have hX0 : Nat.card L = Nat.card ↥(StatedSL 3 K) :=
      (Nat.card_congr (MulEquiv.ofBijective π ⟨hinj, hπ.1⟩).toEquiv).symm
    have hX : Nat.card L = 2 ^ (n * 3) * ((2 ^ (n * 2) - 1) * (2 ^ (n * 3) - 1)) := by
      rw [hX0, card_statedSL_three1527d, hK, ← pow_mul, ← pow_mul]
    have h3 : n * 3 = 6 := by
      rw [hX, padicValNat_two_pow_mul_odd ((odd_two_pow_sub_one_of_pos (by omega)).mul
        (odd_two_pow_sub_one_of_pos (by omega)))] at hv
      exact hv
    obtain rfl : n = 2 := by omega
    refine ⟨?_, K, inferInstance, inferInstance, hK, π, hπ⟩
    rw [hX] at hc
    norm_num at hc
    omega
  ·
    exfalso
    have hn := one_le_of_card_field hK
    have hinj := G64.RealizesVia.injective_of_faithful' (FFModel.nat_faithful _) hπ
    have hI : Finset.Icc 1 2 = {1, 2} := by decide
    have hX0 : Nat.card L = Nat.card ↥(StatedSp 2 K) :=
      (Nat.card_congr (MulEquiv.ofBijective π ⟨hinj, hπ.1⟩).toEquiv).symm
    have hX : Nat.card L = 2 ^ (n * 4) * ((2 ^ (n * 2) - 1) * (2 ^ (n * 4) - 1)) := by
      rw [hX0, CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp, hK, hI,
        Finset.prod_pair (by norm_num), ← pow_mul, ← pow_mul, ← pow_mul]
      norm_num
    rw [hX, padicValNat_two_pow_mul_odd ((odd_two_pow_sub_one_of_pos (by omega)).mul
      (odd_two_pow_sub_one_of_pos (by omega)))] at hv
    omega
  ·
    exfalso
    have h1 := Nat.card_le_card_of_surjective (α := ↥(alternatingGroup (Fin 6))) π hπ.1
    rw [card_alternatingGroup1527d 6 (by norm_num)] at h1
    norm_num [Nat.factorial] at h1
    omega
  ·
    exfalso
    have hinj := G64.RealizesVia.injective_of_faithful' (FFModel.nat_faithful _) hπ
    let φ : ↥(StatedSL 4 K) ≃* ↥L := MulEquiv.ofBijective π ⟨hinj, hπ.1⟩
    have h4 : Nat.card ↥(StatedSL 4 K) = 20160 := by
      rw [card_statedSL1527d (d := 4) (by norm_num), hK]
      norm_num [Finset.prod_Icc_succ_top]
    have hX : Nat.card L = 20160 := by rw [← Nat.card_congr φ.toEquiv, h4]
    have hzz : z = 1 := by omega
    have hZbot : Subgroup.center ↥L = ⊥ := Subgroup.eq_bot_of_card_eq _ (by rw [hZ, hzz])
    obtain ⟨-, F, _, _, hF, ⟨e3⟩⟩ := hP
    have e0 : (↥L ⧸ Subgroup.center ↥L) ≃* ↥L :=
      (QuotientGroup.quotientMulEquivOfEq hZbot).trans QuotientGroup.quotientBot
    have hq4 : Nat.card (StatedProj (StatedSL 4 K)) = 20160 := by
      rw [CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL (by norm_num), hK]
      decide
    have hbij := (QuotientGroup.mk'_surjective
      ((StatedScalars (Fin 4) K).subgroupOf (StatedSL 4 K))).bijective_of_nat_card_le
        (by rw [h4, hq4])
    exact B69.not_equiv_sl_four_psl_three (K := K) (F := F) (by rw [hK]; norm_num)
      (by rw [hF]; norm_num) (e0.trans (φ.symm.trans (MulEquiv.ofBijective _ hbij))) e3
  ·
    exfalso
    have hinj := G64.RealizesVia.injective_of_faithful' (FFModel.nat_faithful _) hπ
    have hX : Nat.card L = Nat.card ↥(StatedSL 5 K) :=
      (Nat.card_congr (MulEquiv.ofBijective π ⟨hinj, hπ.1⟩).toEquiv).symm
    rw [hX, card_statedSL1527d (d := 5) (by norm_num), hK] at hc
    norm_num [Finset.prod_Icc_succ_top] at hc
    omega
  ·
    exfalso
    have h1 := Nat.card_le_card_of_surjective (α := ↥(alternatingGroup (Fin 7))) π hπ.1
    have h2 : Nat.card ↥(alternatingGroup (Fin 7)) = 2520 := by
      rw [card_alternatingGroup1527d 7 (by norm_num)]
      norm_num [Nat.factorial]
    omega

variable {G : Type} [Group G] [Finite G] {T L V H : Subgroup G}

namespace Top43

variable {W K : Subgroup G} (C : Top43 T L V H W K) [IsMulCommutative ↥(conjClosure V H)]
include C

theorem card_autK_of_isPSL34 (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2)
    (h1334 : A6.Stmt13_3_4) (hP : IsPSL 3 2 2 (cStar K ⧸ Subgroup.center (cStar K))) :
    Odd (Nat.card (Subgroup.center ↥C.autK)) ∧
      Nat.card ↥C.autK = Nat.card (Subgroup.center ↥C.autK) * 20160 ∧
      IsPSL 3 2 2 (↥C.autK ⧸ Subgroup.center ↥C.autK) := by
  obtain ⟨φ⟩ := C.nonempty_quotCenter_autK h1222 h1332 h1334
  refine ⟨C.odd_card_center_autK h1222 h1332 h1334, ?_, isPSL_congr φ hP⟩
  obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := hP
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥C.autK),
    ← Nat.card_congr φ.toEquiv, Nat.card_congr e.toEquiv, card_psl34 hF, mul_comm]

end Top43

end CFSG.Quasithin.H13.L32A.C
