module

public import CFSG.Quasithin.H13.L32AC43c
public import CFSG.Quasithin.H13.L32AC36c

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open hiding StatedSL StatedSU StatedSp StatedProj StatedClassicalModel
open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin
open CFSG.Assembly.LowTwoRank
open scoped IsMulCommutative

theorem card_psu3_eight {F : Type} [Field F] [Finite F] (hF : Nat.card F = (2 ^ 3) ^ 2) :
    Nat.card (StatedProj (StatedSU 3 (2 ^ 3) F)) = 5515776 := by
  rw [CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSU Nat.prime_two (by norm_num) hF
    (by norm_num)]
  decide

theorem false_of_d310Two_u38 {W : Type} [CommGroup W] [Finite W] {T L : Subgroup (MulAut W)}
    {U : Subgroup W} (h : D310Two T L U) {z : ℕ} (hz : Odd z)
    (hc : Nat.card L = z * 5515776) : False := by
  have hv : padicValNat 2 (Nat.card L) = 9 := by
    rw [hc, show z * 5515776 = 2 ^ 9 * (z * 10773) by ring]
    exact padicValNat_two_pow_mul_odd (hz.mul (by decide))
  have hz1 : 1 ≤ z := hz.pos
  obtain ⟨hcases, -, -⟩ := h
  rcases hcases with ⟨n, K, _, _, hK, π, hπ⟩ | ⟨n, K, _, _, hK, π, hπ⟩ | ⟨π, hπ⟩ |
    ⟨K, _, _, hK, π, hπ⟩ | ⟨K, _, _, hK, π, hπ⟩ | ⟨α, π, hπ⟩
  ·
    have hn := one_le_of_card_field hK
    have hinj := G64.RealizesVia.injective_of_faithful' (FFModel.nat_faithful _) hπ
    have hX0 : Nat.card L = Nat.card ↥(StatedSL 3 K) :=
      (Nat.card_congr (MulEquiv.ofBijective π ⟨hinj, hπ.1⟩).toEquiv).symm
    have hX : Nat.card L = 2 ^ (n * 3) * ((2 ^ (n * 2) - 1) * (2 ^ (n * 3) - 1)) := by
      rw [hX0, card_statedSL_three1527d, hK, ← pow_mul, ← pow_mul]
    have h3 : n * 3 = 9 := by
      rw [hX, padicValNat_two_pow_mul_odd ((odd_two_pow_sub_one_of_pos (by omega)).mul
        (odd_two_pow_sub_one_of_pos (by omega)))] at hv
      exact hv
    obtain rfl : n = 3 := by omega
    rw [hX] at hc
    norm_num at hc
    omega
  ·
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
    have h1 := Nat.card_le_card_of_surjective (α := ↥(alternatingGroup (Fin 6))) π hπ.1
    rw [card_alternatingGroup1527d 6 (by norm_num)] at h1
    norm_num [Nat.factorial] at h1
    omega
  ·
    have h1 := Nat.card_le_card_of_surjective (α := ↥(StatedSL 4 K)) π hπ.1
    rw [card_statedSL1527d (d := 4) (by norm_num), hK] at h1
    norm_num [Finset.prod_Icc_succ_top] at h1
    omega
  ·
    have hinj := G64.RealizesVia.injective_of_faithful' (FFModel.nat_faithful _) hπ
    have hX : Nat.card L = Nat.card ↥(StatedSL 5 K) :=
      (Nat.card_congr (MulEquiv.ofBijective π ⟨hinj, hπ.1⟩).toEquiv).symm
    rw [hX, card_statedSL1527d (d := 5) (by norm_num), hK] at hc
    norm_num [Finset.prod_Icc_succ_top] at hc
    omega
  ·
    have h1 := Nat.card_le_card_of_surjective (α := ↥(alternatingGroup (Fin 7))) π hπ.1
    have h2 : Nat.card ↥(alternatingGroup (Fin 7)) = 2520 := by
      rw [card_alternatingGroup1527d 7 (by norm_num)]
      norm_num [Nat.factorial]
    omega

variable {G : Type} [Group G] [Finite G] {T L V H : Subgroup G}

namespace Top43

variable {W K : Subgroup G} (C : Top43 T L V H W K) [IsMulCommutative ↥(conjClosure V H)]
include C

@[expose] noncomputable def autKHom : ↥K →* ↥C.autK :=
  (C.act.comp (Subgroup.inclusion C.hKH)).codRestrict _
    (fun k => ⟨⟨(k : G), C.hKH k.2⟩, Subgroup.mem_subgroupOf.mpr k.2, rfl⟩)

theorem le_ker_autKHom : (pCoreOf 2 K).subgroupOf K ≤ C.autKHom.ker := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hO2K : pCoreOf 2 K ≤ pCoreOf 2 H :=
    A4.pCoreOf_le_of_subnormal 2 (subnormal_of_mem_cComp C.hK)
  intro k hk
  rw [MonoidHom.mem_ker]
  exact Subtype.ext (C.act_eq_one_of_mem (h := ⟨k, C.hKH k.2⟩)
    (hO2K (Subgroup.mem_subgroupOf.mp hk)))

@[expose] noncomputable def autKSurj : cStar K →* ↥C.autK :=
  QuotientGroup.lift _ C.autKHom C.le_ker_autKHom

theorem autKSurj_surjective : Function.Surjective C.autKSurj := by
  intro y
  obtain ⟨x, hx, hxy⟩ := y.2
  exact ⟨QuotientGroup.mk ⟨(x : G), Subgroup.mem_subgroupOf.mp hx⟩, Subtype.ext hxy⟩

theorem nonempty_quotCenter_autK (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2)
    (h1334 : A6.Stmt13_3_4) :
    Nonempty ((cStar K ⧸ Subgroup.center (cStar K)) ≃*
      (↥C.autK ⧸ Subgroup.center ↥C.autK)) := by
  refine quotCenter_mulEquiv_of_central_ker C.autKSurj C.autKSurj_surjective ?_ ?_
  · rcases CFSG.LieType.CurtisTits.le_center_or_eq_top_of_isQuasisimple C.hq C.autKSurj.ker
      with h | h
    · exact h
    · exfalso
      obtain ⟨x, hxK, -, hx1⟩ := C.exists_act_ne_one h1222 h1332 h1334
      apply hx1
      have h1 : C.autKSurj (QuotientGroup.mk ⟨x, hxK⟩) = 1 := by
        rw [← MonoidHom.mem_ker, h]
        exact Subgroup.mem_top _
      exact congrArg Subtype.val h1
  · have := C.hq.1.commutator_eq_top
    rwa [_root_.commutator_def] at this

theorem odd_card_center_autK (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2)
    (h1334 : A6.Stmt13_3_4) : Odd (Nat.card (Subgroup.center ↥C.autK)) := by
  refine odd_card_center_of_pCore_eq_bot ?_
  have h := C.pCoreOf_autK h1222 h1332 h1334
  rw [pCoreOf, Subgroup.map_eq_bot_iff_of_injective _ C.autK.subtype_injective] at h
  exact h

theorem card_autK_of_isPSU (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4)
    (hU : IsPSU 3 2 3 (cStar K ⧸ Subgroup.center (cStar K))) :
    ∃ z : ℕ, Odd z ∧ Nat.card ↥C.autK = z * 5515776 := by
  obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := hU
  obtain ⟨φ⟩ := C.nonempty_quotCenter_autK h1222 h1332 h1334
  refine ⟨Nat.card (Subgroup.center ↥C.autK), C.odd_card_center_autK h1222 h1332 h1334, ?_⟩
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥C.autK),
    ← Nat.card_congr φ.toEquiv, Nat.card_congr e.toEquiv, card_psu3_eight hF, mul_comm]

end Top43

end CFSG.Quasithin.H13.L32A.C
