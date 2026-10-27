module

public import CFSG.Quasithin.Vol2.Ch1Sec3Basic

public section

namespace CFSG.Quasithin.S15223

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G]

theorem exists_sylow_three_oTwoUpper {T H : Subgroup G} (hTH : T ≤ H) (hT2 : IsPGroup 2 T)
    (hT9 : T.relIndex H = 9) :
    ∃ P : Subgroup G, P ≤ oTwoUpper H ∧ IsSylowIn 3 P (oTwoUpper H) ∧ Nat.card P = 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨a, ha⟩ := hT2.exists_card_eq
  have h := Subgroup.relIndex_mul_card T H
  rw [inf_eq_left.2 hTH, hT9] at h
  obtain ⟨P, hP, -⟩ := exists_isSylowIn_ge 3 (bot_le : ⊥ ≤ H) IsPGroup.of_bot
  have hfac : (Nat.card H).factorization 3 = 2 := by
    rw [← h, ha, Nat.factorization_mul (by norm_num) (pow_ne_zero _ two_ne_zero),
      Finsupp.add_apply, show (9 : ℕ) = 3 ^ 2 by norm_num,
      Nat.Prime.factorization_pow Nat.prime_three, Nat.Prime.factorization_pow Nat.prime_two]
    simp
  have hPc : Nat.card P = 9 := by
    rw [hP.card_eq, hfac]
    norm_num
  have hPK : P ≤ oTwoUpper H := fun x hx => by
    refine mem_oTwoUpper_of_odd (hP.le hx) ?_
    obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hP.isPGroup ⟨x, hx⟩
    have : orderOf x = 3 ^ k := by rw [← Subgroup.orderOf_coe] at hk; exact hk
    rw [this]
    exact Odd.pow (by decide)
  refine ⟨P, hPK, ⟨hPK, hP.isPGroup, fun hdvd => hP.not_dvd_relIndex ?_⟩, hPc⟩
  have h1 := Subgroup.relIndex_mul_relIndex P (oTwoUpper H) H hPK (oTwoUpper_le H)
  rw [← h1]
  exact Dvd.dvd.mul_right hdvd _

theorem isElemAbelian_of_isXi_sylow {T K P : Subgroup G} (hX : IsXi T K) (hP : IsSylowIn 3 P K)
    (hP9 : Nat.card P = 9) : IsElemAbelian 3 P := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3K : 3 ∣ Nat.card K :=
    ((by rw [hP9]; norm_num : 3 ∣ Nat.card P).trans (Subgroup.card_dvd_of_le hP.le))
  have hc : IsMulCommutative ↥P :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) (by rw [hP9]; norm_num)
  exact ⟨hc, fun x hx => hX.pow_eq_one (by norm_num) h3K hP hx⟩

theorem isSolvable_of_isXi_sylow {T K P : Subgroup G} (hX : IsXi T K) (hP : IsSylowIn 3 P K)
    (hP9 : Nat.card P = 9) : Group.IsSolvable ↥K := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3K : 3 ∣ Nat.card K :=
    ((by rw [hP9]; norm_num : 3 ∣ Nat.card P).trans (Subgroup.card_dvd_of_le hP.le))
  have hc : ∀ a b : ↥P, a * b = b * a := fun a b =>
    (IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) (by rw [hP9]; norm_num)).is_comm.comm
      a b
  have hPP : ⁅P, P⁆ = ⊥ := by
    refine (Subgroup.commutator_eq_bot_iff_le_centralizer).mpr fun a ha => ?_
    refine Subgroup.mem_centralizer_iff.mpr fun b hb => ?_
    exact congrArg Subtype.val (hc ⟨b, hb⟩ ⟨a, ha⟩)
  have hKK : ⁅K, K⁆ ≤ pCoreOf 2 K := by
    have := hX.commutator_le (by norm_num) h3K hP
    rwa [hPP, sup_bot_eq] at this
  have hN2 : IsPGroup 2 ((pCoreOf 2 K).subgroupOf K) := (pCoreOf_isPGroup 2 K).comap_subtype
  have hcomm_le : commutator ↥K ≤ (pCoreOf 2 K).subgroupOf K := by
    rw [commutator_def]
    refine Subgroup.commutator_le.mpr fun a _ b _ => ?_
    rw [Subgroup.mem_subgroupOf]
    exact hKK (Subgroup.commutator_mem_commutator a.2 b.2)
  have hC2 : IsPGroup 2 ↥(commutator ↥K) := hN2.to_le hcomm_le
  have : Group.IsNilpotent ↥(commutator ↥K) := hC2.isNilpotent
  exact Group.isSolvable_commutator_iff.mp inferInstance

end CFSG.Quasithin.S15223
