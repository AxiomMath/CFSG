module

import CFSG.Walter.W67.W2Lemma26C
import CFSG.Walter.W67.W1GW
import CFSG.Walter.W67.W2Cor32A
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Walter.Cited.Huppert
public import CFSG.Walter.JRFacts
public import CFSG.Walter.ReeOrder.JT.Section2

public section

namespace CFSG.Walter.W67

open scoped MatrixGroups Pointwise

theorem pow_prime_pow_mod {ℓ : ℕ} (hℓ : ℓ.Prime) (x a : ℕ) : x ^ ℓ ^ a % ℓ = x % ℓ := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have h : ((x ^ ℓ ^ a : ℕ) : ZMod ℓ) = (x : ZMod ℓ) := by
    push_cast
    exact ZMod.pow_card_pow _
  exact (ZMod.natCast_eq_natCast_iff' _ _ _).mp h

theorem pow_succ_dvd_pow_sub_one {ℓ : ℕ} (hℓ : ℓ.Prime) {x v : ℕ} (hx : 1 ≤ x) (hv : 1 ≤ v)
    (h : ℓ ^ v ∣ x - 1) : ℓ ^ (v + 1) ∣ x ^ ℓ - 1 := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hxl : 1 ≤ x ^ ℓ := Nat.one_le_pow _ _ hx
  have hgeom : ((x : ℤ) ^ ℓ - 1) = (∑ i ∈ Finset.range ℓ, (x : ℤ) ^ i) * ((x : ℤ) - 1) :=
    (geom_sum_mul (x : ℤ) ℓ).symm
  have hx1 : (x : ZMod ℓ) = 1 := by
    have h1 : ℓ ∣ x - 1 := (dvd_pow_self ℓ (by omega)).trans h
    have h2 := (ZMod.natCast_eq_zero_iff (x - 1) ℓ).mpr h1
    rw [Nat.cast_sub hx, Nat.cast_one] at h2
    exact sub_eq_zero.mp h2
  have hsum : (ℓ : ℤ) ∣ ∑ i ∈ Finset.range ℓ, (x : ℤ) ^ i := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [hx1]
    simp
  have hv' : ((ℓ : ℤ) ^ v) ∣ (x : ℤ) - 1 := by
    have := Int.natCast_dvd_natCast.mpr h
    rwa [Nat.cast_sub hx, Nat.cast_one, Nat.cast_pow] at this
  have hfin : ((ℓ : ℤ) ^ (v + 1)) ∣ (x : ℤ) ^ ℓ - 1 := by
    rw [hgeom, pow_succ, mul_comm ((ℓ : ℤ) ^ v)]
    exact mul_dvd_mul hsum hv'
  have := hfin
  rw [show ((x : ℤ) ^ ℓ - 1) = ((x ^ ℓ - 1 : ℕ) : ℤ) by push_cast [Nat.cast_sub hxl]; ring,
    show ((ℓ : ℤ) ^ (v + 1)) = ((ℓ ^ (v + 1) : ℕ) : ℤ) by push_cast; ring] at this
  exact Int.natCast_dvd_natCast.mp this

variable {G : Type} [Group G] [Finite G]

theorem eq_of_le_of_normalizer_le {ℓ : ℕ} [Fact ℓ.Prime] {P R : Subgroup G} (hR : IsPGroup ℓ R)
    (hPR : P ≤ R)
    (h : ∀ Q : Subgroup G, IsPGroup ℓ Q → P ≤ Q → Q ≤ Subgroup.normalizer (P : Set G) → Q ≤ P) :
    P = R := by
  by_contra hne
  have hlt : P.subgroupOf R < ⊤ := by
    refine lt_of_le_of_ne le_top fun htop => hne (le_antisymm hPR fun x hx => ?_)
    have : (⟨x, hx⟩ : R) ∈ P.subgroupOf R := htop ▸ Subgroup.mem_top _
    exact this
  have hnil : Group.IsNilpotent R := hR.isNilpotent
  obtain ⟨y, hyN, hyP⟩ := IsConcreteLE.exists_of_lt
    (Group.normalizerCondition_of_isNilpotent (P.subgroupOf R) hlt)
  have hyNP : (y : G) ∈ Subgroup.normalizer (P : Set G) := by
    refine JT.mem_normalizer_of_conj_mem fun x hx => ?_
    exact (Subgroup.mem_normalizer_iff.mp hyN ⟨x, hPR hx⟩).mp hx
  have hQ := h (R ⊓ Subgroup.normalizer (P : Set G)) (hR.to_le inf_le_left)
    (le_inf hPR Subgroup.le_normalizer) inf_le_right
  exact hyP (hQ ⟨y.2, hyNP⟩)

theorem eq_of_le_of_factorization_le {ℓ : ℕ} [Fact ℓ.Prime] {P R : Subgroup G}
    (hR : IsPGroup ℓ R) (hPR : P ≤ R)
    (hP : (Nat.card (Subgroup.normalizer (P : Set G))).factorization ℓ ≤
      (Nat.card P).factorization ℓ) : P = R := by
  refine eq_of_le_of_normalizer_le hR hPR fun Q hQ hPQ hQN => ?_
  have hQP : Nat.card Q ≤ Nat.card P := by
    obtain ⟨k, hk⟩ := hQ.exists_card_eq
    obtain ⟨m, hm⟩ := (hR.to_le hPR).exists_card_eq
    have h1 : ℓ ^ k ∣ Nat.card (Subgroup.normalizer (P : Set G)) :=
      hk ▸ Subgroup.card_dvd_of_le hQN
    have h2 := (Nat.Prime.pow_dvd_iff_le_factorization Fact.out Nat.card_pos.ne').mp h1
    rw [hm, Nat.factorization_pow_self Fact.out] at hP
    rw [hk, hm]
    exact Nat.pow_le_pow_right (Nat.Prime.pos Fact.out) (h2.trans hP)
  exact (Subgroup.eq_of_le_of_card_ge hPQ hQP).symm.le

theorem false_of_perfect_of_le_centralizer {X : Type} [Group X] [Finite X]
    (hperf : commutator X = ⊤) {ℓ : ℕ} [Fact ℓ.Prime] (hℓ : ℓ ≠ 2) (P : Sylow ℓ X)
    (hP : (P : Subgroup X) ≠ ⊥)
    (hNC : Subgroup.normalizer ((P : Subgroup X) : Set X) ≤
      Subgroup.centralizer ((P : Subgroup X) : Set X)) : False := by
  set D := (MonoidHom.transferSylow P hNC).ker with hD
  have hcomp : Subgroup.IsComplement' D P := MonoidHom.ker_transferSylow_isComplement' P hNC
  have hDn : D.Normal := MonoidHom.normal_ker _
  have hidx : D.index = Nat.card (P : Subgroup X) := hcomp.symm.index_eq_card
  have hodd : Odd D.index := by
    rw [hidx]
    obtain ⟨k, hk⟩ := P.isPGroup'.exists_card_eq
    rw [hk]
    exact (Nat.Prime.odd_of_ne_two Fact.out hℓ).pow
  have htop := eq_top_of_odd_index_of_perfect hperf hodd
  rw [htop, Subgroup.index_top] at hidx
  exact hP (Subgroup.card_eq_one.mp hidx.symm)

theorem false_of_perfect_of_metacyclic {X : Type} [Group X] [Finite X]
    (hperf : commutator X = ⊤) {ℓ : ℕ} [Fact ℓ.Prime] (hℓ : ℓ ≠ 2) (P : Sylow ℓ X)
    (hnc : ¬ IsMulCommutative (P : Subgroup X)) (hmc : JT.IsMetacyclic (P : Subgroup X)) :
    False := by
  obtain ⟨N, hN, hNtop, hNp⟩ := huppertMetacyclicTheorem X ℓ hℓ P hnc hmc
  have hodd : Odd N.index := by
    rw [Subgroup.index_eq_card]
    obtain ⟨k, hk⟩ := hNp.exists_card_eq
    rw [hk]
    exact (Nat.Prime.odd_of_ne_two Fact.out hℓ).pow
  exact hNtop (eq_top_of_odd_index_of_perfect hperf hodd)

theorem exists_sylow_mem_normalizer_of_two {X : Type} [Group X] [Finite X] {ℓ : ℕ}
    [Fact ℓ.Prime] (hℓ : ℓ ≠ 2) (hX2 : (Nat.card X).factorization 2 = 1) {j : X}
    (hj : j ≠ 1) (hj2 : j * j = 1) :
    ∃ R : Sylow ℓ X, j ∈ Subgroup.normalizer ((R : Subgroup X) : Set X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hjo : orderOf j = 2 := orderOf_eq_prime (by rw [pow_two]; exact hj2) hj
  have hPcard : Nat.card (Subgroup.zpowers j) = 2 ^ (Nat.card X).factorization 2 := by
    rw [Nat.card_zpowers, hjo, hX2, pow_one]
  set P₂ : Sylow 2 X := Sylow.ofCard (Subgroup.zpowers j) hPcard
  have hP₂ : (P₂ : Subgroup X) = Subgroup.zpowers j := Sylow.coe_ofCard _ _
  have hNC : Subgroup.normalizer ((P₂ : Subgroup X) : Set X) ≤
      Subgroup.centralizer ((P₂ : Subgroup X) : Set X) := by
    intro n hn
    rw [hP₂] at hn ⊢
    have h1 : n * j * n⁻¹ ∈ Subgroup.zpowers j :=
      (Subgroup.mem_normalizer_iff.mp hn j).mp (Subgroup.mem_zpowers j)
    have hcomm : Commute j n := by
      rcases eq_one_or_eq_of_mem_zpowers hjo h1 with h | h
      · exfalso
        apply hj
        have := congrArg (fun z => n⁻¹ * z * n) h
        simpa [mul_assoc] using this
      · exact (show j * n = n * j by
          calc j * n = (n * j * n⁻¹) * n := by rw [h]
            _ = n * j := by group)
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    exact (Commute.zpow_left hcomm k).eq
  set M := (MonoidHom.transferSylow P₂ hNC).ker with hM
  have hcomp : Subgroup.IsComplement' M P₂ := MonoidHom.ker_transferSylow_isComplement' P₂ hNC
  have hMn : M.Normal := MonoidHom.normal_ker _
  have hMidx : M.index = 2 := by
    rw [hcomp.symm.index_eq_card, hP₂, Nat.card_zpowers, hjo]
  have hMcard : Nat.card M * 2 = Nat.card X := by
    rw [← hMidx]
    exact M.card_mul_index
  have hModd : Odd (Nat.card M) := by
    by_contra hev
    rw [Nat.not_odd_iff_even] at hev
    obtain ⟨m, hm⟩ := hev
    have h4 : 2 ^ 2 ∣ Nat.card X := ⟨m, by rw [← hMcard, hm]; ring⟩
    have := (Nat.prime_two.pow_dvd_iff_le_factorization Nat.card_pos.ne').mp h4
    omega
  obtain ⟨R₀⟩ : Nonempty (Sylow ℓ X) := inferInstance
  have hR₀M : (R₀ : Subgroup X) ≤ M := fun x hx => by
    apply mem_of_index_two_of_odd hMidx
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp R₀.isPGroup') ⟨x, hx⟩
    rw [Subgroup.orderOf_mk] at hk
    rw [hk]
    exact (Nat.Prime.odd_of_ne_two Fact.out hℓ).pow
  have hMtop : (M.subgroupOf (⊤ : Subgroup X)).Normal := hMn.subgroupOf ⊤
  have hsup : M ⊔ Subgroup.normalizer ((R₀ : Subgroup X) : Set X) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    obtain ⟨m, hm, hmx⟩ := exists_mul_mem_normalizer hMtop le_top R₀ hR₀M (Subgroup.mem_top x)
    have : x = m⁻¹ * (m * x) := by group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (M.inv_mem hm)) (Subgroup.mem_sup_right hmx)
  have hcard := card_sup_mul_card_inf_of_le_normalizer
    (A := M) (B := Subgroup.normalizer ((R₀ : Subgroup X) : Set X))
    Subgroup.le_normalizer_of_normal
  rw [hsup, Subgroup.card_top] at hcard
  have hSodd : Odd (Nat.card (Sylow ℓ X)) := by
    rw [Sylow.card_eq_index_normalizer R₀]
    have h1 := (Subgroup.normalizer ((R₀ : Subgroup X) : Set X)).card_mul_index
    have h2 : (Subgroup.normalizer ((R₀ : Subgroup X) : Set X)).index *
        Nat.card (M ⊓ Subgroup.normalizer ((R₀ : Subgroup X) : Set X) : Subgroup X) =
        Nat.card M := by
      apply Nat.eq_of_mul_eq_mul_left
        (Nat.card_pos (α := Subgroup.normalizer ((R₀ : Subgroup X) : Set X)))
      calc Nat.card (Subgroup.normalizer ((R₀ : Subgroup X) : Set X)) *
            ((Subgroup.normalizer ((R₀ : Subgroup X) : Set X)).index *
              Nat.card (M ⊓ Subgroup.normalizer ((R₀ : Subgroup X) : Set X) : Subgroup X))
          = (Nat.card (Subgroup.normalizer ((R₀ : Subgroup X) : Set X)) *
              (Subgroup.normalizer ((R₀ : Subgroup X) : Set X)).index) *
            Nat.card (M ⊓ Subgroup.normalizer ((R₀ : Subgroup X) : Set X) : Subgroup X) := by
            ring
        _ = Nat.card X *
            Nat.card (M ⊓ Subgroup.normalizer ((R₀ : Subgroup X) : Set X) : Subgroup X) := by
            rw [h1]
        _ = Nat.card M * Nat.card (Subgroup.normalizer ((R₀ : Subgroup X) : Set X)) := hcard
        _ = _ := by ring
    exact Odd.of_dvd_nat hModd (Dvd.intro _ h2)
  have hj2g : IsPGroup 2 (Subgroup.zpowers j) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hjo, pow_one])
  have hmod := hj2g.card_modEq_card_fixedPoints (Sylow ℓ X)
  have hfix : Nat.card (MulAction.fixedPoints (Subgroup.zpowers j) (Sylow ℓ X)) ≠ 0 := by
    intro h0
    rw [h0] at hmod
    have := Nat.odd_iff.mp hSodd
    have h' : Nat.card (Sylow ℓ X) % 2 = 0 := hmod
    omega
  obtain ⟨⟨R, hR⟩⟩ := (Nat.card_ne_zero.mp hfix).1
  refine ⟨R, ?_⟩
  have h1 : (⟨j, Subgroup.mem_zpowers j⟩ : Subgroup.zpowers j) • R = R := hR _
  exact (Sylow.smul_eq_iff_mem_normalizer).mp h1

end CFSG.Walter.W67
