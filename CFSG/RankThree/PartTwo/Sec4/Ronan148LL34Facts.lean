module

public import CFSG.RankThree.PartTwo.KFacts.L34PGLFusionFacts
public import CFSG.RankThree.PartTwo.KFacts.L34Models
public import CFSG.RankThree.PartTwo.KFacts.KS18OuterHeisCore

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148L

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.RankThree.PartTwo.KFacts

section L34

variable {k : Type} [Field k] (hk : Nat.card k = 4) {X : Type*} [Group X]
  (χ : X ≃* projectiveSL 3 k)
include hk χ

theorem l34_card : Nat.card X = 20160 := by
  rw [Nat.card_congr χ.toEquiv, L34.card_projectiveSL hk]

theorem l34_finite : Finite X :=
  Nat.finite_of_card_ne_zero (by rw [l34_card hk χ]; norm_num)

theorem l34_mulAut_card : Nat.card (MulAut X) = 241920 := by
  rw [Nat.card_congr (MulAut.congr χ).toEquiv, L34.card_mulAut hk]

theorem l34_card_le_nine {B : Subgroup (MulAut X)} (hB : CFSG.Assembly.IsElemAbelian 3 B) :
    Nat.card B ≤ 9 := by
  haveI : Finite (MulAut X) :=
    Nat.finite_of_card_ne_zero (by rw [l34_mulAut_card hk χ]; norm_num)
  have := hB.1
  haveI : CFSG.IsElementaryAbelian 3 B :=
    { toIsMulCommutative := hB.1
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun a =>
        Subtype.ext (hB.2 _ a.2) }
  exact KS18.card_le_nine_of_pRank (L34.pRank_three_mulAut_of_mulEquiv hk χ) B

theorem l34_pow_three {Q : Subgroup X} (hQ : IsPGroup 3 Q) {x : X} (hx : x ∈ Q) : x ^ 3 = 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI := l34_finite hk χ
  have hd := L34.card_dvd_9_of_isPGroup hk χ hQ
  rw [show (9 : ℕ) = 3 ^ 2 by norm_num] at hd
  have hQ9 : ∀ Q' : Subgroup X, Nat.card Q' = 9 → ∀ y ∈ Q', y ^ 3 = 1 := by
    intro Q' hQ' y hy
    have hE : Nat.card (Q'.map χ.toMonoidHom) = 9 := by
      rw [Subgroup.card_map_of_injective χ.injective, hQ']
    haveI := L34.isElementaryAbelian_of_card_eq_nine hk hE
    have h1 : χ y ^ 3 = 1 :=
      CFSG.elemPow_eq_one_of_isElementaryAbelian (A := Q'.map χ.toMonoidHom) (χ y)
        (Subgroup.mem_map_of_mem _ hy)
    apply χ.injective
    rw [map_pow, map_one]
    exact h1
  rcases (Nat.dvd_prime_pow Nat.prime_three).mp hd with ⟨m, hm, hQm⟩
  interval_cases m
  · rw [pow_zero] at hQm
    have : x = 1 := by
      have h := Subgroup.card_eq_one.mp hQm
      rw [h] at hx
      exact hx
    rw [this, one_pow]
  · have := pow_card_eq_one' (G := Q) (x := ⟨x, hx⟩)
    rw [hQm, pow_one] at this
    exact congrArg Subtype.val this
  · exact hQ9 Q (by rw [hQm]; norm_num) x hx

theorem l34_comm_of_isPGroup {Q : Subgroup X} (hQ : IsPGroup 3 Q) {a b : X} (ha : a ∈ Q)
    (hb : b ∈ Q) : a * b = b * a := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI := l34_finite hk χ
  have hd := L34.card_dvd_9_of_isPGroup hk χ hQ
  rw [show (9 : ℕ) = 3 ^ 2 by norm_num] at hd
  rcases (Nat.dvd_prime_pow Nat.prime_three).mp hd with ⟨m, hm, hQm⟩
  interval_cases m
  · have h := Subgroup.card_eq_one.mp (by rw [hQm, pow_zero])
    rw [h] at ha hb
    rw [Subgroup.mem_bot.mp ha, Subgroup.mem_bot.mp hb]
  · haveI : Fact (Nat.Prime (3 ^ 1)) := ⟨by norm_num⟩
    have hcyc : IsCyclic Q := isCyclic_of_prime_card hQm
    letI := hcyc.commGroup
    exact congrArg Subtype.val (mul_comm (⟨a, ha⟩ : Q) ⟨b, hb⟩)
  · have hE : Nat.card (Q.map χ.toMonoidHom) = 9 := by
      rw [Subgroup.card_map_of_injective χ.injective, hQm]; norm_num
    have hEab := L34.isElementaryAbelian_of_card_eq_nine hk hE
    have h1 := hEab.toIsMulCommutative.is_comm.comm (⟨χ a, a, ha, rfl⟩ : Q.map χ.toMonoidHom)
      ⟨χ b, b, hb, rfl⟩
    apply χ.injective
    rw [map_mul, map_mul]
    exact congrArg Subtype.val h1

theorem l34_card_centralizer {y : X} (hy3 : y ^ 3 = 1) (hy1 : y ≠ 1) :
    Nat.card (Subgroup.centralizer ({y} : Set X)) = 9 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite (projectiveSL 3 k) :=
    Nat.finite_of_card_ne_zero (by rw [L34.card_projectiveSL hk]; norm_num)
  have hy3' : (χ y) ^ 3 = 1 := by rw [← map_pow, hy3, map_one]
  have hy1' : χ y ≠ 1 := by rw [Ne, map_eq_one_iff _ χ.injective]; exact hy1
  have hp : IsPGroup 3 (Subgroup.zpowers (χ y)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, orderOf_eq_prime hy3' hy1', pow_one])
  obtain ⟨Q, hQ⟩ := hp.exists_le_sylow
  have hQ9 : Nat.card (Q : Subgroup (projectiveSL 3 k)) = 9 := by
    rw [Sylow.card_eq_multiplicity, L34.factorization_card hk]; norm_num
  have hC := L34.centralizer_eq_of_card_eq_nine hk hQ9 (hQ (Subgroup.mem_zpowers _)) hy1'
  rw [← hQ9, ← hC]
  refine Nat.card_congr (χ.toEquiv.subtypeEquiv fun c => ?_)
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff,
    MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, ← map_mul, ← map_mul, χ.injective.eq_iff]

theorem l34_mulAut_finite : Finite (MulAut X) :=
  Nat.finite_of_card_ne_zero (by rw [l34_mulAut_card hk χ]; norm_num)

end L34

section SL

variable {k : Type} [Field k] (hk : Nat.card k = 4)
include hk

theorem sl34_pow_three {M : Matrix.SpecialLinearGroup (Fin 3) k} (hM : proj 3 k M ^ 3 = 1) :
    M ^ 3 = 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite (projectiveSL 3 k) :=
    Nat.finite_of_card_ne_zero (by rw [L34.card_projectiveSL hk]; norm_num)
  have hp : IsPGroup 3 (Subgroup.zpowers (proj 3 k M)) := by
    by_cases h1 : proj 3 k M = 1
    · rw [h1, Subgroup.zpowers_one_eq_bot]
      exact IsPGroup.of_bot
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, orderOf_eq_prime hM h1, pow_one])
  obtain ⟨Q, hQ⟩ := hp.exists_le_sylow
  have hQ9 : Nat.card (Q : Subgroup (projectiveSL 3 k)) = 9 := by
    rw [Sylow.card_eq_multiplicity, L34.factorization_card hk]; norm_num
  have hH := L34.isHeisThree_comap_proj hk hQ9
  have hMQ : M ∈ (Q : Subgroup (projectiveSL 3 k)).comap (proj 3 k) :=
    hQ (Subgroup.mem_zpowers _)
  have hexp := hH.2.2
  have h := Monoid.pow_exponent_eq_one
    (⟨M, hMQ⟩ : ↥((Q : Subgroup (projectiveSL 3 k)).comap (proj 3 k)))
  rw [hexp] at h
  exact congrArg Subtype.val h

end SL

end CFSG.RankThree.PartTwo.Sec4.Ronan148L
