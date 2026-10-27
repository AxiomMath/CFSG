module

public import CFSG.Quasithin.Background.F918Z8Op4b1
import CFSG.Sporadic.Bridge.J1
public import CFSG.Sporadic.Bridge.Common

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique
open CFSG.Sporadic.Bridge CFSG.Sporadic.Bridge.J1 CFSG.ProperTwoGeneratedCore

theorem opq4c_inverts_of_prime_order {H : Type*} [Group H] [Finite H] {p : ℕ} (hp : p.Prime)
    {y w : H} (hy : y ^ p = 1) (hy1 : y ≠ 1) (hw : w * w = 1) (hwy : w * y * w⁻¹ = y⁻¹)
    (hsq : ¬ p ^ 2 ∣ Nat.card H) {P : Subgroup H} (hP : IsPGroup p P)
    (hm : ∃ m : ℕ, Nat.card H = Nat.card P * m ∧ ¬ p ∣ m) :
    ∃ τ : H, τ * τ = 1 ∧ ∀ x ∈ P, τ * x * τ⁻¹ = x⁻¹ := by
  have : Fact p.Prime := ⟨hp⟩
  have hord : orderOf y = p := orderOf_eq_prime hy hy1
  refine opq4b_exists_inverts_of_index (T := Subgroup.zpowers y) hw (fun t ht => ?_) ?_ hP hm
  · obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ht
    rw [← conj_zpow, hwy, inv_zpow]
  · rintro ⟨c, hc⟩
    apply hsq
    have h1 := (Subgroup.zpowers y).card_mul_index
    rw [Nat.card_zpowers, hord, hc] at h1
    exact ⟨c, by rw [← h1]; ring⟩

private theorem opq4c_card_seedGroup : Nat.card ↥seedGroup = 175560 := by
  obtain ⟨hfin, hle⟩ := finite_card_le
  have h1 : Nat.card ↥seedGroup ≤ Nat.card TauCeti.Sporadic.j1Presentation.Group :=
    Nat.card_le_card_of_surjective toNative toNative_surjective
  exact le_antisymm (h1.trans hle) le_card_native

private def opq4c_pairs (s : List Bool) : List (ℕ × Bool) :=
  s.flatMap fun e => [(1, e), (0, true)]

private abbrev opq4c_good (p : ℕ) (y : List (ℕ × Bool)) : Prop :=
  matWord y ^ p = 1 ∧ matWord y ≠ 1 ∧
    letterMat (0, true) * matWord y = matWord y ^ (p - 1) * letterMat (0, true)

private theorem opq4c_good_three : opq4c_good 3 (opq4c_pairs
    [false, true, false, false, true, false, true, false, true, true, false, true]) := by
  decide +kernel

private theorem opq4c_good_five : opq4c_good 5 (opq4c_pairs
    [false, false, true, false, true, false, true, false, true, true]) := by
  decide +kernel

private theorem opq4c_good_seven : opq4c_good 7 (opq4c_pairs
    [false, false, true, true, false, true, false, false, true, true]) := by
  decide +kernel

private theorem opq4c_good_eleven : opq4c_good 11 (opq4c_pairs
    [false, false, true, false, false, true, true, false, true, true]) := by
  decide +kernel

private theorem opq4c_good_nineteen : opq4c_good 19 (opq4c_pairs [false, true]) := by
  decide +kernel

private theorem opq4c_seed_inverts (p : ℕ) (hp : p.Prime) (hsq : ¬ p ^ 2 ∣ 175560)
    (y : List (ℕ × Bool)) (hgood : opq4c_good p y)
    {P : Subgroup ↥seedGroup} (hP : IsPGroup p P)
    (hm : ∃ m : ℕ, Nat.card ↥seedGroup = Nat.card P * m ∧ ¬ p ∣ m) :
    ∃ τ : ↥seedGroup, τ * τ = 1 ∧ ∀ x ∈ P, τ * x * τ⁻¹ = x⁻¹ := by
  obtain ⟨hy, hy1, hinv⟩ := hgood
  have : Finite ↥seedGroup := inferInstance
  let Y : ↥seedGroup := ⟨wordProd unitGen y, wordProd_mem_seedGroup y⟩
  let a : ↥seedGroup := ⟨wordProd unitGen [(0, true)], wordProd_mem_seedGroup _⟩
  have hYmat : (((Y : GL (Fin 7) (ZMod 11)) : Matrix (Fin 7) (Fin 7) (ZMod 11))) = matWord y :=
    val_wordProd y
  have hamat : (((a : GL (Fin 7) (ZMod 11)) : Matrix (Fin 7) (Fin 7) (ZMod 11))) =
      letterMat (0, true) := by
    have := val_wordProd [(0, true)]
    simpa [matWord] using this
  have hYp : Y ^ p = 1 := by
    apply Subtype.ext
    apply Units.ext
    rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, hYmat, hy]
    rfl
  have hY1 : Y ≠ 1 := fun h => hy1 (by rw [← hYmat, h]; rfl)
  have haa : a * a = 1 := by
    apply Subtype.ext
    apply Units.ext
    rw [Subgroup.coe_mul, Units.val_mul, hamat]
    have : letterMat (0, true) * letterMat (0, true) = 1 := by decide +kernel
    rw [this]
    rfl
  have haY : a * Y = Y ^ (p - 1) * a := by
    apply Subtype.ext
    apply Units.ext
    rw [Subgroup.coe_mul, Units.val_mul, hamat, hYmat, Subgroup.coe_mul, Units.val_mul,
      Subgroup.coe_pow, Units.val_pow_eq_pow_val, hYmat, hamat]
    exact hinv
  have hYinv : Y ^ (p - 1) = Y⁻¹ := by
    refine eq_inv_of_mul_eq_one_right ?_
    rw [← pow_succ', Nat.sub_add_cancel hp.one_le, hYp]
  have hwy : a * Y * a⁻¹ = Y⁻¹ := by
    rw [inv_eq_of_mul_eq_one_right haa, haY, mul_assoc, haa, mul_one, hYinv]
  refine opq4c_inverts_of_prime_order hp hYp hY1 haa hwy ?_ hP hm
  rwa [opq4c_card_seedGroup]

theorem a38_invSyl_j1 {G : Type} [Group G] {L : Subgroup G} (hL : IsSporadic .J1 ↥L) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpL : p ∣ Nat.card L) : InvSylAll L p := by
  obtain ⟨e⟩ := hL
  let e' : ↥L ≃* ↥seedGroup := e.trans nativeEquiv
  refine opq4b_invSylAll_of_equiv e' ?_
  intro P hP hm
  have hpd : p ∣ 175560 := by
    rw [← opq4c_card_seedGroup, ← Nat.card_congr e'.toEquiv]
    exact hpL
  have hmem : p ∈ Nat.primeFactors 175560 := Nat.mem_primeFactors.2 ⟨hp, hpd, by norm_num⟩
  have hpf : Nat.primeFactors 175560 = {2, 3, 5, 7, 11, 19} := by
    norm_num [Nat.primeFactors]
  rw [hpf] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd rfl hp2
  · exact opq4c_seed_inverts 3 hp (by norm_num) _ opq4c_good_three hP hm
  · exact opq4c_seed_inverts 5 hp (by norm_num) _ opq4c_good_five hP hm
  · exact opq4c_seed_inverts 7 hp (by norm_num) _ opq4c_good_seven hP hm
  · exact opq4c_seed_inverts 11 hp (by norm_num) _ opq4c_good_eleven hP hm
  · exact opq4c_seed_inverts 19 hp (by norm_num) _ opq4c_good_nineteen hP hm

end CFSG.Quasithin
