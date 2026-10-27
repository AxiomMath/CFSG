module

public import CFSG.Quasithin.Vol2.Ch10SecKGA7a
public import CFSG.Quasithin.Vol2.Ch10SecKGCFa

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA.C10KG

open Subgroup
open scoped Pointwise

variable {X : Type*} [Group X] [Finite X]

theorem not_three_dvd_card_sup {O : Subgroup X} {c₀ : X} (hO2 : IsPGroup 2 O)
    (hc₀ : c₀ ^ 5 = 1) (hcO : zpowers c₀ ≤ normalizer (O : Set X)) :
    ¬ 3 ∣ Nat.card ↥(O ⊔ zpowers c₀) := by
  intro h3
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨⟨d, hd⟩, hd3⟩ := exists_prime_orderOf_dvd_card' 3 h3
  rw [Subgroup.orderOf_mk] at hd3
  have hd' : d ∈ ((O : Set X) * (zpowers c₀ : Set X)) := by
    rw [← coe_mul_of_right_le_normalizer_left O (zpowers c₀) hcO]
    exact hd
  obtain ⟨o, ho, c, hc, rfl⟩ := hd'
  change orderOf (o * c) = 3 at hd3
  have hcO' : ∀ y ∈ O, c * y * c⁻¹ ∈ O := fun y hy =>
    (mem_normalizer_iff.mp (hcO hc) y).mp hy
  have hc2O : ∀ y ∈ O, c ^ 2 * y * (c ^ 2)⁻¹ ∈ O := fun y hy => by
    rw [pow_two, mul_inv_rev]
    simpa [mul_assoc] using hcO' _ (hcO' y hy)
  have e : (o * c) ^ 3 = (o * (c * o * c⁻¹) * (c ^ 2 * o * (c ^ 2)⁻¹)) * c ^ 3 := by
    rw [show (o * c) ^ 3 = o * c * (o * c) * (o * c) by rw [pow_succ, pow_two]]
    group
  have hd1 : (o * c) ^ 3 = 1 := by rw [← hd3]; exact pow_orderOf_eq_one _
  have hc3 : c ^ 3 ∈ O := by
    have h1 : c ^ 3 = (o * (c * o * c⁻¹) * (c ^ 2 * o * (c ^ 2)⁻¹))⁻¹ :=
      eq_inv_of_mul_eq_one_right (e.symm.trans hd1)
    rw [h1]
    exact O.inv_mem (O.mul_mem (O.mul_mem ho (hcO' o ho)) (hc2O o ho))
  obtain ⟨m, hm⟩ := hO2 ⟨c ^ 3, hc3⟩
  have hm' : (c ^ 3) ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
  have hc5 : c ^ 5 = 1 := by
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hc
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hc₀, one_zpow]
  have hc1 : c = 1 := by
    have h1 : orderOf c ∣ 3 * 2 ^ m := orderOf_dvd_of_pow_eq_one (by rw [pow_mul, hm'])
    have h2 : orderOf c ∣ 5 := orderOf_dvd_of_pow_eq_one hc5
    have hco : Nat.Coprime (3 * 2 ^ m) 5 :=
      Nat.coprime_mul_iff_left.mpr ⟨by norm_num, Nat.Coprime.pow_left _ (by norm_num)⟩
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hco h1 h2)
  rw [hc1, mul_one] at hd3
  obtain ⟨n, hn⟩ := hO2 ⟨o, ho⟩
  have hn' : o ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
  have h1 : 3 ∣ 2 ^ n := hd3 ▸ orderOf_dvd_of_pow_eq_one hn'
  exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h1) (by norm_num)

theorem exists_commute_five {B O : Subgroup X} {x : X} (h25 : ¬ 25 ∣ Nat.card X)
    (h5 : 5 ∣ Nat.card B) (hO2 : IsPGroup 2 O) (hBO : B ≤ normalizer (O : Set X))
    (hxO : x ∈ normalizer (O : Set X)) (hxB : ∀ b ∈ B, x * b * x⁻¹ * b⁻¹ ∈ O)
    (hx3 : orderOf x = 3) : ∃ c : X, orderOf c = 5 ∧ Commute x c := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨⟨c₀, hc₀B⟩, hc₀5⟩ := exists_prime_orderOf_dvd_card' 5 h5
  rw [Subgroup.orderOf_mk] at hc₀5
  have hc₀5' : c₀ ^ 5 = 1 := hc₀5 ▸ pow_orderOf_eq_one c₀
  have hcO : zpowers c₀ ≤ normalizer (O : Set X) := zpowers_le.mpr (hBO hc₀B)
  set D := O ⊔ zpowers c₀ with hD
  have hxD : ∀ d ∈ D, x * d * x⁻¹ ∈ D := by
    have hcD : x * c₀ * x⁻¹ ∈ D := by
      have : x * c₀ * x⁻¹ = (x * c₀ * x⁻¹ * c₀⁻¹) * c₀ := by group
      rw [this]
      exact D.mul_mem (mem_sup_left (hxB c₀ hc₀B)) (mem_sup_right (mem_zpowers c₀))
    have hle : D ≤ D.comap (MulAut.conj x).toMonoidHom := sup_le
      (fun o ho => mem_sup_left ((mem_normalizer_iff.mp hxO o).mp ho))
      (zpowers_le.mpr hcD)
    exact fun d hd => hle hd
  have hxN : zpowers x ≤ normalizer (D : Set X) := by
    rw [zpowers_le]
    have hinv := CFSG.Quasithin.Vol2.Ch10.SecB.C10KG.inv_conj_mem hxD
    exact mem_normalizer_iff.mpr fun d => ⟨hxD d, fun h => by simpa [mul_assoc] using hinv _ h⟩
  let _ : MulDistribMulAction ↥(zpowers x) ↥D :=
    MulDistribMulAction.compHom ↥D (D.normalizerMonoidHom.comp (Subgroup.inclusion hxN))
  have hZ3 : IsPGroup 3 ↥(zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx3, pow_one])
  have h3 : ¬ 3 ∣ Nat.card (Sylow 5 ↥D) := fun h =>
    not_three_dvd_card_sup hO2 hc₀5' hcO
      (h.trans ((Sylow.card_dvd_index default).trans (Subgroup.index_dvd_card _)))
  obtain ⟨P, hP⟩ := hZ3.nonempty_fixed_point_of_prime_not_dvd_card (Sylow 5 ↥D) h3
  have hPx : ∀ p ∈ (P : Subgroup ↥D), x * (p : X) * x⁻¹ ∈ (P : Subgroup ↥D).map D.subtype := by
    intro p hp
    have h1 := Subgroup.smul_mem_pointwise_smul p (⟨x, mem_zpowers x⟩ : ↥(zpowers x)) _ hp
    rw [← Sylow.pointwise_smul_def, hP ⟨x, mem_zpowers x⟩] at h1
    exact ⟨_, h1, rfl⟩
  set P₀ := (P : Subgroup ↥D).map D.subtype with hP₀
  have hcP : Nat.card P₀ = Nat.card (P : Subgroup ↥D) :=
    Subgroup.card_map_of_injective Subtype.val_injective
  obtain ⟨k, hk⟩ := P.isPGroup'.exists_card_eq
  have h5D : 5 ∣ Nat.card ↥D := by
    rw [← hc₀5]
    exact (Subgroup.orderOf_mk c₀ (mem_sup_right (mem_zpowers c₀) : c₀ ∈ D)) ▸
      orderOf_dvd_natCard (⟨c₀, mem_sup_right (mem_zpowers c₀)⟩ : ↥D)
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero, Subgroup.card_eq_one] at hk
    exact Sylow.ne_bot_of_dvd_card P h5D hk
  have hk1 : k ≤ 1 := by
    by_contra hk2
    refine h25 ((pow_dvd_pow 5 (by omega : 2 ≤ k)).trans ?_)
    rw [← hk, ← hcP]
    exact Subgroup.card_subgroup_dvd_card P₀
  have hcard5 : Nat.card P₀ = 5 := by
    rw [hcP, hk, show k = 1 by omega, pow_one]
  have : Nontrivial P₀ := Finite.one_lt_card_iff_nontrivial.mp (by rw [hcard5]; norm_num)
  obtain ⟨⟨g, hg⟩, hg1⟩ := exists_ne (1 : P₀)
  have hg1' : g ≠ 1 := fun h => hg1 (Subtype.ext h)
  have hg5 : orderOf g = 5 := by
    have h1 : orderOf g ∣ 5 := hcard5 ▸ (Subgroup.orderOf_mk g hg) ▸
      orderOf_dvd_natCard (⟨g, hg⟩ : P₀)
    rcases (Nat.dvd_prime Nat.prime_five).mp h1 with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hg1'
    · exact h
  have hzg : zpowers g = P₀ := Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr hg)
    (by rw [hcard5, Nat.card_zpowers, hg5])
  have hxg : x * g * x⁻¹ ∈ zpowers g := by
    rw [hzg]
    obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.mp hg
    exact hPx p hp
  have hx3' : x ^ 3 = 1 := hx3 ▸ pow_orderOf_eq_one x
  exact ⟨g, hg5, commute_of_conj_mem_zpowers_five hx3' hg5 hxg⟩

end CFSG.Quasithin.Vol2.Ch11.SecA.C10KG
