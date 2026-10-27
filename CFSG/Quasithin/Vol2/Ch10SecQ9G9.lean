module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.F1Models
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F

open CFSG.Open CFSG.Quasithin

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem eq_one_of_two_pow {g : G} {m n : ℕ} (hm : g ^ 2 ^ m = 1) (hn : g ^ n = 1) (hodd : Odd n) :
    g = 1 := by
  have h1 : orderOf g ∣ Nat.gcd (2 ^ m) n :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hm) (orderOf_dvd_of_pow_eq_one hn)
  have h2 : Nat.gcd (2 ^ m) n = 1 :=
    Nat.Coprime.pow_left m ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr
      (by rw [← even_iff_two_dvd]; exact Nat.not_even_iff_odd.mpr hodd))
  rw [h2, Nat.dvd_one, orderOf_eq_one_iff] at h1
  exact h1

theorem exists_two_pow_of_mem_pCoreOf {L : Subgroup G} {g : G} (hg : g ∈ pCoreOf 2 L) :
    ∃ m : ℕ, g ^ 2 ^ m = 1 := by
  obtain ⟨m, hm⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L ⟨g, hg⟩
  exact ⟨m, congrArg Subtype.val hm⟩

theorem exists_orderOf_seven {L : Subgroup G}
    (eL : ↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :
    ∃ x ∈ L, orderOf x = 7 := by
  have : Fact (Nat.Prime 7) := ⟨by decide⟩
  set γ : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) := ⟨!![0, 0, 1; 1, 0, 1; 0, 1, 0], by decide⟩
  have hγ : orderOf γ = 7 := by
    refine orderOf_eq_prime (Subtype.ext (by rw [Matrix.SpecialLinearGroup.coe_pow]; decide))
      fun h => ?_
    have := congrArg (fun g : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) =>
      (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) 0 0) h
    revert this
    decide
  obtain ⟨l, hl⟩ := QuotientGroup.mk_surjective (eL.symm γ)
  set φ := eL.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) with hφ
  have hφl : φ l = γ := by
    rw [hφ, MonoidHom.comp_apply, QuotientGroup.mk'_apply, hl]
    exact eL.apply_symm_apply γ
  have h7 : 7 ∣ orderOf l := hγ ▸ hφl ▸ orderOf_map_dvd φ l
  refine ⟨((l ^ (orderOf l / 7) : ↥L) : G), Subgroup.pow_mem _ l.2 _, ?_⟩
  rw [Subgroup.orderOf_coe, orderOf_pow_orderOf_div (orderOf_pos l).ne' h7]

theorem exists_commute_seven_three {J L : Subgroup G} {S : Type*} [Group S] [Finite S]
    (ψ : ↥J →* S)
    (hψ : ∀ j : ↥J, ψ j = 1 → ∃ m : ℕ, (j : G) ^ 2 ^ m = 1) {x y : G} (hxJ : x ∈ J)
    (hyJ : y ∈ J) (hxL : x ∈ L) (hx7 : orderOf x = 7) (hy3 : orderOf y = 3)
    (hyN : y ∈ Subgroup.normalizer (L : Set G))
    (hyc : ∀ l ∈ L, y * l * y⁻¹ * l⁻¹ ∈ pCoreOf 2 L) :
    ∃ a b : S, orderOf a = 7 ∧ orderOf b = 3 ∧ Commute a b := by
  have : Fact (Nat.Prime 7) := ⟨by decide⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set N := Subgroup.normalizer (L : Set G) with hN
  set O := pCoreOf 2 L with hO
  have hON : N ≤ Subgroup.normalizer (O : Set G) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L
  have hOn : (O.subgroupOf N).Normal := by
    refine ⟨fun a ha g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at ha ⊢
    simpa using (Subgroup.mem_normalizer_iff.mp (hON g.2) a).mp ha
  have hxN : x ∈ N := Subgroup.le_normalizer hxL
  set q := QuotientGroup.mk' (O.subgroupOf N) with hq
  set xb := q ⟨x, hxN⟩ with hxbd
  set yb := q ⟨y, hyN⟩ with hybd
  have hx7' : x ^ 7 = 1 := by have := pow_orderOf_eq_one x; rwa [hx7] at this
  have hy3' : y ^ 3 = 1 := by have := pow_orderOf_eq_one y; rwa [hy3] at this
  have hxb : orderOf xb = 7 := by
    have hx7N : (⟨x, hxN⟩ : ↥N) ^ 7 = 1 := Subtype.ext (by simpa using hx7')
    refine orderOf_eq_prime (by rw [hxbd, ← map_pow, hx7N, map_one]) fun h => ?_
    rw [hxbd, hq, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h
    obtain ⟨m, hm⟩ := exists_two_pow_of_mem_pCoreOf h
    have hx1 : x = 1 := eq_one_of_two_pow hm hx7' (by decide)
    rw [hx1, orderOf_one] at hx7
    omega
  have hyb : orderOf yb = 3 := by
    have hy3N : (⟨y, hyN⟩ : ↥N) ^ 3 = 1 := Subtype.ext (by simpa using hy3')
    refine orderOf_eq_prime (by rw [hybd, ← map_pow, hy3N, map_one]) fun h => ?_
    rw [hybd, hq, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h
    obtain ⟨m, hm⟩ := exists_two_pow_of_mem_pCoreOf h
    have hy1 : y = 1 := eq_one_of_two_pow hm hy3' (by decide)
    rw [hy1, orderOf_one] at hy3
    omega
  have hcomm : Commute xb yb := by
    have h1 : y * x * y⁻¹ * x⁻¹ ∈ O := hyc x hxL
    have h2 : q (⟨y, hyN⟩ * ⟨x, hxN⟩ * ⟨y, hyN⟩⁻¹ * ⟨x, hxN⟩⁻¹) = 1 := by
      rw [hq, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      simpa using h1
    simp only [map_mul, map_inv, ← hxbd, ← hybd] at h2
    have h3 : yb * xb = xb * yb := by
      calc yb * xb = yb * xb * yb⁻¹ * xb⁻¹ * (xb * yb) := by group
        _ = xb * yb := by rw [h2, one_mul]
    exact h3.symm
  have h21 : orderOf (xb * yb) = 21 := by
    rw [hcomm.orderOf_mul_eq_mul_orderOf_of_coprime (by rw [hxb, hyb]; decide), hxb, hyb]
  set z := ψ (⟨x, hxJ⟩ * ⟨y, hyJ⟩) with hz
  have hdvd : 21 ∣ orderOf z := by
    have h1 : ψ ((⟨x, hxJ⟩ * ⟨y, hyJ⟩) ^ orderOf z) = 1 := by rw [map_pow, pow_orderOf_eq_one]
    obtain ⟨m, hm⟩ := hψ _ h1
    have h2 : (x * y) ^ (orderOf z * 2 ^ m) = 1 := by
      rw [pow_mul]
      simpa using hm
    have h3 : (xb * yb) ^ (orderOf z * 2 ^ m) = 1 := by
      rw [hxbd, hybd, ← map_mul, ← map_pow]
      have : (⟨x, hxN⟩ * ⟨y, hyN⟩ : ↥N) ^ (orderOf z * 2 ^ m) = 1 := Subtype.ext (by simpa using h2)
      rw [this, map_one]
    have h4 := orderOf_dvd_of_pow_eq_one h3
    rw [h21] at h4
    exact (Nat.Coprime.dvd_of_dvd_mul_right (Nat.Coprime.pow_right m (by decide)) h4)
  set a := z ^ (orderOf z / 21) with ha
  have ha21 : orderOf a = 21 := orderOf_pow_orderOf_div (orderOf_pos z).ne' hdvd
  refine ⟨a ^ 3, a ^ 7, ?_, ?_, (Commute.refl a).pow_pow 3 7⟩
  · rw [orderOf_pow' a (by norm_num), ha21]
    decide
  · rw [orderOf_pow' a (by norm_num), ha21]
    decide

end CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F
