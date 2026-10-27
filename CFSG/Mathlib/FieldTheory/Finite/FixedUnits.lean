module

public import Mathlib.FieldTheory.Fixed
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard

public section

namespace CFSG

private theorem fixedSubfield_card_eq_prime_pow {p a : ℕ} [Fact p.Prime] {F : Type*}
    [Field F] [Finite F] (hF : Nat.card F = p ^ a) (τ : F ≃+* F) :
    ∃ s : ℕ, Nat.card (FixedPoints.subfield (Subgroup.zpowers τ) F) = p ^ s ∧
      a = s * orderOf τ := by
  classical
  let K := FixedPoints.subfield (Subgroup.zpowers τ) F
  have hp : p.Prime := Fact.out
  have hK2 : 1 < Nat.card K :=
    Finite.one_lt_card_iff_nontrivial.mpr inferInstance
  have hF2 : 1 < Nat.card F :=
    Finite.one_lt_card_iff_nontrivial.mpr inferInstance
  have ha : 0 < a := by
    by_contra h
    have ha0 : a = 0 := Nat.eq_zero_of_not_pos h
    rw [ha0, pow_zero] at hF
    omega
  let : Finite (F ≃+* F) :=
    Finite.of_injective (fun e : F ≃+* F => (e : F → F))
      (fun _ _ h => RingEquiv.ext (congrFun h))
  have hr : orderOf τ ≠ 0 :=
    (orderOf_pos_iff.mpr (isOfFinOrder_of_finite τ)).ne'
  have hcard : Nat.card F = Nat.card K ^ orderOf τ := by
    simpa [K] using
      CFSG.GorensteinWalter.nat_card_eq_fixedSubfield_card_pow_orderOf F τ
  have hpp : IsPrimePow (Nat.card K ^ orderOf τ) := by
    rw [← hcard, hF]
    exact (isPrimePow_nat_iff (p ^ a)).mpr ⟨p, a, hp, ha, rfl⟩
  have hppK : IsPrimePow (Nat.card K) :=
    IsPrimePow.dvd hpp (dvd_pow_self (Nat.card K) hr) (ne_of_gt hK2)
  obtain ⟨q, s, hq, hs, hqK⟩ := (isPrimePow_nat_iff (Nat.card K)).mp hppK
  have hqp : q = p := by
    have hq_dvd : q ∣ p ^ a := by
      have h1 : q ∣ q ^ (s * orderOf τ) :=
        dvd_pow_self q (mul_ne_zero (Nat.ne_of_gt hs) hr)
      have h2 : q ^ (s * orderOf τ) = p ^ a := by
        rw [pow_mul, hqK, ← hcard, hF]
      rwa [h2] at h1
    exact Nat.prime_eq_prime_of_dvd_pow hq hp hq_dvd
  have hKcard : Nat.card K = p ^ s := by
    rw [← hqK, hqp]
  have haeq : a = s * orderOf τ := by
    have hpow : p ^ a = p ^ (s * orderOf τ) := by
      rw [← hF, hcard, hKcard, pow_mul]
    exact Nat.pow_right_injective hp.two_le hpow
  exact ⟨s, hKcard, haeq⟩

private theorem exists_fixed_units_generator {p s : ℕ} [Fact p.Prime] {F : Type*}
    [Field F] [Finite F] {τ : F ≃+* F}
    (hKcard : Nat.card (FixedPoints.subfield (Subgroup.zpowers τ) F) = p ^ s) :
    ∃ y : Fˣ, orderOf y = p ^ s - 1 ∧ τ (y : F) = y ∧
      ∀ z : Fˣ, τ (z : F) = z → z ∈ Subgroup.zpowers y := by
  classical
  let K := FixedPoints.subfield (Subgroup.zpowers τ) F
  let : IsCyclic Kˣ := inferInstance
  obtain ⟨yK, hyKord⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Kˣ)
  let y : Fˣ := Units.map K.subtype.toMonoidHom yK
  have hyord : orderOf y = p ^ s - 1 := by
    rw [orderOf_injective (Units.map K.subtype.toMonoidHom)
      (Units.map_injective (Subfield.subtype_injective K)) yK, hyKord,
      Nat.card_units, hKcard]
  have hyfix : τ (y : F) = y := by
    have hmem := (yK : K).2 ⟨τ, Subgroup.mem_zpowers τ⟩
    simpa [y, Units.coe_map, RingHom.smul_def] using hmem
  refine ⟨y, hyord, hyfix, ?_⟩
  intro z hz
  have hzK_mem : (z : F) ∈ K := by
    intro g
    exact smul_eq_self_of_mem_zpowers g.2 (by simpa [RingHom.smul_def] using hz)
  let zK : K := ⟨(z : F), hzK_mem⟩
  have hzK0 : zK ≠ 0 := by
    intro h
    apply z.ne_zero
    exact congrArg Subtype.val h
  let zu : Kˣ := Units.mk0 zK hzK0
  have hzu : Units.map K.subtype.toMonoidHom zu = z := by
    ext
    rw [Units.coe_map]
    rfl
  have htop : Subgroup.zpowers yK = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [Nat.card_zpowers, hyKord]
  have hzumem : zu ∈ Subgroup.zpowers yK := by
    rw [htop]
    exact Subgroup.mem_top zu
  have hzmap : Units.map K.subtype.toMonoidHom zu ∈
      Subgroup.map (Units.map K.subtype.toMonoidHom) (Subgroup.zpowers yK) :=
    Subgroup.mem_map_of_mem _ hzumem
  rw [MonoidHom.map_zpowers] at hzmap
  rwa [hzu] at hzmap

theorem exists_zpowers_eq_fixed_units {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    {a : ℕ} (hF : Nat.card F = p ^ a) (τ : F ≃+* F) :
    ∃ s : ℕ, s ∣ a ∧ a / s = orderOf τ ∧ ∃ y : Fˣ, orderOf y = p ^ s - 1 ∧
      τ (y : F) = y ∧ ∀ z : Fˣ, τ (z : F) = z → z ∈ Subgroup.zpowers y := by
  classical
  let K := FixedPoints.subfield (Subgroup.zpowers τ) F
  obtain ⟨s, hKcard, haeq⟩ := fixedSubfield_card_eq_prime_pow hF τ
  have hs : 0 < s := by
    by_contra h
    have hs0 : s = 0 := Nat.eq_zero_of_not_pos h
    rw [hs0, pow_zero] at hKcard
    have hK2 : 1 < Nat.card K :=
      Finite.one_lt_card_iff_nontrivial.mpr inferInstance
    exact (ne_of_gt hK2) hKcard
  have hs_dvd : s ∣ a := ⟨orderOf τ, haeq⟩
  have hs_div : a / s = orderOf τ := by
    rw [haeq, Nat.mul_div_right _ hs]
  refine ⟨s, hs_dvd, hs_div, ?_⟩
  obtain ⟨y, hyord, hyfix, hygen⟩ := exists_fixed_units_generator (τ := τ) hKcard
  exact ⟨y, hyord, hyfix, hygen⟩

end CFSG
