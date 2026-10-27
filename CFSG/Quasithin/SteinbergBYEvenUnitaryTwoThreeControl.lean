module

public import CFSG.Timmesfeld.Orders.ClassicalLinear
public import CFSG.Quasithin.H13.U3SimpleRoot
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherRankOneRoot

public section

namespace CFSG.Quasithin.SteinbergBY

open Subgroup CFSG.Assembly.LowTwoRank CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

theorem card_statedProj_statedSU_three_two {K : Type} [Field K] {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) :
    Nat.card (StatedProj (StatedSU 3 (2 ^ f) K)) =
      (2 ^ f) ^ 3 * (((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 3 + 1)) / Nat.gcd 3 (2 ^ f + 1) := by
  rw [CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSU Nat.prime_two hf hK (by norm_num),
    show Finset.Icc 2 3 = {2, 3} by decide, Finset.prod_pair (by norm_num)]
  have hq : 1 ≤ 2 ^ f := Nat.one_le_two_pow
  have h2 : (((2 ^ f : ℕ) : ℤ) ^ 2 - (-1) ^ 2).toNat = (2 ^ f) ^ 2 - 1 := by
    have : 1 ≤ (2 ^ f) ^ 2 := Nat.one_le_pow _ _ (by omega)
    rw [show ((2 ^ f : ℕ) : ℤ) ^ 2 - (-1) ^ 2 = (((2 ^ f) ^ 2 - 1 : ℕ) : ℤ) by
      push_cast [Nat.cast_sub this]; ring]
    exact Int.toNat_natCast _
  have h3 : (((2 ^ f : ℕ) : ℤ) ^ 3 - (-1) ^ 3).toNat = (2 ^ f) ^ 3 + 1 := by
    rw [show ((2 ^ f : ℕ) : ℤ) ^ 3 - (-1) ^ 3 = (((2 ^ f) ^ 3 + 1 : ℕ) : ℤ) by push_cast; ring]
    exact Int.toNat_natCast _
  rw [h2, h3]

theorem exists_prime_five_le_dvd_sq_sub_one {q : ℕ} (hq : 4 ≤ q) (hev : Even q) :
    ∃ p, p.Prime ∧ 5 ≤ p ∧ p ∣ q ^ 2 - 1 := by
  have hsq : q ^ 2 - 1 = (q - 1) * (q + 1) := by
    have : 1 ≤ q := by omega
    zify [this, Nat.one_le_pow 2 q (by omega)]
    ring
  obtain ⟨k, hk⟩ := hev
  obtain ⟨m, hm3, hmodd, hm, hdvd⟩ : ∃ m, 3 ≤ m ∧ m % 2 = 1 ∧ m % 3 ≠ 0 ∧
      m ∣ q ^ 2 - 1 := by
    rw [hsq]
    by_cases h3 : (q - 1) % 3 = 0
    · exact ⟨q + 1, by omega, by omega, by omega, dvd_mul_left _ _⟩
    · exact ⟨q - 1, by omega, by omega, h3, dvd_mul_right _ _⟩
  have hp := Nat.minFac_prime (show m ≠ 1 by omega)
  refine ⟨m.minFac, hp, ?_, (Nat.minFac_dvd m).trans hdvd⟩
  have h2 : m.minFac ≠ 2 := fun h => by
    have := Nat.minFac_dvd m
    rw [h] at this
    omega
  have h3 : m.minFac ≠ 3 := fun h => by
    have := Nat.minFac_dvd m
    rw [h] at this
    omega
  have h4 : m.minFac ≠ 4 := fun h => by
    rw [h] at hp
    exact absurd hp (by decide)
  have := hp.two_le
  omega

theorem card_PSU3_arith {K : Type} [Field K] {f : ℕ} (hf : 2 ≤ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) :
    ∃ r : ℕ, Nat.card (StatedProj (StatedSU 3 (2 ^ f) K)) = (2 ^ f) ^ 3 * r ∧ Odd r ∧
      ∃ p, p.Prime ∧ 5 ≤ p ∧ p ∣ r := by
  set q := 2 ^ f with hqdef
  have hq4 : 4 ≤ q := by
    rw [hqdef]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hqev : Even q := by
    rw [hqdef]
    exact (Nat.even_pow' (by omega)).mpr even_two
  set m := (q ^ 2 - 1) * (q ^ 3 + 1) with hmdef
  set g := Nat.gcd 3 (q + 1) with hgdef
  have hgm : g ∣ m := (Nat.gcd_dvd_right 3 (q + 1)).trans (Dvd.dvd.mul_left (by
    simpa using Odd.nat_add_dvd_pow_add_pow q 1 (by decide : Odd 3)) _)
  refine ⟨m / g, ?_, ?_, ?_⟩
  · rw [card_statedProj_statedSU_three_two (by omega) hK, Nat.mul_div_assoc _ hgm]
  · have hmodd : Odd m := by
      have hq2 : Even (q ^ 2) := (Nat.even_pow' (by norm_num)).mpr hqev
      have hq3 : Even (q ^ 3) := (Nat.even_pow' (by norm_num)).mpr hqev
      have h1 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
      rw [hmdef, Nat.odd_mul]
      obtain ⟨a, ha⟩ := hq2
      obtain ⟨b, hb⟩ := hq3
      exact ⟨⟨a - 1, by omega⟩, ⟨b, by omega⟩⟩
    exact Odd.of_dvd_nat hmodd (Nat.div_dvd_of_dvd hgm)
  · obtain ⟨p, hp, hp5, hpq⟩ := exists_prime_five_le_dvd_sq_sub_one hq4 hqev
    refine ⟨p, hp, hp5, ?_⟩
    have hpg : Nat.Coprime p g := Nat.coprime_of_dvd' fun r hr hrp hrg => by
      have h3 : r ∣ 3 := hrg.trans (Nat.gcd_dvd_left 3 (q + 1))
      have hr3 : r = 3 := (Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).mp h3
      have : r = p := (Nat.prime_dvd_prime_iff_eq hr hp).mp hrp
      omega
    have hpm : p ∣ m / g * g := by
      rw [Nat.div_mul_cancel hgm, hmdef]
      exact Dvd.dvd.mul_right hpq _
    exact hpg.dvd_of_dvd_mul_right hpm

theorem le_normalizer_of_rkOneUStar_comap_le {f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 f K) {S : Type} [Group S] [Finite S] [IsSimpleGroup S]
    (Φ : S →* Equiv.Perm (hypIsotropicLines h 1 1)) (hΦ : Function.Injective Φ)
    (hrange : Φ.range = rkOneG h) {M : Subgroup S} (hMtop : M < ⊤)
    (hUM : (rkOneUStar h).comap Φ ≤ M) :
    M ≤ normalizer (((rkOneUStar h).comap Φ : Subgroup S) : Set S) := by
  classical
  have := h.finite
  set U := (rkOneUStar h).comap Φ with hUdef
  have hUmap : U.map Φ = rkOneUStar h := by
    rw [hUdef, Subgroup.map_comap_eq, hrange]
    exact inf_eq_right.2 (rkOneUStar_le_rkOneG h)
  have hcard : Nat.card U = 2 ^ (f * 3) := by
    rw [← Subgroup.card_map_of_injective hΦ, hUmap, card_rkOneUStar h, ← pow_mul]
  have hUne : U ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card U = 1 := by rw [hbot, Subgroup.card_bot]
    have h2 : 1 < 2 ^ (f * 3) := Nat.one_lt_pow (by have := h.one_le; omega) (by norm_num)
    omega
  let _ : MulAction S (hypIsotropicLines h 1 1) := MulAction.compHom _ Φ
  have hsmul : ∀ (s : S) (L : hypIsotropicLines h 1 1), s • L = Φ s L := fun _ _ => rfl
  have hstab : ∀ s ∈ MulAction.stabilizer S (infL h), Φ s ∈ rkOneGInf h := fun s hs =>
    ⟨hrange ▸ MonoidHom.mem_range.2 ⟨s, rfl⟩, hs⟩
  have hUα : U ≤ MulAction.stabilizer S (infL h) := fun u hu => by
    rw [MulAction.mem_stabilizer_iff, hsmul]
    exact rkOneUStar_fix h hu
  have hUn : (U.subgroupOf (MulAction.stabilizer S (infL h))).Normal := by
    constructor
    intro n hn s
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have hc := (rkOneUStar_normal h).conj_mem ⟨Φ n, hstab n n.2⟩ hn ⟨Φ s, hstab s s.2⟩
    rw [Subgroup.mem_subgroupOf] at hc
    show Φ (↑s * ↑n * (↑s)⁻¹) ∈ rkOneUStar h
    rw [map_mul, map_mul, map_inv]
    exact hc
  have hUt : ∀ β γ : hypIsotropicLines h 1 1, β ≠ infL h → γ ≠ infL h →
      ∃ u ∈ U, u • β = γ := by
    intro β γ hβ hγ
    obtain ⟨a₁, b₁, hab₁, hβ₁⟩ := exists_rkPtL_eq β hβ
    obtain ⟨a₂, b₂, hab₂, hγ₂⟩ := exists_rkPtL_eq γ hγ
    have hx₁ := rkOneU_mem h hab₁
    have hx₂ := rkOneU_mem h hab₂
    have hx₁0 : rkOneU h a₁ b₁ hab₁ (zeroL h) = β := by rw [rkOneU_zeroL, hβ₁]
    have hx₂0 : rkOneU h a₂ b₂ hab₂ (zeroL h) = γ := by rw [rkOneU_zeroL, hγ₂]
    set x₁ := rkOneU h a₁ b₁ hab₁
    set x₂ := rkOneU h a₂ b₂ hab₂
    have hxm : x₂ * x₁⁻¹ ∈ rkOneG h := rkOneUStar_le_rkOneG h
      ((rkOneUStar h).mul_mem hx₂ ((rkOneUStar h).inv_mem hx₁))
    rw [← hrange] at hxm
    obtain ⟨u, hu⟩ := hxm
    refine ⟨u, ?_, ?_⟩
    · show Φ u ∈ rkOneUStar h
      rw [hu]
      exact (rkOneUStar h).mul_mem hx₂ ((rkOneUStar h).inv_mem hx₁)
    · rw [hsmul, hu, Equiv.Perm.mul_apply, Equiv.Perm.inv_eq_iff_eq.2 hx₁0.symm, hx₂0]
  have hMle := CFSG.Quasithin.H13.U3.simple_transitive_root_proper_overgroups (infL h) hUne hUα
    hUn hUt hMtop hUM
  exact hMle.trans ((normal_subgroupOf_iff_le_normalizer hUα).1 hUn)

theorem exists_pointAction_of_statedPSU3 {S : Type} [Group S] {f : ℕ}
    (hS : StatedClassicalModel S .PSU 3 2 f) :
    ∃ (K : Type) (_ : Field K) (h : UnitaryFieldData 2 f K),
      Nat.card K = (2 ^ f) ^ 2 ∧ Nonempty (S ≃* StatedProj (StatedSU 3 (2 ^ f) K)) ∧
      ∃ Φ₀ : S →* Equiv.Perm (hypIsotropicLines h 1 1), Function.Injective Φ₀ ∧
        Φ₀.range = rkOneG h := by
  obtain ⟨⟨-, hf1, -⟩, K, _, _, hK, ⟨e₀⟩⟩ := hS
  have h : UnitaryFieldData 2 f K := ⟨Nat.prime_two, hf1, by rw [hK, ← pow_mul, mul_comm]⟩
  obtain ⟨R, hR⟩ := exists_isHypTransport (r := 1) (ε := 1) h
  let e₁ : S ≃* hypPSU h 1 1 := e₀.trans (hypPSUEquivStatedProj h hR (by norm_num)).symm
  refine ⟨K, inferInstance, h, hK, ⟨e₀⟩, (hypProjLineAction h 1 1).comp e₁.toMonoidHom,
    (hypProjLineAction_injective h (by norm_num)).comp e₁.injective, ?_⟩
  ext x
  constructor
  · rintro ⟨s, rfl⟩
    exact ⟨e₁ s, rfl⟩
  · rintro ⟨y, rfl⟩
    exact ⟨e₁.symm y, by simp⟩

theorem le_normalizer_of_statedPSU3 {S : Type} [Group S] [Finite S] [IsSimpleGroup S] {f : ℕ}
    (hf : 2 ≤ f) (hS : StatedClassicalModel S .PSU 3 2 f) (T : Sylow 2 S) :
    (∀ M : Subgroup S, (T : Subgroup S) ≤ M → ∀ a b : ℕ, Nat.card M = 2 ^ a * 3 ^ b →
      M ≤ normalizer ((T : Subgroup S) : Set S)) ∧ 2 ∣ Nat.card S := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨K, _, h, hK, ⟨e₀⟩, Φ₀, hΦ₀, hrange₀⟩ := exists_pointAction_of_statedPSU3 hS
  have := h.finite
  obtain ⟨r, hr, hrodd, p, hp, hp5, hpr⟩ := card_PSU3_arith hf hK
  have hcardS : Nat.card S = (2 ^ f) ^ 3 * r := by rw [Nat.card_congr e₀.toEquiv, hr]
  set U₀ := (rkOneUStar h).comap Φ₀ with hU₀
  have hU₀map : U₀.map Φ₀ = rkOneUStar h := by
    rw [hU₀, Subgroup.map_comap_eq, hrange₀]
    exact inf_eq_right.2 (rkOneUStar_le_rkOneG h)
  have hU₀card : Nat.card U₀ = (2 ^ f) ^ 3 := by
    rw [← Subgroup.card_map_of_injective hΦ₀, hU₀map, card_rkOneUStar h]
  have hidx : U₀.index = r := by
    have hmul := U₀.card_mul_index
    rw [hU₀card, hcardS] at hmul
    exact Nat.eq_of_mul_eq_mul_left (by positivity) hmul
  have hidx2 : ¬ 2 ∣ U₀.index := by
    rw [hidx]
    exact fun h2 => (Nat.not_even_iff_odd.2 hrodd) (even_iff_two_dvd.2 h2)
  have hU₀2 : IsPGroup 2 U₀ := IsPGroup.of_card (n := f * 3) (by rw [hU₀card, ← pow_mul])
  have h2S : 2 ∣ Nat.card S := by
    rw [← U₀.card_mul_index, hU₀card, ← pow_mul]
    exact Dvd.dvd.mul_right (dvd_pow_self 2 (by omega)) _
  refine ⟨fun M hTM a b hM => ?_, h2S⟩
  let P₀ : Sylow 2 S := hU₀2.toSylow hidx2
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq S P₀ T
  let Φ : S →* Equiv.Perm (hypIsotropicLines h 1 1) := Φ₀.comp (MulAut.conj x⁻¹).toMonoidHom
  have hΦ : Function.Injective Φ := hΦ₀.comp (MulAut.conj x⁻¹).injective
  have hrange : Φ.range = rkOneG h := by
    rw [← hrange₀]
    ext y
    constructor
    · rintro ⟨s, rfl⟩
      exact ⟨_, rfl⟩
    · rintro ⟨s, rfl⟩
      refine ⟨x * s * x⁻¹, ?_⟩
      simp only [Φ, MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
        MulAut.conj_apply, inv_inv]
      congr 1
      group
  have hTU : (rkOneUStar h).comap Φ = (T : Subgroup S) := by
    ext y
    rw [← hx, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv,
      MulAut.smul_def]
    rfl
  have hMtop : M < ⊤ := by
    refine lt_top_iff_ne_top.2 fun hMt => ?_
    have hc : Nat.card S = 2 ^ a * 3 ^ b := by rw [← hM, hMt, Subgroup.card_top]
    have hpS : p ∣ Nat.card S := by
      rw [hcardS]
      exact Dvd.dvd.mul_left hpr _
    rw [hc] at hpS
    rcases (Nat.Prime.dvd_mul hp).mp hpS with h2 | h3
    · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h2)
      omega
    · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (hp.dvd_of_dvd_pow h3)
      omega
  have h1 := le_normalizer_of_rkOneUStar_comap_le h Φ hΦ hrange hMtop (hTU ▸ hTM)
  rwa [hTU] at h1

end CFSG.Quasithin.SteinbergBY
