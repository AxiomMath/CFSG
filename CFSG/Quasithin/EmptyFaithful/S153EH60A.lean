module

public import CFSG.LocalAnalysis.SignalizerFunctor.CoprimeQuotientNormalizers

public section

namespace CFSG.Quasithin

namespace S153EH60

variable {H B : Type*} [Group H] [Group B]

theorem card_map_mul_card_inf_ker [Finite H] (φ : H →* B) (C : Subgroup H) :
    Nat.card (C.map φ) * Nat.card ↥(φ.ker ⊓ C) = Nat.card C := by
  rw [← Subgroup.relIndex_ker, Subgroup.relIndex_mul_card]

theorem inf_eq_bot_of_isPGroup (K D : Subgroup H) (hK : IsPGroup 2 K) (hD : IsPGroup 3 D) :
    K ⊓ D = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨k, hk⟩ := hK ⟨x, hx.1⟩
  obtain ⟨j, hj⟩ := hD ⟨x, hx.2⟩
  have hk' : x ^ 2 ^ k = 1 := congrArg Subtype.val hk
  have hj' : x ^ 3 ^ j = 1 := congrArg Subtype.val hj
  have h1 : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
  have h2 : orderOf x ∣ 3 ^ j := orderOf_dvd_of_pow_eq_one hj'
  have hcop : Nat.Coprime (2 ^ k) (3 ^ j) :=
    Nat.Coprime.pow _ _ (by norm_num)
  have h3 : orderOf x ∣ 1 := hcop ▸ Nat.dvd_gcd h1 h2
  rw [Nat.dvd_one, orderOf_eq_one_iff] at h3
  simp [h3]

theorem map_centralizer_eq [Finite H] (φ : H →* B) (D : Subgroup H) (hD : IsPGroup 3 D)
    (hker : IsPGroup 2 φ.ker) :
    (Subgroup.centralizer (D : Set H)).map φ =
      Subgroup.centralizer ((D.map φ : Subgroup B) : Set B) ⊓ φ.range := by
  have hbot : φ.ker ⊓ D = ⊥ := inf_eq_bot_of_isPGroup _ _ hker hD
  ext b
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨Subgroup.mem_centralizer_iff.mpr fun y hy => ?_, ⟨x, rfl⟩⟩
    obtain ⟨d, hd, rfl⟩ := Subgroup.mem_map.mp hy
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.mp hx d hd]
  · rintro ⟨hb, x₀, rfl⟩
    have hcop : Nat.Coprime 3 (Nat.card φ.rangeRestrict.ker) := by
      rw [MonoidHom.ker_rangeRestrict]
      obtain ⟨n, hn⟩ := hker.exists_card_eq
      rw [hn]
      exact Nat.Coprime.pow_right _ (by norm_num)
    have hnorm := CFSG.SignalizerFunctor.Helpers.coprime_surjective_normalizer_image 3
      Nat.prime_three φ.rangeRestrict φ.rangeRestrict_surjective D hcop hD
    have hmem : φ.rangeRestrict x₀ ∈ Subgroup.normalizer
        ((D.map φ.rangeRestrict : Subgroup ↥φ.range) : Set ↥φ.range) := by
      refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun y hy => ?_)
      obtain ⟨d, hd, rfl⟩ := Subgroup.mem_map.mp hy
      apply Subtype.ext
      exact Subgroup.mem_centralizer_iff.mp hb (φ d) (Subgroup.mem_map_of_mem φ hd)
    rw [← hnorm] at hmem
    obtain ⟨x, hxN, hx⟩ := hmem
    have hxφ : φ x = φ x₀ := congrArg Subtype.val hx
    refine ⟨x, Subgroup.mem_centralizer_iff.mpr fun d hd => ?_, hxφ⟩
    have hconj : x * d * x⁻¹ ∈ D := (Subgroup.mem_normalizer_iff.mp hxN d).mp hd
    have hφ : φ (x * d * x⁻¹) = φ d := by
      have := Subgroup.mem_centralizer_iff.mp hb (φ d) (Subgroup.mem_map_of_mem φ hd)
      calc φ (x * d * x⁻¹) = (φ x₀ * φ d) * (φ x₀)⁻¹ := by rw [map_mul, map_mul, map_inv, hxφ]
        _ = (φ d * φ x₀) * (φ x₀)⁻¹ := by rw [this]
        _ = φ d := by group
    have hker' : (x * d * x⁻¹)⁻¹ * d ∈ φ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hφ, inv_mul_cancel]
    have hD' : (x * d * x⁻¹)⁻¹ * d ∈ D := D.mul_mem (D.inv_mem hconj) hd
    have hone : (x * d * x⁻¹)⁻¹ * d ∈ φ.ker ⊓ D := ⟨hker', hD'⟩
    rw [hbot, Subgroup.mem_bot, inv_mul_eq_one] at hone
    calc d * x = (x * d * x⁻¹) * x := by rw [hone]
      _ = x * d := by group

theorem card_centralizer_eq [Finite H] (φ : H →* B) (D : Subgroup H) (hD : IsPGroup 3 D)
    (hker : IsPGroup 2 φ.ker) :
    Nat.card ↥(Subgroup.centralizer (D : Set H)) =
      Nat.card ↥(Subgroup.centralizer ((D.map φ : Subgroup B) : Set B) ⊓ φ.range) *
        Nat.card ↥(φ.ker ⊓ Subgroup.centralizer (D : Set H)) := by
  rw [← map_centralizer_eq φ D hD hker]
  exact (card_map_mul_card_inf_ker φ _).symm

end S153EH60

end CFSG.Quasithin
