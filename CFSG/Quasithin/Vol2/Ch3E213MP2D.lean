module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.H13.QRCBenderModels

public section

namespace CFSG.Quasithin.Ch3E213M.P2

open Subgroup CFSG.ABGLocalTools CFSG.Quasithin.SteinbergBS

theorem exists_inverted_of_bender {G : Type*} [Group G] [Finite G] {U : Subgroup G} {n : ℕ}
    (hD : H13.QRC.BenderData G U n) {e : G} (heU : e ∈ U) (he : orderOf e = 2) :
    ∃ x : G, x ∉ normalizer (U : Set G) ∧ ∃ ℓ : ℕ, ℓ.Prime ∧ ℓ ≠ 2 ∧ orderOf x = ℓ ∧
      e * x * e⁻¹ = x⁻¹ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := normalizer (U : Set G) with hN
  have he2 : e * e = 1 := by rw [← sq, ← he, pow_orderOf_eq_one]
  have heinv : e⁻¹ = e := inv_eq_of_mul_eq_one_right he2
  have hsyl : IsSylowOf 2 U ⊤ := isSylowOf_iff.2 ⟨le_top, hD.isPGroup, by
    rw [relIndex_top_right]; exact hD.not_dvd_index⟩
  have hCU : ∀ g : G, e * g = g * e → g ∈ U := by
    intro g hg
    have hUC : U ≤ centralizer ({e} : Set G) := fun u hu => by
      rw [mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff.1 hh]
      exact hD.sq_comm e heU (by rw [sq, he2]) u hu
    have h1 := hsyl.eq_of_le hUC le_top (hD.centralizer_isPGroup e he)
    rw [← h1, mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff.1 hh]
    exact hg
  obtain ⟨y, hyN⟩ : ∃ y, y ∉ N := by
    by_contra h
    push Not at h
    exact hD.stronglyEmbedded.1 (eq_top_iff.2 fun x _ => h x)
  set c := e * (y⁻¹ * e * y) with hc
  have he'2 : (y⁻¹ * e * y) * (y⁻¹ * e * y) = 1 :=
    calc (y⁻¹ * e * y) * (y⁻¹ * e * y) = y⁻¹ * (e * e) * y := by group
      _ = 1 := by rw [he2]; group
  have he'inv : (y⁻¹ * e * y)⁻¹ = y⁻¹ * e * y := inv_eq_of_mul_eq_one_right he'2
  have hc1 : c ≠ 1 := by
    intro h1
    apply hyN
    have h1' : e * (y⁻¹ * e * y) = 1 := h1
    have h3 : y⁻¹ * e * y = e := (eq_inv_of_mul_eq_one_right h1').trans heinv
    have h2 : e * y = y * e :=
      calc e * y = y * (y⁻¹ * e * y) := by group
        _ = y * e := by rw [h3]
    exact le_normalizer (hCU y h2)
  have hec : e * c * e⁻¹ = c⁻¹ := by
    rw [hc, mul_inv_rev, he'inv, heinv]
    calc e * (e * (y⁻¹ * e * y)) * e = (e * e) * (y⁻¹ * e * y) * e := by group
      _ = y⁻¹ * e * y * e := by rw [he2, one_mul]
  have hconj : ∀ j : ℕ, e * c ^ j * e⁻¹ = (c ^ j)⁻¹ := fun j => by
    rw [← MulAut.conj_apply, map_pow, MulAut.conj_apply, hec, inv_pow]
  have hodd : ¬ 2 ∣ orderOf c := by
    intro h2
    set z := c ^ (orderOf c / 2) with hz
    have hzo : orderOf z = 2 := orderOf_pow_orderOf_div (orderOf_pos c).ne' h2
    have hz2 : z * z = 1 := by rw [← sq, ← hzo, pow_orderOf_eq_one]
    have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
    have hez : e * z = z * e := by
      have h1 := hconj (orderOf c / 2)
      rw [← hz, hzinv] at h1
      calc e * z = e * z * e⁻¹ * e := by group
        _ = z * e := by rw [h1]
    have hzU : z ∈ U := hCU z hez
    have hyz : e * (y * z * y⁻¹) = (y * z * y⁻¹) * e := by
      have h1 : (y⁻¹ * e * y) * c * (y⁻¹ * e * y)⁻¹ = c⁻¹ := by
        rw [he'inv, hc, mul_inv_rev, he'inv, heinv]
        calc y⁻¹ * e * y * (e * (y⁻¹ * e * y)) * (y⁻¹ * e * y) =
            y⁻¹ * e * y * e * ((y⁻¹ * e * y) * (y⁻¹ * e * y)) := by group
          _ = y⁻¹ * e * y * e := by rw [he'2, mul_one]
      have h2 : (y⁻¹ * e * y) * z * (y⁻¹ * e * y)⁻¹ = z := by
        rw [hz, ← MulAut.conj_apply, map_pow, MulAut.conj_apply, h1, inv_pow, ← hz, hzinv]
      calc e * (y * z * y⁻¹) = y * ((y⁻¹ * e * y) * z * (y⁻¹ * e * y)⁻¹) * y⁻¹ * e := by group
        _ = (y * z * y⁻¹) * e := by rw [h2]
    have hyzU : y * z * y⁻¹ ∈ U := hCU _ hyz
    have hzNN : z ∈ N ⊓ N.map (MulAut.conj y⁻¹).toMonoidHom :=
      ⟨le_normalizer hzU, ⟨y * z * y⁻¹, le_normalizer hyzU, by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
        group⟩⟩
    have h3 := Subgroup.orderOf_dvd_natCard _ hzNN
    rw [hzo] at h3
    exact (Nat.not_even_iff_odd.2 (hD.stronglyEmbedded.2.2 y hyN)) (even_iff_two_dvd.2 h3)
  have hm1 : orderOf c ≠ 1 := fun h => hc1 (orderOf_eq_one_iff.1 h)
  obtain ⟨ℓ, hℓ, hℓm⟩ := Nat.exists_prime_and_dvd hm1
  have hℓ2 : ℓ ≠ 2 := fun h => hodd (h ▸ hℓm)
  set x := c ^ (orderOf c / ℓ) with hx
  have hxo : orderOf x = ℓ := orderOf_pow_orderOf_div (orderOf_pos c).ne' hℓm
  have hex : e * x * e⁻¹ = x⁻¹ := hconj _
  refine ⟨x, fun hxN => ?_, ℓ, hℓ, hℓ2, hxo, hex⟩
  have h1 : x * e⁻¹ * x⁻¹ ∈ U := (mem_normalizer_iff.1 hxN e⁻¹).1 (U.inv_mem heU)
  have h2 : (x ^ 2)⁻¹ ∈ U := by
    have h3 := U.mul_mem heU h1
    rwa [show e * (x * e⁻¹ * x⁻¹) = e * x * e⁻¹ * x⁻¹ by group, hex, ← mul_inv_rev,
      ← sq] at h3
  obtain ⟨j, hj⟩ := hD.isPGroup ⟨_, h2⟩
  have hj' : (x ^ 2) ^ 2 ^ j = 1 := by
    have := congrArg Subtype.val hj
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one, inv_pow] at this
    exact inv_eq_one.1 this
  have h4 : ℓ ∣ 2 * 2 ^ j := by
    rw [← hxo]
    exact orderOf_dvd_of_pow_eq_one (by rw [pow_mul]; exact hj')
  rw [← pow_succ'] at h4
  exact hℓ2 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).1 (hℓ.dvd_of_dvd_pow h4))

end CFSG.Quasithin.Ch3E213M.P2
