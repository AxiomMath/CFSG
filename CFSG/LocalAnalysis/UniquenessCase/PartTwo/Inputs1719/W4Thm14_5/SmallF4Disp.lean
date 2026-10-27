module

public import CFSG.LieType.Ree.FixedSubgroupData
public import CFSG.Quasithin.Background.Module
import CFSG.Quasithin.Background.SmithB42F4Main

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5

open CFSG.Quasithin CFSG.Quasithin.B42Disp CFSG.Quasithin.B42F4
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Ree.ReeTag CFSG.LieType.Ree.LargeReeInvolution



theorem two_pow_le_index_pow_four_of_twistedF4 {I : Type} [CommGroup I] [Finite I]
    (hI : ∀ w : I, w * w = 1) {L : Subgroup (MulAut I)} {K : Type} [Field K] [Finite K]
    [CharP K F4.prime] {a : ℕ} (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    (ε : ↥L ≃* ↥(F4.reeGamma K a)) {y : MulAut I} (hy : y ∈ L) (hyy : y * y = 1) (hy1 : y ≠ 1) :
    2 ^ (12 * (2 * a + 1)) ≤ (fixV (Subgroup.zpowers y)).index ^ 4 := by
  classical
  obtain ⟨ℓ, hℓ, hℓ2, hord⟩ := exists_prime_orderOf_two_eq (12 * (2 * a + 1)) (by omega) (by omega)
  obtain ⟨c, hcΓ, hcord, hinv⟩ := exists_inverted_by_tOne ha hK hℓ hℓ2 hord
  set φ : ↥(F4.reeGamma K a) →* MulAut I := L.subtype.comp ε.symm.toMonoidHom with hφ
  have hφinj : Function.Injective φ := L.subtype_injective.comp ε.symm.injective
  have horder : ∀ g, orderOf (φ g) = orderOf g := fun g => orderOf_injective φ hφinj g
  set ξ : ↥(F4.reeGamma K a) := ε ⟨y, hy⟩ with hξ
  have hφξ : φ ξ = y := by simp [hφ, hξ]
  have hξξ : ξ * ξ = 1 := hφinj (by rw [map_mul, hφξ, hyy, map_one])
  have hξ2 : (ξ : ModGL F4.tag K) ^ 2 = 1 := by
    rw [sq, ← Subgroup.coe_mul, hξξ, Subgroup.coe_one]
  have hξ1 : (ξ : ModGL F4.tag K) ≠ 1 := fun h =>
    hy1 (by rw [← hφξ, show ξ = 1 from Subtype.ext h, map_one])
  have hpos : 0 < (fixV (Subgroup.zpowers y)).index :=
    Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite)
  rcases isZConj_or_isTConj ha hK ξ.2 hξ2 hξ1 with ⟨g, hg, hgξ⟩ | ⟨g, hg, hgξ⟩
  ·
    obtain ⟨p₁, hp₁, p₂, hp₂, ht⟩ := exists_tOne_eq_conj_mul_conj (a := a) hK
    have hξg : (ξ : ModGL F4.tag K) = g⁻¹ * sylowH a K 0 1 * g := by rw [← hgξ]; group
    set m₁ : ↥(F4.reeGamma K a) := ⟨p₁ * g, mul_mem hp₁ hg⟩ with hm₁
    set m₂ : ↥(F4.reeGamma K a) := ⟨p₂ * g, mul_mem hp₂ hg⟩ with hm₂
    set cc : ↥(F4.reeGamma K a) := ⟨c, hcΓ⟩ with hcc
    set T : ↥(F4.reeGamma K a) := m₁ * ξ * m₁⁻¹ * (m₂ * ξ * m₂⁻¹) with hT
    have hTv : (T : ModGL F4.tag K) = sylowL a K 1 := by
      rw [hT]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hm₁, hm₂]
      rw [hξg, ht]
      group
    have key : ∀ T' : ↥(F4.reeGamma K a), (T' : ModGL F4.tag K) = sylowL a K 1 →
        T' * (cc * T' * cc⁻¹) = cc⁻¹ ^ 2 := by
      intro T' hT'
      refine Subtype.ext ?_
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
        Subgroup.coe_pow, Subgroup.coe_inv, hT']
      change sylowL a K 1 * (c * sylowL a K 1 * c⁻¹) = c⁻¹ ^ 2
      calc sylowL a K 1 * (c * sylowL a K 1 * c⁻¹) =
          (sylowL a K 1 * c * (sylowL a K 1)⁻¹) * (sylowL a K 1 * sylowL a K 1) * c⁻¹ := by
            group
        _ = c⁻¹ ^ 2 := by rw [hinv, sylowL_mul_self, mul_one, sq]
    have hTc := key T hTv
    have hprod : ([m₁, m₂, cc * m₁, cc * m₂].map fun m => m * ξ * m⁻¹).prod =
        T * (cc * T * cc⁻¹) := by
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, hT]
      group
    have hprodL : (([m₁, m₂, cc * m₁, cc * m₂].map φ).map fun h => h * y * h⁻¹).prod =
        φ (cc⁻¹ ^ 2) := by
      rw [← hTc, ← hprod, ← hφξ]
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, map_mul, map_inv,
        map_one]
    have hco : orderOf cc = ℓ := by rw [← Subgroup.orderOf_coe]; exact hcord
    have hdvd : ℓ ∣ orderOf (([m₁, m₂, cc * m₁, cc * m₂].map φ).map fun h => h * y * h⁻¹).prod := by
      rw [hprodL, horder, orderOf_pow' _ two_ne_zero, orderOf_inv, hco,
        (Nat.coprime_primes hℓ Nat.prime_two).2 hℓ2, Nat.div_one]
    simpa [hord] using two_pow_le_index_pow hI hℓ hℓ2 y _ hdvd
  ·
    have hξg : (ξ : ModGL F4.tag K) = g⁻¹ * sylowL a K 1 * g := by rw [← hgξ]; group
    set c' : ↥(F4.reeGamma K a) := ⟨g⁻¹ * c * g, mul_mem (mul_mem (inv_mem hg) hcΓ) hg⟩ with hc'
    have hinv' : ξ * c' * ξ⁻¹ = c'⁻¹ := by
      refine Subtype.ext ?_
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hc']
      rw [hξg]
      calc g⁻¹ * sylowL a K 1 * g * (g⁻¹ * c * g) * (g⁻¹ * sylowL a K 1 * g)⁻¹ =
          g⁻¹ * (sylowL a K 1 * c * (sylowL a K 1)⁻¹) * g := by group
        _ = (g⁻¹ * c * g)⁻¹ := by rw [hinv]; group
    have hinvL : y * φ c' * y⁻¹ = (φ c')⁻¹ := by
      rw [← hφξ, ← map_inv, ← map_mul, ← map_mul, hinv', map_inv]
    have hc'ord : orderOf c' = ℓ := by
      rw [← Subgroup.orderOf_coe, hc']
      change orderOf (g⁻¹ * c * g) = ℓ
      rw [show g⁻¹ * c * g = MulAut.conj g⁻¹ c by simp, MulEquiv.orderOf_eq, hcord]
    have h2 := two_pow_le_index_sq_of_inverts hI hℓ hℓ2 hyy hinvL (by rw [horder, hc'ord])
    rw [hord] at h2
    exact h2.trans (Nat.pow_le_pow_right hpos (by norm_num))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5
