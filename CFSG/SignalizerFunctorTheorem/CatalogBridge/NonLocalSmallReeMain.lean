module

public import CFSG.SignalizerFunctorTheorem.CatalogBridge.NonLocalSmallRee
import CFSG.SignalizerFunctorTheorem.CatalogBridge.SmallReeFixed

public section

open CFSG.Open (signalizerFixedSubgroup)
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
open CFSG.RankThree (fixed_reeGamma_eq_map)
open CFSG.ComponentClassification.CatalogueBSmallRee (reeGamma_G2_simple)

namespace CFSG.SignalizerFunctorTheorem.CatalogBridge

theorem card_reeGamma_G2
    {a : ℕ} {K : Type} [Field K] [Finite K] [CharP K ReeTag.G2.prime]
    (hK : Nat.card K = 3 ^ (2 * a + 1)) :
    Nat.card (ReeTag.G2.reeGamma K a) =
      (3 ^ (2 * a + 1)) ^ 3 * ((3 ^ (2 * a + 1)) ^ 3 + 1) * (3 ^ (2 * a + 1) - 1) := by
  obtain ⟨w₀, hw₀, -⟩ := weyl_longest_element ReeTag.G2.tag
  obtain ⟨-, -, -, -, -, -, -, -, -, h, -⟩ := small_Ree_Borel_coset_Sylow_action a K hK w₀ hw₀
  rw [h, mul_right_comm]

theorem nonLocalized_smallRee_of_ne
    {a : ℕ} (_ha : 1 ≤ a) {K : Type} [Field K] [Finite K]
    [CharP K ReeTag.G2.prime] (hK : Nat.card K = 3 ^ (2 * a + 1)) {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) (hpa : p ≠ 2 * a + 1) (σ : K ≃+* K) (hσ : orderOf σ = p) :
    NonLocalized (signalizerFixedSubgroup (ReeTag.G2.reeGammaFieldAut K a σ)) := by
  classical
  obtain ⟨b, hbp, hkcard, hfixed⟩ := smallRee_fixed_data_odd hK hp (by omega) σ hσ
  have hb1 : 1 ≤ b := by
    by_contra h0
    obtain rfl : b = 0 := by omega
    exact hpa (by omega)
  have : Finite (fixSubfield σ) := Subtype.finite
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : CharP (fixSubfield σ) ReeTag.G2.prime := by
    have : Fintype (fixSubfield σ) := Fintype.ofFinite _
    exact charP_of_card_eq_prime_pow (f := 2 * b + 1) (by
      rw [← Nat.card_eq_fintype_card, hkcard]
      rfl)
  have hFix : signalizerFixedSubgroup (ReeTag.G2.reeGammaFieldAut K a σ) =
      (ReeTag.G2.reeGammaFieldAut K a σ).toMonoidHom.eqLocus (MonoidHom.id _) :=
    Subgroup.ext fun _ => Iff.rfl
  let eC : signalizerFixedSubgroup (ReeTag.G2.reeGammaFieldAut K a σ) ≃*
      ReeTag.G2.reeGamma (fixSubfield σ) b :=
    (((signalizerFixedSubgroup (ReeTag.G2.reeGammaFieldAut K a σ)).equivMapOfInjective
      (ReeTag.G2.reeGamma K a).subtype (ReeTag.G2.reeGamma K a).subtype_injective).trans
      (MulEquiv.subgroupCongr (by rw [hFix]; exact hfixed))).trans
    ((ReeTag.G2.reeGamma (fixSubfield σ) b).equivMapOfInjective _
      (baseChangeGL_injective (τ := ReeTag.G2.tag) (fixSubfield σ).subtype)).symm
  obtain ⟨-, hs, -⟩ := reeGamma_G2_simple (Nat.pos_of_ne_zero (by omega)) (fixSubfield σ) hkcard
  have : IsSimpleGroup (ReeTag.G2.reeGamma (fixSubfield σ) b) := hs
  have hsC : IsSimpleGroup (signalizerFixedSubgroup (ReeTag.G2.reeGammaFieldAut K a σ)) :=
    eC.isSimpleGroup
  have hcardC : 3 ^ 9 ∣ Nat.card (signalizerFixedSubgroup (ReeTag.G2.reeGammaFieldAut K a σ)) := by
    rw [Nat.card_congr eC.toEquiv, card_reeGamma_G2 hkcard]
    refine Dvd.dvd.mul_right (Dvd.dvd.mul_right ?_ _) _
    rw [← pow_mul]
    exact pow_dvd_pow 3 (by omega)
  exact nonLocalized_smallRee_of_simple hK σ hsC hcardC

end CFSG.SignalizerFunctorTheorem.CatalogBridge
