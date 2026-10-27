module

public import CFSG.SignalizerFunctorTheorem.CatalogBridge.NonLocalLargeRee
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.LargeReeFixed
import CFSG.RankThree.SteinbergR3ELargeReeOrder
import CFSG.LieType.Ree.LargeReeFixedGroupOddCore
import CFSG.RankThree.Chevalley.SteinbergBTCanonicalFieldCommon

public section

open CFSG.Open (signalizerFixedSubgroup)
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
open CFSG.RankThree.Chevalley.SteinbergBT (card_fixSubfield)
open CFSG.LieType.Simplicity (isSimpleGroup_quotient_center_reeFixed_F4)

namespace CFSG.SignalizerFunctorTheorem.CatalogBridge

theorem isSimpleGroup_reeGamma_F4
    {b : ℕ} (hb : 1 ≤ b) {k : Type} [Field k] [Finite k]
    [CharP k ReeTag.F4.prime] (hk : Nat.card k = 2 ^ (2 * b + 1)) :
    IsSimpleGroup (ReeTag.F4.reeGamma k b) := by
  set e := ReeTag.reeFixedEquivReeGamma k b
  have hZ : Subgroup.center (reeFixed ReeTag.F4 k b) = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have hz' : e z ∈ Subgroup.center (ReeTag.F4.reeGamma k b) :=
      (MulEquivClass.apply_mem_center_iff e).2 hz
    rw [ReeTag.large_Ree_fixed_group_center_trivial b k hk, Subgroup.mem_bot] at hz'
    exact Subgroup.mem_bot.2 (e.injective (hz'.trans (map_one e).symm))
  have : IsSimpleGroup (reeFixed ReeTag.F4 k b ⧸ Subgroup.center (reeFixed ReeTag.F4 k b)) :=
    isSimpleGroup_quotient_center_reeFixed_F4 b hb hk
  have hs : IsSimpleGroup (reeFixed ReeTag.F4 k b) :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.isSimpleGroup
  exact e.symm.isSimpleGroup

theorem nonLocalized_largeRee_of_ne
    {a : ℕ} (_ha : 1 ≤ a) {K : Type} [Field K] [Finite K]
    [CharP K ReeTag.F4.prime] (hK : Nat.card K = 2 ^ (2 * a + 1)) {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) (hpa : p ≠ 2 * a + 1) (σ : K ≃+* K) (hσ : orderOf σ = p) :
    NonLocalized (signalizerFixedSubgroup (ReeTag.F4.reeGammaFieldAut K a σ)) := by
  classical
  obtain ⟨b, hbp, hkcard, hfixed⟩ := largeRee_fixed_data_odd hK hp (by omega) σ hσ
  have hb1 : 1 ≤ b := by
    by_contra h0
    obtain rfl : b = 0 := by omega
    exact hpa (by omega)
  have : Finite (fixSubfield σ) := Subtype.finite
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP (fixSubfield σ) ReeTag.F4.prime := by
    have : Fintype (fixSubfield σ) := Fintype.ofFinite _
    exact charP_of_card_eq_prime_pow (f := 2 * b + 1) (by
      rw [← Nat.card_eq_fintype_card, hkcard]
      rfl)
  have hFix : signalizerFixedSubgroup (ReeTag.F4.reeGammaFieldAut K a σ) =
      (ReeTag.F4.reeGammaFieldAut K a σ).toMonoidHom.eqLocus (MonoidHom.id _) :=
    Subgroup.ext fun _ => Iff.rfl
  let eC : signalizerFixedSubgroup (ReeTag.F4.reeGammaFieldAut K a σ) ≃*
      ReeTag.F4.reeGamma (fixSubfield σ) b :=
    (((signalizerFixedSubgroup (ReeTag.F4.reeGammaFieldAut K a σ)).equivMapOfInjective
      (ReeTag.F4.reeGamma K a).subtype (ReeTag.F4.reeGamma K a).subtype_injective).trans
      (MulEquiv.subgroupCongr (by rw [hFix]; exact hfixed))).trans
    ((ReeTag.F4.reeGamma (fixSubfield σ) b).equivMapOfInjective _
      (baseChangeGL_injective (τ := ReeTag.F4.tag) (fixSubfield σ).subtype)).symm
  have : IsSimpleGroup (ReeTag.F4.reeGamma (fixSubfield σ) b) :=
    isSimpleGroup_reeGamma_F4 hb1 hkcard
  have hsC : IsSimpleGroup (signalizerFixedSubgroup (ReeTag.F4.reeGammaFieldAut K a σ)) :=
    eC.isSimpleGroup
  have hcardC : 2 ^ 36 ∣ Nat.card (signalizerFixedSubgroup (ReeTag.F4.reeGammaFieldAut K a σ)) := by
    rw [Nat.card_congr eC.toEquiv,
      (CFSG.RankThree.LargeReeOrder.large_Ree_exact_native_order_and_prime_factor_exhaustion b
        (fixSubfield σ) hkcard).1]
    set q := 2 ^ (2 * b + 1) with hq
    have h12 : 2 ^ 36 ∣ q ^ 12 := by
      rw [hq, ← pow_mul]
      exact pow_dvd_pow 2 (by omega)
    exact h12.trans (Dvd.intro ((q - 1) ^ 2 * (q + 1) ^ 2 * (q ^ 2 + 1) ^ 2 * (q ^ 2 - q + 1) *
      (q ^ 4 - q ^ 2 + 1)) (by ring))
  exact nonLocalized_largeRee_of_simple hK σ hsC hcardC

end CFSG.SignalizerFunctorTheorem.CatalogBridge
