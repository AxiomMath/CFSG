module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven.OddFieldFixBase
import CFSG.Blueprint.LieModelAPI
import CFSG.SignalizerFunctorTheorem.McBride.Models.Transport
import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderTwistedE6Descent
import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderTwistedE6Diag
import CFSG.LocalAnalysis.GLTheoremA.CatA.FRTD4
import CFSG.RankThree.Chevalley.SteinbergBTTwistedE6OddField
import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD291OuterLieTw
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven.OddAutSylow

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven

open Subgroup
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem fixesSylowOutside_twistedE6
    {X : Type} [Group X] [Finite X] {n r f : ℕ} (hr2 : r ≠ 2)
    (hadm : CFSG.Open.StatedLieAdmissible .twistedE6 n r f)
    (hX : CFSG.Blueprint.LieModel X .twistedE6 n r f) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    FixesSylowOutside X (inner X) p := by
  intro α hα hout
  classical
  have hp2 : p ≠ 2 := by omega
  have : Fact p.Prime := ⟨hp⟩
  have hα1 : α ≠ 1 := fun h => hout (h ▸ (inner X).one_mem)
  have hord : orderOf α = p := orderOf_eq_prime hα hα1
  have hrp : r.Prime := hadm.1
  have hf : 1 ≤ f := hadm.2.1
  have hrodd : Odd r := hrp.odd_of_ne_two hr2
  obtain ⟨-, hchev⟩ :=
    (CFSG.Blueprint.LieModel.chevalleyExceptional_iff (by decide)).1 hX
  obtain ⟨K, _, _, σ, hcard, hσ, ⟨e'⟩⟩ :=
    CFSG.LieType.Chevalley.exists_mulEquiv_graphFixedRootGroup_E6 hchev
  have : Finite (graphFixedRootGroup TwistTag.E6 K σ.toRingHom) := Subtype.finite
  let α' : MulAut (graphFixedRootGroup TwistTag.E6 K σ.toRingHom) := MulAut.congr e' α
  have hα'ord : orderOf α' = p :=
    (CFSG.SignalizerFunctorTheorem.McBride.orderOf_congr e' α).trans hord
  have hα'p : α' ^ p = 1 := hα'ord ▸ pow_orderOf_eq_one α'
  have hα'in : α' ∉ inner (graphFixedRootGroup TwistTag.E6 K σ.toRingHom) := fun hin =>
    hout ((CFSG.HardMathSupport.Lang.Coordinator.congr_mem_inner_iff e' α).mp hin)
  have hK2f : Nat.card K = r ^ (2 * f) := by rw [hcard, ← pow_mul, mul_comm]
  obtain ⟨-, -, -, -, -, -, -, -, ⟨Θ, hΘ, -, hker, -, hcube, -⟩, -, -, -, -, -⟩ :=
    CFSG.LieType.Chevalley.twisted_E6_all_characteristic_exact_automorphism_normal_form
      hrp hf K hcard σ hσ
  have hpg : ¬ p ∣ Nat.gcd 3 (r ^ f + 1) := by
    intro h
    have h1 : p ∣ 3 := h.trans (Nat.gcd_dvd_left 3 _)
    have h2 : p ≤ 3 := Nat.le_of_dvd (by norm_num) h1
    omega
  have hη1 : Θ α' ≠ 1 := by
    intro h1
    have hmem : α' ∈ CFSG.LieType.Chevalley.twistedE6Inn K σ ⊔
        CFSG.LieType.Chevalley.twistedE6Diag K σ := by
      rw [← hker, MonoidHom.mem_ker]
      exact h1
    exact hα'in (CFSG.HardMathSupport.Lang.Coordinator.mem_inner_of_mem_inn_sup_diag
      hp hcard hσ hpg hcube hα'p hmem)
  obtain ⟨d, hd, hd1, r₀, s, T, ε, hT, hε, hrs, ψ, hψpow, -⟩ :=
    CFSG.HardMathSupport.Lang.Coordinator.twisted_E6_field_descent_data_of_prime_order
      hrp hf K hK2f σ hσ Θ hΘ hp hp2 α' hα'p hη1
  obtain ⟨fr, hfr, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      hrp (by omega : 1 ≤ 2 * f) hK2f
  obtain ⟨κ, hκ⟩ : ∃ κ : K ≃+* K, ∀ c, κ c = c ^ r ^ (2 * d) :=
    ⟨fr ^ (2 * d), fun c => CFSG.LieType.Chevalley.ringAut_pow_apply_of_frobenius hfr (2 * d) c⟩
  have hKdp : Nat.card K = r ^ (2 * d * p) := by
    rw [hK2f, hd]
    congr 1
    ring
  have hσdp : ∀ c, σ c = c ^ r ^ (d * p) := fun c => by
    rw [hσ c, hd, mul_comm p d]
  have hσ₀ : ∀ c : CFSG.LieType.Chevalley.fixSubfield κ,
      (CFSG.LieType.Chevalley.fixSubfieldRestrict T κ c : K) = (c : K) ^ r ^ d :=
    fun c => by rw [CFSG.LieType.Chevalley.coe_fixSubfieldRestrict, hT]
  have hm3 : 3 ≤ p := by omega
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  obtain ⟨-, hkcard, hJC, -, hder, hsimpleJ, -, -⟩ :=
    CFSG.RankThree.Chevalley.twisted_E6_canonical_odd_field_derived_subgroup_and_pointwise_centralizer
      hrp hd1 hm3 hpodd K hKdp κ hκ σ hσdp (CFSG.LieType.Chevalley.fixSubfieldRestrict T κ)
      hσ₀ ε hε
  set δ := CFSG.LieType.Chevalley.fieldActor (t := TwistTag.E6) σ ε with hδ
  set J := CFSG.RankThree.Chevalley.subfieldRootGroupImage TwistTag.E6
    (CFSG.LieType.Chevalley.fixSubfield κ) (CFSG.LieType.Chevalley.fixSubfieldRestrict T κ)
    with hJdef
  have hder' : ⁅fixedSubgroup δ, fixedSubgroup δ⁆ =
      J.subgroupOf (CFSG.LieType.Chevalley.twistedE6RootGroup K σ) := hder
  have hJΓ : J.subgroupOf (CFSG.LieType.Chevalley.twistedE6RootGroup K σ) ≤ fixedSubgroup δ := by
    rw [← hder']
    exact Subgroup.commutator_le_self _
  have hσ₀' : ∀ c : CFSG.LieType.Chevalley.fixSubfield κ,
      (CFSG.LieType.Chevalley.fixSubfieldRestrict T κ) c = c ^ (r ^ d) := fun c =>
    Subtype.ext (by rw [hσ₀]; rfl)
  have hkcard' : Nat.card (CFSG.LieType.Chevalley.fixSubfield κ) =
      (r ^ d) ^ TwistTag.E6.order := by
    rw [hkcard, ← pow_mul, mul_comm]
    rfl
  have hmodel := CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291OL.twistedModel_graphFixedRootGroup
    (t := TwistTag.E6) hrp hd1 (CFSG.LieType.Chevalley.fixSubfield κ) hkcard'
    (CFSG.LieType.Chevalley.fixSubfieldRestrict T κ) hσ₀'
  let eJ : ↥(graphFixedRootGroup TwistTag.E6 (CFSG.LieType.Chevalley.fixSubfield κ)
      (CFSG.LieType.Chevalley.fixSubfieldRestrict T κ).toRingHom) ≃* ↥J :=
    Subgroup.equivMapOfInjective
      (graphFixedRootGroup TwistTag.E6 (CFSG.LieType.Chevalley.fixSubfield κ)
        (CFSG.LieType.Chevalley.fixSubfieldRestrict T κ).toRingHom)
      (CFSG.LieType.Chevalley.baseChangeGL (τ := TwistTag.E6.tag)
        (CFSG.LieType.Chevalley.fixSubfield κ).subtype)
      (CFSG.LieType.Chevalley.baseChangeGL_injective _)
  let eJC : ↥(J.subgroupOf (CFSG.LieType.Chevalley.twistedE6RootGroup K σ)) ≃* ↥J :=
    Subgroup.subgroupOfEquivOfLe hJC
  let ιJ : ↥J →* graphFixedRootGroup TwistTag.E6 K σ.toRingHom :=
    (Subgroup.subtype (J.subgroupOf (CFSG.LieType.Chevalley.twistedE6RootGroup K σ))).comp
      eJC.symm.toMonoidHom
  have hιJ : Function.Injective ιJ :=
    (Subgroup.subtype_injective (J.subgroupOf
      (CFSG.LieType.Chevalley.twistedE6RootGroup K σ))).comp eJC.symm.injective
  have hfixJ : ∀ y, δ (ιJ y) = ιJ y := fun y => hJΓ (eJC.symm y).2
  let H := ↥(graphFixedRootGroup TwistTag.E6 (CFSG.LieType.Chevalley.fixSubfield κ)
      (CFSG.LieType.Chevalley.fixSubfieldRestrict T κ).toRingHom)
  let ι' : H →* X := e'.symm.toMonoidHom.comp (ψ.symm.toMonoidHom.comp (ιJ.comp eJ.toMonoidHom))
  have hι' : Function.Injective ι' :=
    e'.symm.injective.comp (ψ.symm.injective.comp (hιJ.comp eJ.injective))
  have hfix' : ∀ y, α (ι' y) = ι' y := by
    intro y
    have hψcongr : MulAut.congr ψ (α' ^ r₀) = δ := by
      have heq : MulAut.congr ψ (α' ^ r₀) = ψ * α' ^ r₀ * ψ⁻¹ := by
        ext x
        rfl
      exact heq.trans hψpow
    have hkeep : δ (ιJ (eJ y)) = ιJ (eJ y) := hfixJ (eJ y)
    have hz : (α' ^ r₀) (ψ.symm (ιJ (eJ y))) = ψ.symm (ιJ (eJ y)) := by
      have h2 : (MulAut.congr ψ (α' ^ r₀)) (ιJ (eJ y)) = ιJ (eJ y) := by
        rw [hψcongr]
        exact hkeep
      have h1 : ψ ((α' ^ r₀) (ψ.symm (ιJ (eJ y)))) = ιJ (eJ y) := by
        have h2' := h2
        rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply] at h2'
        exact h2'
      have h3 := congrArg ψ.symm h1
      rw [MulEquiv.symm_apply_apply] at h3
      exact h3
    have hzα : α' (ψ.symm (ιJ (eJ y))) = ψ.symm (ιJ (eJ y)) := by
      rw [← hrs]
      exact CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291OL.fixedSubgroup_le_pow'
        (α' ^ r₀) s (show ψ.symm (ιJ (eJ y)) ∈ fixedSubgroup (α' ^ r₀) from hz)
    have key : ∀ z : graphFixedRootGroup TwistTag.E6 K σ.toRingHom,
        α (e'.symm z) = e'.symm (α' z) := by
      intro z
      have hzz : α' z = e' (α (e'.symm z)) := by
        show MulAut.congr e' α z = e' (α (e'.symm z))
        rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply]
      rw [hzz, MulEquiv.symm_apply_apply]
    calc α (ι' y) = α (e'.symm (ψ.symm (ιJ (eJ y)))) := rfl
      _ = e'.symm (α' (ψ.symm (ιJ (eJ y)))) := key _
      _ = e'.symm (ψ.symm (ιJ (eJ y))) := by rw [hzα]
      _ = ι' y := rfl
  have hcardH : Nat.card H = CFSG.EvenSmallLie.CatalogOrders.lieOrd .twistedE6 0 (r ^ d) :=
    CFSG.EvenSmallLie.CatalogOrders.card_eq_lieOrd_of_exceptional ⟨⟨hrp, hd1, rfl⟩, hmodel⟩
  have hcardX : Nat.card X = CFSG.EvenSmallLie.CatalogOrders.lieOrd .twistedE6 0 (r ^ f) :=
    CFSG.EvenSmallLie.CatalogOrders.card_eq_lieOrd_of_exceptional hchev
  have hcard2 : (Nat.card H).factorization 2 = (Nat.card X).factorization 2 := by
    have hfeq : r ^ f = (r ^ d) ^ p := by rw [hd, mul_comm p d, pow_mul]
    rw [hcardH]
    rw [hcardX]
    rw [hfeq]
    exact (factorization_two_lieOrd_pow (q := r ^ d) (k := p) .twistedE6 0
      (hrodd.pow) hpodd).symm
  exact exists_isSylowOf_fixed_of_injective ι' hι' α hfix' hcard2

theorem fixesSylowOutside_trialityD4
    {X : Type} [Group X] [Finite X] {n r f : ℕ} (hr2 : r ≠ 2)
    (hadm : CFSG.Open.StatedLieAdmissible .trialityD4 n r f)
    (hX : CFSG.Blueprint.LieModel X .trialityD4 n r f) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    FixesSylowOutside X (inner X) p := by
  intro α hα hout
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hα1 : α ≠ 1 := fun h => hout (h ▸ (inner X).one_mem)
  have hord : orderOf α = p := orderOf_eq_prime hα hα1
  have hrp : r.Prime := hadm.1
  have hf : 1 ≤ f := hadm.2.1
  obtain ⟨-, hchev⟩ :=
    (CFSG.Blueprint.LieModel.chevalleyExceptional_iff (by decide)).1 hX
  obtain ⟨K, _, _, σ, hcard, hσ, ⟨e'⟩⟩ :=
    CFSG.LieType.Chevalley.exists_mulEquiv_graphFixedRootGroup_card TwistTag.D4 hrp hf hchev.2
  have : Finite (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := Subtype.finite
  let α' : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := MulAut.congr e' α
  have hα'ord : orderOf α' = p :=
    (CFSG.SignalizerFunctorTheorem.McBride.orderOf_congr e' α).trans hord
  have hα'p : α' ^ p = 1 := hα'ord ▸ pow_orderOf_eq_one α'
  have hα'in : α' ∉ inner (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := fun hin =>
    hout ((CFSG.HardMathSupport.Lang.Coordinator.congr_mem_inner_iff e' α).mp hin)
  obtain ⟨f₀, k₀, _, _, σ₀, hf_eq, hk₀, hσ₀, hmod0, ⟨eFix⟩⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.FR.trialityD4_outer_fixed_equiv
      hrp hf hp hp5 K hcard σ hσ α' hα'p hα'in
  have hp2 : p ≠ 2 := by omega
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have hrodd : Odd r := hrp.odd_of_ne_two hr2
  have hq0odd : Odd (r ^ f₀) := hrodd.pow
  have hd1 : 1 ≤ f₀ := by
    rcases Nat.eq_zero_or_pos f₀ with h | h
    · rw [h, mul_zero] at hf_eq
      omega
    · exact h
  have hmod' : p % 3 = 1 ∨ p % 3 = 2 := by
    have hlt : p % 3 < 3 := Nat.mod_lt _ (by norm_num)
    have hne : p % 3 ≠ 0 := by
      intro h
      have h3 : 3 ∣ p := Nat.dvd_of_mod_eq_zero h
      have h3' := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1 h3
      omega
    omega
  let ι : ↥(graphFixedRootGroup TwistTag.D4 k₀ σ₀.toRingHom) →*
      graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
    (Subgroup.subtype (fixedSubgroup α')).comp eFix.symm.toMonoidHom
  have hι : Function.Injective ι :=
    (Subgroup.subtype_injective (fixedSubgroup α')).comp eFix.symm.injective
  have hfix : ∀ y, α' (ι y) = ι y := fun y => (eFix.symm y).2
  let ι' : ↥(graphFixedRootGroup TwistTag.D4 k₀ σ₀.toRingHom) →* X :=
    e'.symm.toMonoidHom.comp ι
  have hι' : Function.Injective ι' := e'.symm.injective.comp hι
  have hfix' : ∀ y, α (ι' y) = ι' y := by
    intro y
    have h1 : α' (ι y) = ι y := hfix y
    have key : ∀ z : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
        α (e'.symm z) = e'.symm (α' z) := by
      intro z
      have hzz : α' z = e' (α (e'.symm z)) := by
        show MulAut.congr e' α z = e' (α (e'.symm z))
        rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply]
      rw [hzz, MulEquiv.symm_apply_apply]
    calc α (ι' y) = α (e'.symm (ι y)) := rfl
      _ = e'.symm (α' (ι y)) := key (ι y)
      _ = e'.symm (ι y) := by rw [h1]
      _ = ι' y := rfl
  have hcardX : Nat.card X = CFSG.EvenSmallLie.CatalogOrders.lieOrd .trialityD4 0 (r ^ f) :=
    CFSG.EvenSmallLie.CatalogOrders.card_eq_lieOrd_of_exceptional hchev
  have hcardH : Nat.card ↥(graphFixedRootGroup TwistTag.D4 k₀ σ₀.toRingHom)
      = CFSG.EvenSmallLie.CatalogOrders.lieOrd .trialityD4 0 (r ^ f₀) := by
    have h1 := (triality_both_orientations_exact_finite_order r f₀ hrp hd1 k₀ hk₀ (p % 3)
      hmod' σ₀.toRingHom hσ₀).1
    rw [h1]
    unfold CFSG.EvenSmallLie.CatalogOrders.lieOrd CFSG.Open.ordTrialityD4
    ring
  have hcard2 : (Nat.card ↥(graphFixedRootGroup TwistTag.D4 k₀ σ₀.toRingHom)).factorization 2
      = (Nat.card X).factorization 2 := by
    have hfeq : r ^ f = (r ^ f₀) ^ p := by rw [hf_eq, mul_comm p f₀, pow_mul]
    rw [hcardH]
    rw [hcardX]
    rw [hfeq]
    exact (factorization_two_lieOrd_pow (q := r ^ f₀) (k := p) .trialityD4 0 hq0odd hpodd).symm
  exact exists_isSylowOf_fixed_of_injective ι' hι' α hfix' hcard2

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven
