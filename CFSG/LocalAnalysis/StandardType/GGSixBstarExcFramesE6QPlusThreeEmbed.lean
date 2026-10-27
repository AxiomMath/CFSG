module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesE6QPlusThreeLang
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross.ExcLangNE6Two
public import CFSG.LieType.Chevalley.CoordinateFieldBaseChange
public import CFSG.LieType.Chevalley.GraphFixedF4GroupDescent
public import CFSG.Timmesfeld.Orders.ExceptionalUntwisted
public import CFSG.LieType.Chevalley.PerfectSimpleRoot
public import CFSG.HardMathSupport.Curtis.UnitaryLevi.ExcSylowN
public import CFSG.LieType.Chevalley.ChevalleySplitBN
public import CFSG.LieType.SeitzGeneration.Lift
public import CFSG.LieType.SeitzGeneration.RegimesExcFamilies

public section

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Lattice
  CFSG.RankThree.PartOne.KE6 CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

namespace CFSG.StandardType.ExcFrames.E6QPlusThree

section Certs

variable {K : Type} [Field K] [Finite K] {L : Type} [Field L] [Algebra K L]

theorem negPhi_conj_baseChangeGL
    (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ Nat.card K)
    {g0 : ModGL .E6 L} (hg0 : Units.map (entrywiseHom Fr) g0 = g0 * eqpN L) (x : ModGL .E6 K) :
    negPhi Fr (eqpN L) (g0⁻¹ * baseChangeGL (algebraMap K L) x * g0) =
      g0⁻¹ * baseChangeGL (algebraMap K L) x * g0 := by
  rw [negPhi_apply, map_mul, map_mul, map_inv, hg0,
    units_map_entrywiseHom_baseChangeGL_algebraMap Fr hFr x]
  group

theorem card_NFix_eqpN [IsAlgClosure K L]
    (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ Nat.card K) :
    Nat.card (NFix (eqpN L) Fr) = (Nat.card K + 1) ^ 4 * (Nat.card K - 1) ^ 2 * 1152 := by
  haveI : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have hq : 2 ≤ Nat.card K := Finite.one_lt_card
  have hq1 : 1 ≤ Nat.card K := by omega
  haveI : Fintype K := Fintype.ofFinite K
  have hq0 : (Nat.card K : L) = 0 := by
    rw [Nat.card_eq_fintype_card, ← map_natCast (algebraMap K L) (Fintype.card K),
      FiniteField.cast_card_eq_zero K, map_zero]
  rw [card_NFix_gen Fr e6W0 hq hFr, card_centralizer_e6W0]
  rw [natCard_eqpTorus (Fr := Fr) hFr hq0 hq1]

theorem finite_NFix_eqpN [IsAlgClosure K L]
    (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ Nat.card K) :
    Finite (NFix (eqpN L) Fr) := by
  refine Nat.finite_of_card_ne_zero ?_
  rw [card_NFix_eqpN Fr hFr]
  have hq : 2 ≤ Nat.card K := Finite.one_lt_card
  exact mul_ne_zero
    (mul_ne_zero (pow_ne_zero _ (by omega : Nat.card K + 1 ≠ 0))
      (pow_ne_zero _ (by omega : Nat.card K - 1 ≠ 0))) (by norm_num)

theorem exists_nfixEmb [IsAlgClosure K L]
    (h3 : ¬ 3 ∣ Nat.card K - 1) (Fr : L →+* L)
    (hFr : ∀ c, Fr c = c ^ Nat.card K) {g0 : ModGL .E6 L} (hg0C : g0 ∈ adjointGroup .E6 L)
    (hg0 : Units.map (entrywiseHom Fr) g0 = g0 * eqpN L) :
    ∃ ι : NFix (eqpN L) Fr →* adjointGroup .E6 K, Function.Injective ι ∧
      (∀ y : NFix (eqpN L) Fr, baseChangeGL (algebraMap K L)
          ((ι y : adjointGroup .E6 K) : ModGL .E6 K) = g0 * (y : ModGL .E6 L) * g0⁻¹) ∧
      ∀ x : adjointGroup .E6 K,
        g0⁻¹ * baseChangeGL (algebraMap K L) (x : ModGL .E6 K) * g0 ∈ monomialSubgroup .E6 L →
          x ∈ ι.range := by
  classical
  haveI hNF : Finite (NFix (eqpN L) Fr) := finite_NFix_eqpN Fr hFr
  let c : ModGL .E6 L →* ModGL .E6 L := (MulAut.conj g0).toMonoidHom
  have hc : Function.Injective c := (MulAut.conj g0).injective
  have hc_apply : ∀ x, c x = g0 * x * g0⁻¹ := fun x => rfl
  let X : Subgroup (ModGL .E6 L) := (NFix (eqpN L) Fr).map c
  have hXfin : Finite X :=
    Finite.of_surjective (c.subgroupMap _) (c.subgroupMap_surjective _)
  haveI : Finite X := hXfin
  have hXC : X ≤ adjointGroup .E6 L := by
    rintro _ ⟨x, hx, rfl⟩
    exact mul_mem (mul_mem hg0C (monomialSubgroup_le_adjointGroup' hx.1)) (inv_mem hg0C)
  have hXF : ∀ x ∈ X, Units.map (entrywiseHom Fr) x = x := by
    rintro _ ⟨x, hx, rfl⟩
    have hxfix : negPhi Fr (eqpN L) x = x := hx.2
    rw [negPhi_apply] at hxfix
    rw [hc_apply, map_mul, map_mul, map_inv, hg0]
    calc g0 * eqpN L * Units.map (entrywiseHom Fr) x * (g0 * eqpN L)⁻¹
        = g0 * (eqpN L * Units.map (entrywiseHom Fr) x * (eqpN L)⁻¹) * g0⁻¹ := by group
      _ = g0 * x * g0⁻¹ := by rw [hxfix]
  have hrel := relIndex_dvd_E6_of_not_three_dvd K h3 L Fr hFr X hXC hXF
  let ι' : adjointGroup .E6 K →* ModGL .E6 L :=
    (baseChangeGL (algebraMap K L)).comp (adjointGroup .E6 K).subtype
  have hrange : ι'.range = (adjointGroup .E6 K).map (baseChangeGL (algebraMap K L)) := by
    change ((baseChangeGL (algebraMap K L)).comp (adjointGroup .E6 K).subtype).range = _
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hι' : Function.Injective ι' :=
    (baseChangeGL_injective (algebraMap K L)).comp (Subgroup.subtype_injective _)
  have hr : ((adjointGroup .E6 K).map (baseChangeGL (algebraMap K L))).relIndex X = 1 :=
    Nat.dvd_one.1 hrel
  have hXr : X ≤ ι'.range := by
    rw [hrange]
    exact Subgroup.relIndex_eq_one.1 hr
  let φ : NFix (eqpN L) Fr →* ModGL .E6 L := c.comp (NFix (eqpN L) Fr).subtype
  have hφ : ∀ x, φ x ∈ ι'.range := fun x => hXr ⟨x, x.2, rfl⟩
  let e : adjointGroup .E6 K ≃* ι'.range := MonoidHom.ofInjective hι'
  let ψ : NFix (eqpN L) Fr →* adjointGroup .E6 K :=
    (e.symm : ι'.range ≃* adjointGroup .E6 K).toMonoidHom.comp (φ.codRestrict ι'.range hφ)
  have hψ_inj : Function.Injective ψ := by
    intro x y hxy
    have h1 := e.symm.injective hxy
    exact Subtype.ext (hc (Subtype.ext_iff.1 h1))
  have hψ_bc : ∀ y : NFix (eqpN L) Fr,
      baseChangeGL (algebraMap K L) ((ψ y : adjointGroup .E6 K) : ModGL .E6 K) =
        g0 * (y : ModGL .E6 L) * g0⁻¹ := by
    intro y
    change ι' (ψ y) = g0 * (y : ModGL .E6 L) * g0⁻¹
    rw [← MonoidHom.ofInjective_apply hι' (x := ψ y)]
    exact congrArg Subtype.val (MulEquiv.apply_symm_apply e (φ.codRestrict ι'.range hφ y))
  have hψ_range : ∀ x : adjointGroup .E6 K,
      g0⁻¹ * baseChangeGL (algebraMap K L) (x : ModGL .E6 K) * g0 ∈ monomialSubgroup .E6 L →
        x ∈ ψ.range := by
    intro x hx
    have hfix := negPhi_conj_baseChangeGL Fr hFr hg0 (x : ModGL .E6 K)
    let y : NFix (eqpN L) Fr :=
      ⟨g0⁻¹ * baseChangeGL (algebraMap K L) (x : ModGL .E6 K) * g0, hx, hfix⟩
    refine ⟨y, ?_⟩
    apply Subtype.ext
    apply baseChangeGL_injective (algebraMap K L)
    rw [hψ_bc y]
    change g0 * (g0⁻¹ * baseChangeGL (algebraMap K L) (x : ModGL .E6 K) * g0) * g0⁻¹ =
      baseChangeGL (algebraMap K L) (x : ModGL .E6 K)
    group
  exact ⟨ψ, hψ_inj, hψ_bc, hψ_range⟩

private theorem padicValNat_three_card_NFix (h3 : 3 ∣ Nat.card K + 1) :
    padicValNat 3 ((Nat.card K + 1) ^ 4 * (Nat.card K - 1) ^ 2 * 1152) =
      4 * padicValNat 3 (Nat.card K + 1) + 2 := by
  have hq : 1 < Nat.card K := Finite.one_lt_card
  have hndvd : ¬ 3 ∣ Nat.card K - 1 := by
    rintro ⟨b, hb⟩
    obtain ⟨a, ha⟩ := h3
    omega
  have h1152 : padicValNat 3 1152 = 2 := by
    have h : (1152 : ℕ) = 3 ^ 2 * 128 := by norm_num
    have hm : padicValNat 3 (3 ^ 2 * 128) = padicValNat 3 (3 ^ 2) + padicValNat 3 128 :=
      padicValNat.mul (pow_ne_zero 2 (by norm_num)) (by norm_num)
    rw [h, hm, padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd (by norm_num)]
  have hpow1 : padicValNat 3 ((Nat.card K + 1) ^ 4) =
      4 * padicValNat 3 (Nat.card K + 1) :=
    padicValNat.pow (Nat.card K + 1) 4
  have hpow2 : padicValNat 3 ((Nat.card K - 1) ^ 2) =
      2 * padicValNat 3 (Nat.card K - 1) :=
    padicValNat.pow (Nat.card K - 1) 2
  have hz : padicValNat 3 (Nat.card K - 1) = 0 := padicValNat.eq_zero_of_not_dvd hndvd
  have hm1 : padicValNat 3 ((Nat.card K + 1) ^ 4 * (Nat.card K - 1) ^ 2 * 1152) =
      padicValNat 3 ((Nat.card K + 1) ^ 4 * (Nat.card K - 1) ^ 2) + padicValNat 3 1152 :=
    padicValNat.mul
      (mul_ne_zero (pow_ne_zero _ (by omega : Nat.card K + 1 ≠ 0))
        (pow_ne_zero _ (by omega : Nat.card K - 1 ≠ 0))) (by norm_num)
  have hm2 : padicValNat 3 ((Nat.card K + 1) ^ 4 * (Nat.card K - 1) ^ 2) =
      padicValNat 3 ((Nat.card K + 1) ^ 4) + padicValNat 3 ((Nat.card K - 1) ^ 2) :=
    padicValNat.mul (pow_ne_zero _ (by omega : Nat.card K + 1 ≠ 0))
      (pow_ne_zero _ (by omega : Nat.card K - 1 ≠ 0))
  rw [hm1, hm2, hpow1, hpow2, hz, h1152]

theorem exists_sylow_le_nfixEmb_range [IsAlgClosure K L]
    (h3 : 3 ∣ Nat.card K + 1) (Fr : L →+* L)
    (hFr : ∀ c, Fr c = c ^ Nat.card K) (ι : NFix (eqpN L) Fr →* adjointGroup .E6 K)
    (hι : Function.Injective ι) :
    ∃ P : Sylow 3 (adjointGroup .E6 K), (P : Subgroup (adjointGroup .E6 K)) ≤ ι.range := by
  haveI := generated_group_finite .E6 K
  refine CFSG.HardMathSupport.Curtis.UnitaryLevi.exists_sylow_three_le_of_factorization_eq
    ι.range ?_
  rw [← Nat.card_congr (MonoidHom.ofInjective hι).toEquiv, card_NFix_eqpN Fr hFr,
    CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_E6,
    Nat.factorization_def _ Nat.prime_three]
  rw [Nat.factorization_def _ Nat.prime_three]
  rw [padicValNat_three_ordE6_neg (q := Nat.card K) Finite.one_lt_card h3]
  exact padicValNat_three_card_NFix h3

end Certs

end CFSG.StandardType.ExcFrames.E6QPlusThree
