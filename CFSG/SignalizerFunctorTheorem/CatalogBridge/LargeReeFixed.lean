module

public import CFSG.SignalizerFunctorTheorem.CatalogBridge.FieldGlue
public import CFSG.LieType.Ree.SmallReeOuterThreeKernel
public import CFSG.LieType.Chevalley.EvenQuadraticGraphFieldDescent
import CFSG.SignalizerFunctorTheorem.CatalogBridge.StabilizerLift
import CFSG.RankThree.SteinbergR3ESmallReeCosetDescent
import CFSG.RankThree.Chevalley.SteinbergBTCanonicalFieldCommon
import CFSG.RankThree.PartTwo.KFacts.KS14SzRee
import CFSG.LieType.Ree.LargeReeFixedGroupOddCore

public section

open CFSG.Open (signalizerFixedSubgroup)
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
open CFSG.LieType.Simplicity (titsData isSimpleGroup_quotient_center_reeFixed_F4)
open CFSG.RankThree (entrywiseFixedGroup_eq_fixedFieldImage_of_det_one)
open CFSG.RankThree.Chevalley.SteinbergBT (card_fixSubfield)
open CFSG.RankThree.PartTwo.KFacts.KS14 (center_commutator_reeFixed_tits_eq_bot)

namespace CFSG.SignalizerFunctorTheorem.CatalogBridge

section BaseChange

variable {t : ReeTag} {k K : Type} [Field k] [Finite k] [CharP k t.prime] [Field K] [Finite K]
  [CharP K t.prime]

theorem baseChange_finiteExceptionalAut
    (ι₀ : k →+* K) (u : adjointGroup t.tag k) :
    adjointBaseChangeHom t.tag ι₀ (t.finiteExceptionalAut k u) =
      t.finiteExceptionalAut K (adjointBaseChangeHom t.tag ι₀ u) := by
  have hx : ∀ (i : Fin t.tag.rank) (c : k),
      adjointBaseChangeHom t.tag ι₀ (xElement i c) = xElement i (ι₀ c) :=
    fun i c => Subtype.ext (baseChangeGL_xUnit _ i c)
  have hy : ∀ (i : Fin t.tag.rank) (c : k),
      adjointBaseChangeHom t.tag ι₀ (yElement i c) = yElement i (ι₀ c) :=
    fun i c => Subtype.ext (baseChangeGL_yUnit _ i c)
  have h := adjointGroup_hom_ext
    (f := (adjointBaseChangeHom t.tag ι₀).comp (t.finiteExceptionalAut k).toMonoidHom)
    (g := (t.finiteExceptionalAut K).toMonoidHom.comp (adjointBaseChangeHom t.tag ι₀))
    (fun i c => by
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
      rw [ReeTag.finiteExceptionalAut_xElement, hx, hx, ReeTag.finiteExceptionalAut_xElement,
        map_pow])
    (fun i c => by
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
      rw [ReeTag.finiteExceptionalAut_yElement, hy, hy, ReeTag.finiteExceptionalAut_yElement,
        map_pow])
  exact DFunLike.congr_fun h u

theorem baseChange_finiteFrobeniusAut
    (ι₀ : k →+* K) (u : adjointGroup t.tag k) :
    adjointBaseChangeHom t.tag ι₀ (t.finiteFrobeniusAut k u) =
      t.finiteFrobeniusAut K (adjointBaseChangeHom t.tag ι₀ u) := by
  refine Subtype.ext ?_
  rw [coe_adjointBaseChangeHom, ReeTag.coe_finiteFrobeniusAut, ReeTag.coe_finiteFrobeniusAut,
    coe_adjointBaseChangeHom]
  change baseChangeGL ι₀ (Units.map (entrywiseHom (frobenius k t.prime))
      (u : ModGL t.tag k)) =
    Units.map (entrywiseHom (frobenius K t.prime)) (baseChangeGL ι₀ (u : ModGL _ k))
  have hc : (frobenius K t.prime).comp ι₀ = ι₀.comp (frobenius k t.prime) :=
    RingHom.ext fun c => by simp only [RingHom.comp_apply, frobenius_def, map_pow]
  rw [units_map_entrywiseHom_eq_baseChangeGL, units_map_entrywiseHom_eq_baseChangeGL,
    baseChangeGL_baseChangeGL, baseChangeGL_baseChangeGL, hc]

theorem baseChange_finiteFrobeniusAut_pow
    (ι₀ : k →+* K) (n : ℕ) (u : adjointGroup t.tag k) :
    adjointBaseChangeHom t.tag ι₀ ((t.finiteFrobeniusAut k ^ n) u) =
      (t.finiteFrobeniusAut K ^ n) (adjointBaseChangeHom t.tag ι₀ u) := by
  induction n generalizing u with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ, MulAut.mul_apply, pow_succ, MulAut.mul_apply, ih,
      baseChange_finiteFrobeniusAut]

theorem baseChange_finiteReeAut
    (ι₀ : k →+* K) (a : ℕ) (u : adjointGroup t.tag k) :
    adjointBaseChangeHom t.tag ι₀ (t.finiteReeAut k a u) =
      t.finiteReeAut K a (adjointBaseChangeHom t.tag ι₀ u) := by
  change adjointBaseChangeHom t.tag ι₀
      ((t.finiteExceptionalAut k * t.finiteFrobeniusAut k ^ a) u) =
    (t.finiteExceptionalAut K * t.finiteFrobeniusAut K ^ a)
      (adjointBaseChangeHom t.tag ι₀ u)
  rw [MulAut.mul_apply, MulAut.mul_apply, baseChange_finiteExceptionalAut,
    baseChange_finiteFrobeniusAut_pow]

theorem finiteReeAut_eq_of_modEq
    {a b d m : ℕ} (hk : Nat.card k = t.prime ^ d)
    (hab : a = b + d * m) : t.finiteReeAut k a = t.finiteReeAut k b := by
  change t.finiteExceptionalAut k * t.finiteFrobeniusAut k ^ a =
    t.finiteExceptionalAut k * t.finiteFrobeniusAut k ^ b
  rw [hab, pow_add, pow_mul, finiteFrobeniusAut_pow_card t hk, one_pow, mul_one]

end BaseChange

theorem fixed_reeGamma_eq_map_of_det_one
    {t : ReeTag} (hdet : t.tag.cartan.transpose.det = 1)
    {K : Type} [Field K] [Finite K] [CharP K t.prime] {a b d m : ℕ} (σ : K ≃+* K)
    (hk : Nat.card (fixSubfield σ) = t.prime ^ d) (hab : a = b + d * m) :
    ((t.reeGammaFieldAut K a σ).toMonoidHom.eqLocus (MonoidHom.id _)).map
        (t.reeGamma K a).subtype =
      (t.reeGamma (fixSubfield σ) b).map (baseChangeGL (fixSubfield σ).subtype) := by
  set k := fixSubfield σ
  set ι := adjointBaseChangeHom t.tag k.subtype
  have hFab := finiteReeAut_eq_of_modEq (t := t) (k := k) hk hab
  have hJ := entrywiseFixedGroup_eq_fixedFieldImage_of_det_one hdet σ
  ext g
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx' : t.reeGammaFieldAut K a σ x = x := hx
    obtain ⟨hgC, hgF⟩ := ReeTag.mem_reeGamma.1 x.2
    have hfix : (x : ModGL t.tag K) ∈ entrywiseFixedGroup t.tag σ := by
      refine ⟨hgC, ?_⟩
      have h := congrArg (fun y : t.reeGamma K a => (y : ModGL t.tag K)) hx'
      simp only [ReeTag.coe_reeGammaFieldAut] at h
      exact h
    rw [hJ] at hfix
    obtain ⟨v, hv, hvx⟩ := hfix
    refine ⟨v, ReeTag.mem_reeGamma.2 ⟨hv, ?_⟩, hvx⟩
    apply adjointBaseChangeHom_injective t.tag k.subtype
    rw [← hFab, baseChange_finiteReeAut]
    have hιv : ι ⟨v, hv⟩ = ⟨(x : ModGL t.tag K), hgC⟩ := Subtype.ext hvx
    rw [hιv]
    exact hgF
  · rintro ⟨v, hv, rfl⟩
    obtain ⟨hvC, hvF⟩ := ReeTag.mem_reeGamma.1 hv
    have hgC : baseChangeGL k.subtype v ∈ adjointGroup t.tag K :=
      baseChangeGL_mem_adjointGroup _ hvC
    have hgΓ : baseChangeGL k.subtype v ∈ t.reeGamma K a := by
      refine ReeTag.mem_reeGamma.2 ⟨hgC, ?_⟩
      have h := baseChange_finiteReeAut k.subtype a ⟨v, hvC⟩
      rw [hFab, hvF] at h
      exact h.symm
    refine ⟨⟨_, hgΓ⟩, ?_, rfl⟩
    change t.reeGammaFieldAut K a σ ⟨_, hgΓ⟩ = ⟨_, hgΓ⟩
    refine Subtype.ext ?_
    rw [ReeTag.coe_reeGammaFieldAut]
    change Units.map (entrywiseHom σ.toRingHom) (baseChangeGL k.subtype v) =
      baseChangeGL k.subtype v
    rw [units_map_entrywiseHom_eq_baseChangeGL, baseChangeGL_baseChangeGL,
      show σ.toRingHom.comp k.subtype = k.subtype from RingHom.ext fun c => c.2]

theorem det_transpose_cartan_F4 : Tag.F4.cartan.transpose.det = 1 := by
  rw [Matrix.det_transpose, det_cartan_F4]

theorem fixed_reeGamma_F4_eq_map
    {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime]
    {a b d m : ℕ} (σ : K ≃+* K) (hk : Nat.card (fixSubfield σ) = 2 ^ d) (hab : a = b + d * m) :
    ((ReeTag.F4.reeGammaFieldAut K a σ).toMonoidHom.eqLocus (MonoidHom.id _)).map
        (ReeTag.F4.reeGamma K a).subtype =
      (ReeTag.F4.reeGamma (fixSubfield σ) b).map (baseChangeGL (fixSubfield σ).subtype) :=
  fixed_reeGamma_eq_map_of_det_one (t := ReeTag.F4) det_transpose_cartan_F4 σ hk hab

theorem isFStarSimple_reeGamma_F4
    {b : ℕ} {k : Type} [Field k] [Finite k]
    [CharP k ReeTag.F4.prime] (hk : Nat.card k = 2 ^ (2 * b + 1)) :
    McBride.Nonsolv.L514.IsFStarSimple (ReeTag.F4.reeGamma k b) := by
  set e := ReeTag.reeFixedEquivReeGamma k b
  refine (McBride.Nonsolv.L514.isFStarSimple_congr e).1 ?_
  have hZ : Subgroup.center (reeFixed ReeTag.F4 k b) = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have hz' : e z ∈ Subgroup.center (ReeTag.F4.reeGamma k b) :=
      (MulEquivClass.apply_mem_center_iff e).2 hz
    rw [ReeTag.large_Ree_fixed_group_center_trivial b k hk, Subgroup.mem_bot] at hz'
    exact Subgroup.mem_bot.2 (e.injective (hz'.trans (map_one e).symm))
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · have hk2 : Nat.card k = 2 := by simpa using hk
    set D := commutator (reeFixed ReeTag.F4 k 0)
    have : IsSimpleGroup (D ⧸ Subgroup.center D) := ((titsData k hk2).isQuasisimple hk2).2.1
    have hZD : Subgroup.center D = ⊥ := center_commutator_reeFixed_tits_eq_bot hk2
    have hs : IsSimpleGroup D :=
      ((QuotientGroup.quotientMulEquivOfEq hZD).trans QuotientGroup.quotientBot).symm.isSimpleGroup
    obtain ⟨x, hx, y, hy, hxy⟩ := (titsData k hk2).nonabelian
    exact isFStarSimple_of_derived_simple hZ hs
      ⟨⟨x, hx⟩, ⟨y, hy⟩, fun h => hxy (congrArg Subtype.val h)⟩
  · have : IsSimpleGroup (reeFixed ReeTag.F4 k b ⧸ Subgroup.center (reeFixed ReeTag.F4 k b)) :=
      isSimpleGroup_quotient_center_reeFixed_F4 b hb hk
    have hs : IsSimpleGroup (reeFixed ReeTag.F4 k b) :=
      ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.isSimpleGroup
    refine McBride.Nonsolv.L514.isFStarSimple_of_isSimpleGroup ?_
    rw [isMulCommutative_iff]
    intro hcomm
    obtain ⟨x, hx⟩ := exists_ne (1 : reeFixed ReeTag.F4 k b)
    refine hx ?_
    have hxZ : x ∈ Subgroup.center (reeFixed ReeTag.F4 k b) :=
      Subgroup.mem_center_iff.2 fun z => hcomm z x
    rwa [hZ, Subgroup.mem_bot] at hxZ

theorem largeRee_fixed_data_odd
    {a : ℕ} {K : Type} [Field K] [Finite K]
    [CharP K ReeTag.F4.prime] (hK : Nat.card K = 2 ^ (2 * a + 1)) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (σ : K ≃+* K) (hσ : orderOf σ = p) :
    ∃ b : ℕ, (2 * b + 1) * p = 2 * a + 1 ∧ Nat.card (fixSubfield σ) = 2 ^ (2 * b + 1) ∧
      ((ReeTag.F4.reeGammaFieldAut K a σ).toMonoidHom.eqLocus (MonoidHom.id _)).map
          (ReeTag.F4.reeGamma K a).subtype =
        (ReeTag.F4.reeGamma (fixSubfield σ) b).map (baseChangeGL (fixSubfield σ).subtype) := by
  obtain ⟨hpf, hcard⟩ := card_fixSubfield Nat.prime_two (by omega) hK σ
  rw [hσ] at hpf hcard
  obtain ⟨d, hd⟩ := hpf
  have hd' : (2 * a + 1) / p = d := by rw [hd, Nat.mul_div_cancel_left _ hp.pos]
  rw [hd'] at hcard
  have hdodd : Odd d := by
    have h1 : Odd (p * d) := hd ▸ odd_two_mul_add_one a
    exact (Nat.odd_mul.1 h1).2
  obtain ⟨b, hb⟩ := hdodd
  obtain ⟨m, hm⟩ := hp.odd_of_ne_two hp2
  have hab : a = b + d * m := by
    have e1 : p * d = 2 * (d * m) + d := by rw [hm]; ring
    omega
  exact ⟨b, by rw [← hb, mul_comm, ← hd], by rw [hcard, hb], fixed_reeGamma_F4_eq_map σ hcard hab⟩

theorem largeRee_fixed_data
    {a : ℕ} (_ha : 1 ≤ a) {K : Type} [Field K] [Finite K]
    [CharP K ReeTag.F4.prime] (hK : Nat.card K = 2 ^ (2 * a + 1)) {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) (σ : K ≃+* K) (hσ : orderOf σ = p) :
    ∃ b : ℕ, Nat.card (fixSubfield σ) = 2 ^ (2 * b + 1) ∧
      ((ReeTag.F4.reeGammaFieldAut K a σ).toMonoidHom.eqLocus (MonoidHom.id _)).map
          (ReeTag.F4.reeGamma K a).subtype =
        (ReeTag.F4.reeGamma (fixSubfield σ) b).map (baseChangeGL (fixSubfield σ).subtype) := by
  obtain ⟨b, -, hb, hfix⟩ := largeRee_fixed_data_odd hK hp (by omega) σ hσ
  exact ⟨b, hb, hfix⟩

theorem largeReeFixedSimple :
    ∀ (a : ℕ), 1 ≤ a → ∀ (K : Type) [Field K] [Finite K] [CharP K ReeTag.F4.prime],
      Nat.card K = 2 ^ (2 * a + 1) → ∀ p : ℕ, p.Prime → 3 < p → ∀ σ : K ≃+* K, orderOf σ = p →
        FStarSimple (signalizerFixedSubgroup (ReeTag.F4.reeGammaFieldAut K a σ)) := by
  intro a ha K _ _ _ hK p hp hp3 σ hσ
  obtain ⟨b, hkcard, hfixed⟩ := largeRee_fixed_data ha hK hp hp3 σ hσ
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
  exact (fStarSimple_iff_isFStarSimple _).2
    ((McBride.Nonsolv.L514.isFStarSimple_congr eC).2 (isFStarSimple_reeGamma_F4 hkcard))

end CFSG.SignalizerFunctorTheorem.CatalogBridge
