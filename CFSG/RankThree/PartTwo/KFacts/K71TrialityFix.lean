module

public import CFSG.RankThree.PartTwo.KFacts.K71D4G2Group
public import CFSG.RankThree.PartTwo.KFacts.K71Basic
import CFSG.LieType.Chevalley.TrialityExactFiniteOrder
public import CFSG.LieType.Chevalley.EvenCartanRootDiagonals
public import CFSG.LieType.Chevalley.TwistedE6NormalFormActors

public noncomputable section

namespace CFSG.RankThree.PartTwo.KFacts

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

variable {K : Type} [Field K]

theorem entrywiseFixedGroup_D4_eq_fixedFieldImage [Finite K] (hK : ringChar K = 2)
    (σ : K ≃+* K) :
    entrywiseFixedGroup TwistTag.D4.tag σ = fixedFieldImage TwistTag.D4.tag σ := by
  obtain ⟨-, -, -, hJΓ, hΓ, -⟩ :=
    Chevalley_coordinate_field_fixed_normal_subgroup TwistTag.D4.tag K σ
  have hT := (even_power_two_Cartan_root_diagonals_inner TwistTag.D4.tag
    (Or.inr (Or.inr (Or.inl rfl))) K hK).2.2.2 σ
  refine le_antisymm (fun g hg => ?_) hJΓ
  have hg' : g ∈ (entrywiseFixedGroup TwistTag.D4.tag σ : Set (ModGL TwistTag.D4.tag K)) := hg
  rw [hΓ] at hg'
  obtain ⟨h, hh, j, hj, rfl⟩ := Set.mem_mul.1 hg'
  refine mul_mem ?_ hj
  have hh' : h ∈ torusGroup TwistTag.D4.tag K ⊓
      (Units.map (entrywiseHom σ.toRingHom)).eqLocus (MonoidHom.id _) := ⟨hh.1, hh.2.2⟩
  rw [hT] at hh'
  obtain ⟨t, ht, rfl⟩ := hh'
  have hle : torusGroup TwistTag.D4.tag (fixSubfield σ) ≤
      adjointGroup TwistTag.D4.tag (fixSubfield σ) :=
    (Subgroup.closure_le _).2 fun _ ⟨q, hq⟩ => hq ▸ torusElt_mem_adjointGroup q.1 q.2
  exact ⟨t, hle ht, rfl⟩

section Fix

variable (σ : K ≃+* K)

@[expose] def trialityFixImage : Subgroup (ModGL TwistTag.D4.tag K) :=
  (twistedFixedGroup TwistTag.D4 (fixSubfield σ) (RingHom.id _)).map
    (baseChangeGL (fixSubfield σ).subtype)

theorem baseChangeGL_g2OrbitXUnit {k : Type} [Field k] (ι : k →+* K) (j : Fin Tag.G2.rank)
    (c : k) : baseChangeGL ι (g2OrbitXUnit k j c) = g2OrbitXUnit K j (ι c) := by
  rw [g2OrbitXUnit, map_list_prod, List.map_map, g2OrbitXUnit]
  refine congrArg List.prod (List.map_congr_left fun i _ => ?_)
  rw [Function.comp_apply, baseChangeGL_xUnit]

theorem baseChangeGL_g2OrbitYUnit {k : Type} [Field k] (ι : k →+* K) (j : Fin Tag.G2.rank)
    (c : k) : baseChangeGL ι (g2OrbitYUnit k j c) = g2OrbitYUnit K j (ι c) := by
  rw [g2OrbitYUnit, map_list_prod, List.map_map, g2OrbitYUnit]
  refine congrArg List.prod (List.map_congr_left fun i _ => ?_)
  rw [Function.comp_apply, baseChangeGL_yUnit]

variable {σ} in
theorem ringHom_pow_apply_of_fixed {c : K} (hc : σ c = c) (n : ℕ) :
    (σ.toRingHom ^ n) c = c := by
  rw [RingHom.coe_pow]
  exact Function.iterate_fixed hc n

variable {σ} in
theorem mem_orbitField_of_fixed {c : K} (hc : σ c = c) (a : Fin TwistTag.D4.foldedTag.rank) :
    c ∈ orbitField TwistTag.D4 K σ.toRingHom a :=
  mem_orbitField.2 (ringHom_pow_apply_of_fixed hc _)

variable {σ} in
theorem g2OrbitXUnit_eq_orbitX_of_fixed {c : K} (hc : σ c = c) (j : Fin Tag.G2.rank) :
    g2OrbitXUnit K j c = (orbitX TwistTag.D4 K σ.toRingHom (g2FoldedIndex j)
      ⟨c, mem_orbitField_of_fixed hc _⟩ : ModGL TwistTag.D4.tag K) := by
  rw [coe_orbitX, g2OrbitXUnit, TwistTag.orbitWord_eq_map_range, List.map_map]
  refine congrArg List.prod (List.map_congr_left fun k _ => ?_)
  rw [Function.comp_apply, ringHom_pow_apply_of_fixed hc]

variable {σ} in
theorem g2OrbitYUnit_eq_orbitY_of_fixed {c : K} (hc : σ c = c) (j : Fin Tag.G2.rank) :
    g2OrbitYUnit K j c = (orbitY TwistTag.D4 K σ.toRingHom (g2FoldedIndex j)
      ⟨c, mem_orbitField_of_fixed hc _⟩ : ModGL TwistTag.D4.tag K) := by
  rw [coe_orbitY, g2OrbitYUnit, TwistTag.orbitWord_eq_map_range, List.map_map]
  refine congrArg List.prod (List.map_congr_left fun k _ => ?_)
  rw [Function.comp_apply, ringHom_pow_apply_of_fixed hc]

theorem trialityFixImage_le :
    trialityFixImage σ ≤ graphFixedRootGroup TwistTag.D4 K σ.toRingHom := by
  rw [trialityFixImage, Subgroup.map_le_iff_le_comap, d4_twistedFixedGroup_id_eq_closure,
    Subgroup.closure_le]
  rintro _ ⟨j, c, rfl | rfl⟩
  · rw [SetLike.mem_coe, Subgroup.mem_comap, baseChangeGL_g2OrbitXUnit, fixSubfield_subtype_apply,
      g2OrbitXUnit_eq_orbitX_of_fixed (σ := σ) c.2]
    exact le_sup_left (a := graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom)
      (orbitX_mem_graphFixedPosUnipotent _ _ _ _)
  · rw [SetLike.mem_coe, Subgroup.mem_comap, baseChangeGL_g2OrbitYUnit, fixSubfield_subtype_apply,
      g2OrbitYUnit_eq_orbitY_of_fixed (σ := σ) c.2]
    exact le_sup_right (a := graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom)
      (orbitY_mem_graphFixedNegUnipotent _ _ _ _)

theorem comp_fixSubfield_subtype :
    σ.toRingHom.comp (fixSubfield σ).subtype = (fixSubfield σ).subtype :=
  RingHom.ext fun c => c.2

theorem units_map_entrywiseHom_baseChangeGL_fixSubfield {τ : Tag} (g : ModGL τ (fixSubfield σ)) :
    Units.map (entrywiseHom σ.toRingHom) (baseChangeGL (fixSubfield σ).subtype g) =
      baseChangeGL (fixSubfield σ).subtype g := by
  change baseChangeGL σ.toRingHom (baseChangeGL (fixSubfield σ).subtype g) = _
  rw [baseChangeGL_baseChangeGL, comp_fixSubfield_subtype]

theorem fieldActor_eq_self_iff [Finite K] (hK : ringChar K = 2)
    (g : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :
    fieldActor σ σ g = g ↔ (g : ModGL TwistTag.D4.tag K) ∈ trialityFixImage σ := by
  constructor
  · intro hg
    have hfix : Units.map (entrywiseHom σ.toRingHom) (g : ModGL TwistTag.D4.tag K) = g := by
      rw [← coe_fieldActor, hg]
    have hgΓ := graphFixedRootGroup_le TwistTag.D4 K σ.toRingHom g.2
    have hP := ((mem_twistedFixedGroup_iff_twistHom TwistTag.D4 K σ.toRingHom).1 hgΓ).2
    rw [twistHom_apply, hfix] at hP
    have hE : (g : ModGL TwistTag.D4.tag K) ∈ entrywiseFixedGroup TwistTag.D4.tag σ :=
      ⟨hgΓ.1, hfix⟩
    rw [entrywiseFixedGroup_D4_eq_fixedFieldImage hK] at hE
    obtain ⟨g', hg', hgg'⟩ := hE
    refine ⟨g', d4_mem_twistedFixedGroup_id_iff.2 ⟨hg', ?_⟩, hgg'⟩
    have h1 : baseChangeGL (fixSubfield σ).subtype
        (diagramMap TwistTag.D4 (fixSubfield σ) * g' * (diagramMap TwistTag.D4 (fixSubfield σ))⁻¹) =
        baseChangeGL (fixSubfield σ).subtype g' := by
      rw [map_mul, map_mul, map_inv, baseChangeGL_diagramMap, hgg']
      exact hP
    have h2 := baseChangeGL_injective (fixSubfield σ).subtype h1
    set P := diagramMap TwistTag.D4 (fixSubfield σ)
    calc P * g' = P * g' * P⁻¹ * P := by group
      _ = g' * P := by rw [h2]
  · rintro ⟨g', -, hgg'⟩
    refine Subtype.ext ?_
    rw [coe_fieldActor, ← hgg', units_map_entrywiseHom_baseChangeGL_fixSubfield]

@[expose] def trialityFixIncl :
    twistedFixedGroup TwistTag.D4 (fixSubfield σ) (RingHom.id _) →*
      graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
  ((baseChangeGL (fixSubfield σ).subtype).comp
    (twistedFixedGroup TwistTag.D4 (fixSubfield σ) (RingHom.id _)).subtype).codRestrict _
      fun g => trialityFixImage_le σ ⟨g, g.2, rfl⟩

theorem coe_trialityFixIncl (g : twistedFixedGroup TwistTag.D4 (fixSubfield σ) (RingHom.id _)) :
    (trialityFixIncl σ g : ModGL TwistTag.D4.tag K) =
      baseChangeGL (fixSubfield σ).subtype (g : ModGL TwistTag.D4.tag (fixSubfield σ)) :=
  rfl

theorem trialityFixIncl_injective : Function.Injective (trialityFixIncl σ) := fun _ _ h =>
  Subtype.ext (baseChangeGL_injective (fixSubfield σ).subtype (congrArg Subtype.val h))

theorem mem_range_trialityFixIncl_iff [Finite K] (hK : ringChar K = 2)
    (g : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :
    g ∈ (trialityFixIncl σ).range ↔ fieldActor σ σ g = g := by
  rw [fieldActor_eq_self_iff σ hK]
  constructor
  · rintro ⟨g', rfl⟩
    exact ⟨g', g'.2, rfl⟩
  · rintro ⟨g', hg', hgg'⟩
    exact ⟨⟨g', hg'⟩, Subtype.ext hgg'⟩

theorem two_eq_zero_fixSubfield (hK : ringChar K = 2) : (2 : fixSubfield σ) = 0 := by
  have : CharP K 2 := ringChar.of_eq hK
  have h2 : (2 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 2
  apply (fixSubfield σ).subtype.injective
  rw [map_ofNat, map_zero, h2]

@[expose] def trialityG2Incl (hK : ringChar K = 2) :
    adjointGroup Tag.G2 (fixSubfield σ) →* graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
  (trialityFixIncl σ).comp (d4FixedG2Equiv (fixSubfield σ) (two_eq_zero_fixSubfield σ hK)).symm

theorem trialityG2Incl_injective (hK : ringChar K = 2) :
    Function.Injective (trialityG2Incl σ hK) :=
  (trialityFixIncl_injective σ).comp (MulEquiv.injective _)

theorem mem_range_trialityG2Incl_iff [Finite K] (hK : ringChar K = 2)
    (g : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :
    g ∈ (trialityG2Incl σ hK).range ↔ fieldActor σ σ g = g := by
  rw [← mem_range_trialityFixIncl_iff σ hK]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨_, rfl⟩
  · rintro ⟨y, rfl⟩
    refine ⟨d4FixedG2Equiv (fixSubfield σ) (two_eq_zero_fixSubfield σ hK) y, ?_⟩
    change trialityFixIncl σ ((d4FixedG2Equiv _ _).symm (d4FixedG2Equiv _ _ y)) = _
    rw [MulEquiv.symm_apply_apply]

theorem nonempty_fixedPoints_fieldActor_mulEquiv_g2 [Finite K] (hK : ringChar K = 2) :
    Nonempty ((fieldActor (t := TwistTag.D4) σ σ).toMonoidHom.eqLocus (MonoidHom.id _) ≃*
      adjointGroup Tag.G2 (fixSubfield σ)) := by
  have hrange : (trialityG2Incl σ hK).range =
      (fieldActor (t := TwistTag.D4) σ σ).toMonoidHom.eqLocus (MonoidHom.id _) := by
    ext g
    rw [mem_range_trialityG2Incl_iff σ hK]
    rfl
  exact ⟨(MulEquiv.subgroupCongr hrange).symm.trans
    (MonoidHom.ofInjective (trialityG2Incl_injective σ hK)).symm⟩

end Fix

section Bar

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem nonempty_barCentralizer_mulEquiv_g2_of_conj_fieldActor [Finite K]
    (hK : ringChar K = 2) {σ : K ≃+* K}
    (e : L ⧸ aschbacherSolvableCore 3 L ≃* graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
    {a : G} (ha : a ∈ Subgroup.normalizer (L : Set G))
    (β : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (hα : inducedAutHom L e ⟨a, ha⟩ = β * fieldActor σ σ * β⁻¹ ∨
      inducedAutHom L e ⟨a, ha⟩ = β * (fieldActor σ σ)⁻¹ * β⁻¹) :
    Nonempty (Sec8.barCentralizer (Subgroup.zpowers a) L ≃*
      adjointGroup Tag.G2 (fixSubfield σ)) := by
  refine nonempty_barCentralizer_mulEquiv ha e (β.toMonoidHom.comp (trialityG2Incl σ hK))
    (β.injective.comp (trialityG2Incl_injective σ hK)) fun z => ?_
  have hfix : ∀ y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      (fieldActor (t := TwistTag.D4) σ σ)⁻¹ y = y ↔ fieldActor σ σ y = y := fun y => by
    constructor
    · intro h
      conv_lhs => rw [← h]
      exact MulEquiv.apply_symm_apply _ y
    · intro h
      conv_lhs => rw [← h]
      exact MulEquiv.symm_apply_apply _ y
  have hz : z ∈ (β.toMonoidHom.comp (trialityG2Incl σ hK)).range ↔
      fieldActor (t := TwistTag.D4) σ σ (β⁻¹ z) = β⁻¹ z := by
    rw [← mem_range_trialityG2Incl_iff σ hK]
    constructor
    · rintro ⟨x, rfl⟩
      refine ⟨x, ?_⟩
      change trialityG2Incl σ hK x = β⁻¹ (β (trialityG2Incl σ hK x))
      rw [← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply]
    · rintro ⟨x, hx⟩
      refine ⟨x, ?_⟩
      change β (trialityG2Incl σ hK x) = z
      rw [hx, ← MulAut.mul_apply, mul_inv_cancel, MulAut.one_apply]
  have hinv : ∀ y, β⁻¹ (β y) = y := fun y => by
    rw [← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply]
  have hinv' : ∀ y, β (β⁻¹ y) = y := fun y => by
    rw [← MulAut.mul_apply, mul_inv_cancel, MulAut.one_apply]
  have hβ : ∀ φ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
      (β * φ * β⁻¹) z = z ↔ φ (β⁻¹ z) = β⁻¹ z := fun φ => by
    rw [MulAut.mul_apply, MulAut.mul_apply]
    constructor
    · intro h
      calc φ (β⁻¹ z) = β⁻¹ (β (φ (β⁻¹ z))) := (hinv _).symm
        _ = β⁻¹ z := by rw [h]
    · intro h
      rw [h, hinv']
  rw [hz]
  rcases hα with hα | hα
  · rw [hα, hβ]
  · rw [hα, hβ, hfix]

theorem card_fixSubfield_of_cube {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 3)
    {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) : Nat.card (fixSubfield σ) = 2 ^ f := by
  have hσ' : ∀ c, σ.toRingHom c = c ^ ((2 ^ f) ^ 1) := fun c => by rw [pow_one]; exact hσ c
  have h := card_orbitField_D4_orientation Nat.prime_two hf hK (Or.inl rfl) hσ'
    ⟨1, by decide⟩
  rw [show (TwistTag.D4.orbit ⟨1, by decide⟩).card = 1 by decide, pow_one] at h
  rw [← h]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun c => ?_)
  rw [mem_orbitField, show (TwistTag.D4.orbit ⟨1, by decide⟩).card = 1 by decide, pow_one]
  rfl

theorem isoGTwoEven_barCentralizer_of_conj_fieldActor {f : ℕ} (hf : 1 ≤ f) [Finite K]
    (hK : Nat.card K = (2 ^ f) ^ 3) {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f)
    (e : L ⧸ aschbacherSolvableCore 3 L ≃* graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
    {a : G} (ha : a ∈ Subgroup.normalizer (L : Set G))
    (β : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (hα : inducedAutHom L e ⟨a, ha⟩ = β * fieldActor σ σ * β⁻¹ ∨
      inducedAutHom L e ⟨a, ha⟩ = β * (fieldActor σ σ)⁻¹ * β⁻¹) :
    Sec8.IsoGTwoEven (Sec8.barCentralizer (Subgroup.zpowers a) L) f := by
  have hK3 : Nat.card K = 2 ^ (3 * f) := by rw [hK, ← pow_mul, mul_comm]
  have : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (by omega) hK3
  have hK2 : ringChar K = 2 := ringChar.eq K 2
  obtain ⟨ψ⟩ := nonempty_barCentralizer_mulEquiv_g2_of_conj_fieldActor hK2 e ha β hα
  exact ⟨fixSubfield σ, inferInstance, inferInstance, card_fixSubfield_of_cube hf hK hσ, ⟨ψ⟩⟩

end Bar

end CFSG.RankThree.PartTwo.KFacts
