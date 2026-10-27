module

public import CFSG.RankThree.PartTwo.Sec11.Item1113
public import CFSG.RankThree.PartTwo.KFacts.K71bRigidity

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.KFacts CFSG.GorensteinWalter
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ClassicalGroups.UnitaryFlag

@[expose] def IsFieldCentClassical (X : Type) [Group X] : Prop :=
  (∃ (K : Type) (_ : Field K) (_ : Finite K), Nonempty (X ≃* PSL2 K)) ∨
    (∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K % 3 = 2 ∧
      Nonempty (X ≃* projectiveSL 3 K)) ∨
    ∃ (p f : ℕ) (K : Type) (_ : Field K) (h : UnitaryFieldData p f K), p ^ f % 3 = 1 ∧
      2 < p ^ f ∧ Nonempty (X ≃* unitaryPSU h 3)

section Transport

variable {X X' : Type*} [Group X] [Group X']

theorem fieldCent_nonempty_eqLocus_congr (e : X ≃* X') (α : MulAut X) :
    Nonempty (α.toMonoidHom.eqLocus (MonoidHom.id X) ≃*
      (MulAut.congr e α).toMonoidHom.eqLocus (MonoidHom.id X')) := by
  have hmap : (α.toMonoidHom.eqLocus (MonoidHom.id X)).map e.toMonoidHom =
      (MulAut.congr e α).toMonoidHom.eqLocus (MonoidHom.id X') := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hy' : α y = y := hy
      show e (α (e.symm (e y))) = e y
      rw [MulEquiv.symm_apply_apply, hy']
    · intro hz
      have hz' : e (α (e.symm z)) = z := hz
      refine ⟨e.symm z, ?_, e.apply_symm_apply z⟩
      show α (e.symm z) = e.symm z
      apply e.injective
      rw [MulEquiv.apply_symm_apply]
      exact hz'
  exact ⟨(e.subgroupMap _).trans (MulEquiv.subgroupCongr hmap)⟩

theorem fieldCent_not_isSolvable {Q : Type*} [Group Q] (hQ : IsQuasisimple Q) :
    ¬ Group.IsSolvable Q := by
  obtain ⟨-, hs, a, b, hab⟩ := hQ
  intro hsol
  have : Group.IsSolvable (Q ⧸ Subgroup.center Q) := inferInstance
  exact hab ((IsSimpleGroup.comm_iff_isSolvable).mpr this a b)

theorem fieldCent_isSolvable_psl2 {F : Type*} [Field F] [Finite F] (hF : Nat.card F ≤ 3) :
    Group.IsSolvable (PSL2 F) := by
  have h1 : 1 < Nat.card F := Finite.one_lt_card
  have : Group.IsSolvable (GL (Fin 2) F) :=
    CFSG.ComponentClassification.CatalogueBGeneralLinear.generalLinear_two_small_solvable F
      (by omega)
  have : Group.IsSolvable (Matrix.SpecialLinearGroup (Fin 2) F) :=
    Group.isSolvable_of_isSolvable_injective Matrix.SpecialLinearGroup.toGL_injective
  infer_instance

end Transport

section Models

variable {X : Type} [Group X]

theorem fieldCent_facts_psl2 {K : Type} [Field K] [Finite K] (e : X ≃* PSL2 K) {α : MulAut X}
    (hα3 : α ^ 3 = 1) (hout : ¬ IsInnerAut α) :
    ((IsQuasisimple (α.toMonoidHom.eqLocus (MonoidHom.id X)) ∧
        Subgroup.center (α.toMonoidHom.eqLocus (MonoidHom.id X)) = ⊥) ∨
      Group.IsSolvable (α.toMonoidHom.eqLocus (MonoidHom.id X))) ∧
    ∀ β : MulAut X, (∀ z, α z = z → β z = z) → β ∈ Subgroup.zpowers α := by
  have hα'3 : MulAut.congr e α ^ 3 = 1 := by rw [← map_pow, hα3, map_one]
  have hα'out : ¬ IsInnerAut (MulAut.congr e α) := by rwa [isInnerAut_congr]
  refine ⟨?_, fun β hβ => mem_zpowers_of_congr e
    (mem_zpowers_of_fixes_psl2' hα'3 hα'out (fixes_congr e hβ))⟩
  obtain ⟨σ, hσ3, ⟨eC⟩⟩ := exists_eqLocus_mulEquiv_psl2 hα'3 hα'out
  have hcard := GH74.GLS.IVK.fixedField_card_pow σ
  rw [hσ3] at hcard
  by_cases h4 : 4 ≤ Nat.card (GH74.GLS.IVK.fixedField σ)
  · obtain ⟨hZ, hQ, -, -⟩ := fixedPoints_facts_of_mulEquiv_psl2 e h4 hcard.symm hα3 hout
    exact Or.inl ⟨hQ, hZ⟩
  · have : Group.IsSolvable (PSL2 (GH74.GLS.IVK.fixedField σ)) :=
      fieldCent_isSolvable_psl2 (by omega)
    obtain ⟨f⟩ := fieldCent_nonempty_eqLocus_congr e α
    exact Or.inr (Group.isSolvable_of_isSolvable_injective (f := (f.trans eC).toMonoidHom)
      (f.trans eC).injective)

theorem fieldCent_facts_psl3 {K : Type} [Field K] [Finite K] (hK : Nat.card K % 3 = 2)
    (e : X ≃* projectiveSL 3 K) {α : MulAut X} (hα3 : α ^ 3 = 1) (hout : ¬ IsInnerAut α) :
    ((IsQuasisimple (α.toMonoidHom.eqLocus (MonoidHom.id X)) ∧
        Subgroup.center (α.toMonoidHom.eqLocus (MonoidHom.id X)) = ⊥) ∨
      Group.IsSolvable (α.toMonoidHom.eqLocus (MonoidHom.id X))) ∧
    ∀ β : MulAut X, (∀ z, α z = z → β z = z) → β ∈ Subgroup.zpowers α := by
  obtain ⟨φ⟩ := nonempty_projSL_mulEquiv 3 K
  obtain ⟨hZ, hQ⟩ := fixedPoints_facts_of_mulEquiv_projSL hK (e.trans φ.symm) hα3 hout
  refine ⟨Or.inl ⟨hQ, hZ⟩, fun β hβ => ?_⟩
  have hα'3 : MulAut.congr e α ^ 3 = 1 := by rw [← map_pow, hα3, map_one]
  have hD : MulAut.congr e α ∉ linearAutGroup 3 K := fun hD =>
    hout ((isInnerAut_congr e α).mp (isInnerAut_of_mem_linearAutGroup hK hD))
  exact mem_zpowers_of_congr e
    (mem_zpowers_of_fixes_projectiveSL le_rfl hα'3 hD (fixes_congr e hβ))

theorem fieldCent_facts_psu3 {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)
    (hq : p ^ f % 3 = 1) (hq2 : 2 < p ^ f) (e : X ≃* unitaryPSU h 3) {α : MulAut X}
    (hα3 : α ^ 3 = 1) (hout : ¬ IsInnerAut α) :
    ((IsQuasisimple (α.toMonoidHom.eqLocus (MonoidHom.id X)) ∧
        Subgroup.center (α.toMonoidHom.eqLocus (MonoidHom.id X)) = ⊥) ∨
      Group.IsSolvable (α.toMonoidHom.eqLocus (MonoidHom.id X))) ∧
    ∀ β : MulAut X, (∀ z, α z = z → β z = z) → β ∈ Subgroup.zpowers α := by
  obtain ⟨hZ, hQ⟩ := fixedPoints_facts_of_mulEquiv_unitaryPSU h hq hq2 e hα3 hout
  refine ⟨Or.inl ⟨hQ, hZ⟩, fun β hβ => ?_⟩
  have hα'3 : MulAut.congr e α ^ 3 = 1 := by rw [← map_pow, hα3, map_one]
  have hD : MulAut.congr e α ∉ (psuConj h).range := fun hD =>
    hout ((isInnerAut_congr e α).mp (isInnerAut_of_mem_psuConj_range h hq hD))
  obtain ⟨σ, hσ, -⟩ := unitary_order_three_field_descent hq2 (MulAut.congr e α) hα'3 hD
  obtain ⟨f₀, hf, -, -⟩ := exists_card_fixedField_of_orderOf_eq_three h hσ
  have hq₀ : p ^ (f / 3) ≠ 2 := by
    rw [hf, Nat.mul_div_cancel_left f₀ (by norm_num)]
    intro h2
    have hpow : p ^ f = (p ^ f₀) ^ 3 := by rw [hf, ← pow_mul, mul_comm]
    rw [hpow, h2] at hq
    norm_num at hq
  exact mem_zpowers_of_congr e
    (mem_zpowers_of_fixes_unitaryPSU h hq2 hq₀ hα'3 hD (fixes_congr e hβ))

theorem fieldCent_facts_of_classical (hX : IsFieldCentClassical X) {α : MulAut X}
    (hα3 : α ^ 3 = 1) (hout : ¬ IsInnerAut α) :
    ((IsQuasisimple (α.toMonoidHom.eqLocus (MonoidHom.id X)) ∧
        Subgroup.center (α.toMonoidHom.eqLocus (MonoidHom.id X)) = ⊥) ∨
      Group.IsSolvable (α.toMonoidHom.eqLocus (MonoidHom.id X))) ∧
    ∀ β : MulAut X, (∀ z, α z = z → β z = z) → β ∈ Subgroup.zpowers α := by
  rcases hX with ⟨K, _, _, ⟨e⟩⟩ | ⟨K, _, _, hK, ⟨e⟩⟩ | ⟨p, f, K, _, h, hq, hq2, ⟨e⟩⟩
  · exact fieldCent_facts_psl2 e hα3 hout
  · exact fieldCent_facts_psl3 hK e hα3 hout
  · exact fieldCent_facts_psu3 h hq hq2 e hα3 hout

end Models

section Generic

variable {G : Type} [Group G] [Finite G]

theorem fieldCent_map_cMap_ne_bot {Y : Subgroup G} {c : G}
    {K : Subgroup (Y ⊓ Subgroup.centralizer ({c} : Set G) : Subgroup G)}
    (hK : K ∈ thetaComponents 3 (Y ⊓ Subgroup.centralizer ({c} : Set G) : Subgroup G)) :
    K.map (cMap Y c) ≠ ⊥ := by
  intro hbot
  set ι : (Y ⊓ Subgroup.centralizer ({c} : Set G) : Subgroup G) →* Y :=
    Subgroup.inclusion inf_le_left with hι
  have hle : K.map ι ≤ aschbacherSolvableCore 3 Y := by
    rintro _ ⟨k, hk, rfl⟩
    have h1 : cMap Y c k ∈ K.map (cMap Y c) := ⟨k, hk, rfl⟩
    rw [hbot, Subgroup.mem_bot, cMap, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at h1
    exact h1
  have : Group.IsSolvable (aschbacherSolvableCore 3 Y) :=
    (solvable_prime_complement_core_characterization (H := Y) Nat.prime_three).1
  have : Group.IsSolvable (K.map ι) :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hle)
  have : Group.IsSolvable K := Group.isSolvable_of_isSolvable_injective
    (f := (K.equivMapOfInjective ι (Subgroup.inclusion_injective _)).toMonoidHom)
    (K.equivMapOfInjective ι (Subgroup.inclusion_injective _)).injective
  exact fieldCent_not_isSolvable hK.2.2 inferInstance

theorem fieldCent_false_of_isSolvable {Y K : Subgroup G} {c : G}
    (hcN : c ∈ Subgroup.normalizer (Y : Set G)) (hc3 : c ^ 3 = 1)
    (hK : K ∈ thetaComponentsIn (Y ⊓ Subgroup.centralizer ({c} : Set G)))
    (hF : Group.IsSolvable ((Sec4.thetaQuotMulAut Y
      (Sec4.compAction Y ⟨c, hcN⟩)).toMonoidHom.eqLocus
        (MonoidHom.id (Y ⧸ aschbacherSolvableCore 3 Y)))) : False := by
  obtain ⟨K', hK', -⟩ := hK
  apply fieldCent_map_cMap_ne_bot hK'
  have : Group.IsPerfect K' := hK'.1
  have : Group.IsPerfect (K'.map (cMap Y c)) := Group.IsPerfect.map _
  have hle : K'.map (cMap Y c) ≤ (cMap Y c).range := Subgroup.map_le_range _ _
  rw [range_cMap hcN hc3] at hle
  have : Group.IsSolvable (K'.map (cMap Y c)) :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hle)
  by_contra hne
  have : Nontrivial (K'.map (cMap Y c)) := (Subgroup.nontrivial_iff_ne_bot _).mpr hne
  exact Group.IsPerfect.not_isSolvable (K'.map (cMap Y c)) inferInstance

theorem fieldCent_fixes {Y K : Subgroup G} {c t : G}
    (hcN : c ∈ Subgroup.normalizer (Y : Set G)) (hc3 : c ^ 3 = 1)
    (htN : t ∈ Subgroup.normalizer (Y : Set G))
    (hQ : IsQuasisimple ((Sec4.thetaQuotMulAut Y (Sec4.compAction Y ⟨c, hcN⟩)).toMonoidHom.eqLocus
      (MonoidHom.id (Y ⧸ aschbacherSolvableCore 3 Y))))
    (hZ : Subgroup.center ((Sec4.thetaQuotMulAut Y
      (Sec4.compAction Y ⟨c, hcN⟩)).toMonoidHom.eqLocus
        (MonoidHom.id (Y ⧸ aschbacherSolvableCore 3 Y))) = ⊥)
    (hK : K ∈ thetaComponentsIn (Y ⊓ Subgroup.centralizer ({c} : Set G)))
    (htK : ∀ k ∈ K, t * k * t⁻¹ * k⁻¹ ∈ inSubgroup (aschbacherSolvableCore 3) K) :
    ∀ z, Sec4.thetaQuotMulAut Y (Sec4.compAction Y ⟨c, hcN⟩) z = z →
      Sec4.thetaQuotMulAut Y (Sec4.compAction Y ⟨t, htN⟩) z = z := by
  set α := Sec4.thetaQuotMulAut Y (Sec4.compAction Y ⟨c, hcN⟩) with hα
  set F := α.toMonoidHom.eqLocus (MonoidHom.id (Y ⧸ aschbacherSolvableCore 3 Y)) with hF
  set M := (Y ⊓ Subgroup.centralizer ({c} : Set G) : Subgroup G) with hM
  obtain ⟨K', hK', rfl⟩ := hK
  have hrange : (cMap Y c).range = F := range_cMap hcN hc3
  have hmem : ∀ m, cMap Y c m ∈ F := fun m => hrange ▸ ⟨m, rfl⟩
  set ψ : M →* F := (cMap Y c).codRestrict F hmem with hψ
  have hψs : Function.Surjective ψ := by
    rintro ⟨z, hz⟩
    rw [← hrange] at hz
    obtain ⟨m, rfl⟩ := hz
    exact ⟨m, rfl⟩
  have hsimple : IsSimpleGroup F := by
    have := hQ.2.1
    exact ((QuotientGroup.quotientMulEquivOfEq hZ).trans
      QuotientGroup.quotientBot).symm.isSimpleGroup
  have htop : K'.map ψ = ⊤ := by
    rcases (hK'.2.1.map hψs).eq_bot_or_top_of_isSimpleGroup hsimple with h | h
    · refine absurd ?_ (fieldCent_map_cMap_ne_bot hK')
      rw [Subgroup.eq_bot_iff_forall]
      rintro _ ⟨k, hk, rfl⟩
      have h1 : ψ k ∈ K'.map ψ := ⟨k, hk, rfl⟩
      rw [h, Subgroup.mem_bot] at h1
      exact congrArg Subtype.val h1
    · exact h
  set χ : K' →* F := ψ.comp K'.subtype with hχ
  have hχs : Function.Surjective χ := by
    intro z
    have hz : z ∈ K'.map ψ := htop ▸ Subgroup.mem_top z
    obtain ⟨k, hk, rfl⟩ := hz
    exact ⟨⟨k, hk⟩, rfl⟩
  have hθ : (aschbacherSolvableCore 3 K').map χ = ⊥ := by
    obtain ⟨hθs, hθc, -⟩ :=
      solvable_prime_complement_core_characterization (H := K') Nat.prime_three
    have : ((aschbacherSolvableCore 3 K').map χ).Normal :=
      (inferInstance : (aschbacherSolvableCore 3 K').Normal).map χ hχs
    exact Sec11.eq_bot_of_normal_solvable_of_isQuasisimple hQ hZ _
      (Group.isSolvable_of_surjective (χ.subgroupMap_surjective _))
  intro z hz
  obtain ⟨⟨k, hk⟩, hkz⟩ := hχs ⟨z, hz⟩
  have hkz' : ((Subgroup.inclusion inf_le_left k : Y) : Y ⧸ aschbacherSolvableCore 3 Y) = z :=
    congrArg Subtype.val hkz
  have hkG : ((k : M) : G) ∈ K'.map M.subtype := ⟨k, hk, rfl⟩
  have hc := htK _ hkG
  rw [inSubgroup_theta_map_subtype_sub K'] at hc
  obtain ⟨m, ⟨y, hy, rfl⟩, hm⟩ := hc
  have hy1 : χ y = 1 := by
    have h1 : χ y ∈ (aschbacherSolvableCore 3 K').map χ := ⟨y, hy, rfl⟩
    rw [hθ, Subgroup.mem_bot] at h1
    exact h1
  have hy1' : ((Subgroup.inclusion inf_le_left (y : M) : Y) :
      Y ⧸ aschbacherSolvableCore 3 Y) = 1 := congrArg Subtype.val hy1
  have e1 : Sec4.compAction Y ⟨t, htN⟩ (Subgroup.inclusion inf_le_left k) =
      Subgroup.inclusion inf_le_left (y : M) * Subgroup.inclusion inf_le_left k := by
    apply Subtype.ext
    change t * (k : G) * t⁻¹ = ((y : M) : G) * (k : G)
    rw [show (((y : K') : M) : G) = t * (k : G) * t⁻¹ * (k : G)⁻¹ from hm]
    group
  rw [← hkz', Sec4.thetaQuotMulAut_mk, e1, QuotientGroup.mk_mul, hy1', one_mul]

end Generic

section Core

variable {G : Type} [Group G] [Finite G]

theorem exists_mul_pow_mem_thetaQuotCentralizer_of_classical {Y K : Subgroup G} {c t : G}
    (hY : IsFieldCentClassical (Y ⧸ aschbacherSolvableCore 3 Y))
    (hout : Sec4.InducesOuterTheta c Y) (hc3 : c ^ 3 = 1)
    (hK : K ∈ thetaComponentsIn (Y ⊓ Subgroup.centralizer ({c} : Set G)))
    (htN : t ∈ Subgroup.normalizer (Y : Set G))
    (htK : ∀ k ∈ K, t * k * t⁻¹ * k⁻¹ ∈ inSubgroup (aschbacherSolvableCore 3) K) :
    ∃ i : ℕ, t * c ^ i ∈ Sec4.thetaQuotCentralizer Y := by
  obtain ⟨hcN, hαout⟩ := hout
  set α := Sec4.thetaQuotMulAut Y (Sec4.compAction Y ⟨c, hcN⟩) with hα
  set β := Sec4.thetaQuotMulAut Y (Sec4.compAction Y ⟨t, htN⟩) with hβ
  have hα3 : α ^ 3 = 1 := by
    have h1 : (⟨c, hcN⟩ : Subgroup.normalizer (Y : Set G)) ^ 3 = 1 :=
      Subtype.ext (by simpa using hc3)
    rw [hα, ← map_pow, ← map_pow, h1, map_one, map_one]
  obtain ⟨hF, hrig⟩ := fieldCent_facts_of_classical hY hα3 hαout
  rcases hF with ⟨hQ, hZ⟩ | hsol
  · obtain ⟨i, hi⟩ := exists_pow_eq_of_mem_zpowers hα3
      (hrig β (fieldCent_fixes hcN hc3 htN hQ hZ hK htK))
    refine ⟨2 * i, ?_⟩
    have hmem : t * c ^ (2 * i) ∈ Subgroup.normalizer (Y : Set G) :=
      mul_mem htN (pow_mem hcN _)
    refine ⟨⟨_, hmem⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker]
    have e4 : (⟨t * c ^ (2 * i), hmem⟩ : Subgroup.normalizer (Y : Set G)) =
        ⟨t, htN⟩ * ⟨c, hcN⟩ ^ (2 * i) := Subtype.ext (by simp)
    rw [e4, map_mul, map_pow]
    change β * α ^ (2 * i) = 1
    rw [hi, ← pow_add, show i + 2 * i = 3 * i by ring, pow_mul, hα3, one_pow]
  · exact (fieldCent_false_of_isSolvable hcN hc3 hK hsol).elim

end Core

section Covers

variable {X : Type} [Group X]

theorem isFieldCentClassical_of_mulEquiv_sl3 {K : Type} [Field K] [Finite K]
    (hK : Nat.card K % 3 = 2) (e : X ≃* Matrix.SpecialLinearGroup (Fin 3) K) :
    IsFieldCentClassical X :=
  Or.inr (Or.inl ⟨K, inferInstance, inferInstance, hK,
    ⟨e.trans (MulEquiv.ofBijective (proj 3 K) ⟨proj_three_injective hK, proj_surjective 3 K⟩)⟩⟩)

theorem isFieldCentClassical_of_mulEquiv_su3 {p f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData p f K) (hq : p ^ f % 3 = 1) (hq2 : 2 < p ^ f)
    (e : X ≃* unitarySU p f K 3) : IsFieldCentClassical X :=
  Or.inr (Or.inr ⟨p, f, K, inferInstance, h, hq, hq2,
    ⟨e.trans (MulEquiv.ofBijective (unitaryProj h 3)
      ⟨unitaryProj_three_injective h hq, unitaryProj_surjective h 3⟩)⟩⟩)

end Covers

section Main


@[expose] def FieldCentRigidVacuous : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Y K : Subgroup G) (c t : G),
    KFacts.InducesStdKind Y c .field →
    ¬ IsFieldCentClassical (Y ⧸ aschbacherSolvableCore 3 Y) → c ^ 3 = 1 →
    K ∈ thetaComponentsIn (Y ⊓ Subgroup.centralizer ({c} : Set G)) →
    IsType424 (K ⧸ aschbacherSolvableCore 3 K) →
    t ∈ Subgroup.normalizer (Y : Set G) → (∃ k : ℕ, t ^ 3 ^ k = 1) → t * c = c * t →
    (∀ k ∈ K, t * k * t⁻¹ * k⁻¹ ∈ inSubgroup (aschbacherSolvableCore 3) K) →
      ∃ i : ℕ, t * c ^ i ∈ Sec4.thetaQuotCentralizer Y

theorem fieldCentRigid_of (hvac : FieldCentRigidVacuous) : FieldCentRigid := by
  intro G _ _ Y K c t hf hc3 hK hT htN ht3 htc htK
  by_cases hY : IsFieldCentClassical (Y ⧸ aschbacherSolvableCore 3 Y)
  · exact exists_mul_pow_mem_thetaQuotCentralizer_of_classical hY
      (KFacts.InducesStdKind.inducesOuterTheta Y hf (by decide)) hc3 hK htN htK
  · exact hvac G Y K c t hf hY hc3 hK hT htN ht3 htc htK

theorem not_inducesKindTriality_field_of_pow_three {G : Type} [Group G] [Finite G] {f : ℕ}
    (hf : 1 ≤ f) {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ f) ^ 3)
    {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) (L : Subgroup G) {x : G} (hx3 : x ^ 3 = 1) :
    ¬ KFacts.InducesKindTriality σ L x .field := by
  rintro ⟨e, hx, δ, hδ1, hδ3, g, hτ⟩
  have h3 := inducedAutHom_pow_eq_one L e hx hx3
  rw [hτ, conj_pow] at h3
  have h4 : CFSG.LieType.Chevalley.fieldActor (t := CFSG.Blueprint.Chevalley.TwistTag.D4) σ δ ^ 3 =
      1 := by
    calc CFSG.LieType.Chevalley.fieldActor σ δ ^ 3 = (MulAut.conj g)⁻¹ *
          (MulAut.conj g * CFSG.LieType.Chevalley.fieldActor σ δ ^ 3 * (MulAut.conj g)⁻¹) *
            MulAut.conj g := by group
      _ = 1 := by rw [h3]; group
  have h5 : CFSG.LieType.Chevalley.fieldActor (t := CFSG.Blueprint.Chevalley.TwistTag.D4) σ
      (δ ^ 3) = 1 := by
    rw [← CFSG.LieType.Chevalley.fieldActorHom_apply, map_pow,
      CFSG.LieType.Chevalley.fieldActorHom_apply, h4]
  have h6 : δ ^ 3 = 1 := (isInnerAut_fieldActor_iff hf hK hσ).mp (h5 ▸ ⟨1, map_one _⟩)
  exact hδ1 (orderOf_eq_one_iff.mp
    (Nat.Coprime.eq_one_of_dvd hδ3 (orderOf_dvd_of_pow_eq_one h6)))

end Main

end CFSG.RankThree.PartTwo.Sec11
