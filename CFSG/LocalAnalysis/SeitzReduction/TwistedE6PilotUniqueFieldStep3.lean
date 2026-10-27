module

public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotUniqueField
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotStep3

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.TwistedE6Pilot

open Subgroup CFSG.Open CFSG.EvenSmallLie CFSG.Blueprint CFSG.Blueprint.Chevalley
open CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit)
open CFSG.Quasithin (perfectCore)
open CFSG.SeitzReduction.EPilot (normalizerQuotMulAut normalizerQuotMulAut_apply)

section Generic

variable {G : Type*} [Group G] [Finite G]

theorem le_iSup_perfectCore_of_quotient_mulEquiv {M : Subgroup G} (hMp : ⁅M, M⁆ = M)
    {E : Type*} [Group E] [Finite E] (ψ : M ⧸ center M ≃* E) {ι : Type*} (T : ι → Subgroup G)
    (hTM : ∀ i, T i ≤ M)
    (hgen : ⨆ i, perfectCore (centralizer ((((T i).subgroupOf M).map
      (ψ.toMonoidHom.comp (QuotientGroup.mk' (center M))) : Subgroup E) : Set E)) = ⊤) :
    M ≤ ⨆ i, perfectCore (M ⊓ centralizer (T i : Set G)) := by
  set π := QuotientGroup.mk' (center M) with hπ
  have hgenQ : ⨆ i, perfectCore (centralizer ((((T i).subgroupOf M).map π :
      Subgroup (M ⧸ center M)) : Set (M ⧸ center M))) = ⊤ := by
    apply Subgroup.map_injective (f := ψ.toMonoidHom) ψ.injective
    rw [Subgroup.map_iSup]
    simp_rw [CFSG.Quasithin.map_perfectCore, F4Pilot.map_centralizer_mulEquiv, Subgroup.map_map]
    rw [hgen, ← MonoidHom.range_eq_map, MonoidHom.range_eq_top.2 ψ.surjective]
  have hmapTop : (⨆ i, perfectCore (centralizer (((T i).subgroupOf M : Subgroup M) :
      Set M))).map π = ⊤ := by
    rw [Subgroup.map_iSup, eq_top_iff, ← hgenQ]
    exact iSup_mono fun i => E6Pilot.perfectCore_centralizer_map_le _
  have hMperf : Group.IsPerfect M := Subgroup.isPerfect_iff.2 hMp
  have hTop := E6Pilot.eq_top_of_map_eq_top_of_perfect hMperf.commutator_eq_top hmapTop
  intro g hg
  have hg' : (⟨g, hg⟩ : M) ∈ ⨆ i, perfectCore (centralizer (((T i).subgroupOf M : Subgroup M) :
      Set M)) := hTop ▸ mem_top _
  have h2 := mem_map_of_mem M.subtype hg'
  rw [Subgroup.map_iSup] at h2
  simp_rw [← F4Pilot.perfectCore_inf_centralizer_eq_map (hTM _)] at h2
  exact h2

end Generic

section Model


theorem iSup_relLevi_subgroupOf_eq_top (K : Type) [Field K] :
    ⨆ I : {I : Finset (Fin Tag.F4.rank) // I.card ≤ 2},
      (relLevi K I.1).subgroupOf (adjointGroup TwistTag.E6.tag K) = ⊤ := by
  rw [eq_top_iff]
  refine le_trans (le_of_eq (E6Pilot.iSup_levi_adjDatumE6_eq_top K).symm) ?_
  refine iSup_le fun J => ?_
  have hcard : (J.1.image e6IndexToF4).card ≤ 2 := Finset.card_image_le.trans J.2
  refine le_iSup_of_le ⟨J.1.image e6IndexToF4, hcard⟩ ?_
  rw [E6Pilot.levi_adjDatumE6_eq]
  intro x hx
  have hx' : (x : ModGL TwistTag.E6.tag K) ∈
      rootSpan TwistTag.E6.tag K (E6Pilot.amalgamRoots J.1) := hx
  show (x : ModGL TwistTag.E6.tag K) ∈ relLevi K (J.1.image e6IndexToF4)
  refine rootSpan_mono (fun α hα => ?_) hx'
  obtain ⟨j, hj, hα⟩ := hα
  exact ⟨j, Finset.mem_coe.2 (mem_relNodeSet.2 (Finset.mem_image_of_mem _ hj)), hα⟩

theorem perfectCore_centralizer_relLeviTorus_subgroupOf {K : Type} [Field K] [Finite K]
    {A : Subgroup Kˣ} (hA : 3 ≤ Nat.card A) {I : Finset (Fin Tag.F4.rank)} (hI : I.card ≤ 2)
    (hTC : relLeviTorus K A I ≤ adjointGroup TwistTag.E6.tag K) :
    perfectCore (centralizer (((relLeviTorus K A I).subgroupOf (adjointGroup TwistTag.E6.tag K) :
        Subgroup (adjointGroup TwistTag.E6.tag K)) : Set (adjointGroup TwistTag.E6.tag K))) =
      (relLevi K I).subgroupOf (adjointGroup TwistTag.E6.tag K) := by
  have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  have h := perfectCore_inf_centralizer_relLeviTorus hA hI (K := K)
  rw [F4Pilot.perfectCore_inf_centralizer_eq_map hTC] at h
  apply Subgroup.map_injective (adjointGroup TwistTag.E6.tag K).subtype_injective
  rw [h, subgroupOf_map_subtype, inf_of_le_left (relLevi_le_adjointGroup I)]

theorem iSup_perfectCore_centralizer_conj_relLeviTorus_eq_top {K : Type} [Field K] [Finite K]
    {A : Subgroup Kˣ} (hA : 3 ≤ Nat.card A)
    (hTC : ∀ I, relLeviTorus K A I ≤ adjointGroup TwistTag.E6.tag K)
    (g : adjointGroup TwistTag.E6.tag K) :
    ⨆ I : {I : Finset (Fin Tag.F4.rank) // I.card ≤ 2},
      perfectCore (centralizer ((((relLeviTorus K A I.1).subgroupOf
        (adjointGroup TwistTag.E6.tag K)).map (MulAut.conj g).toMonoidHom :
          Subgroup (adjointGroup TwistTag.E6.tag K)) : Set (adjointGroup TwistTag.E6.tag K))) =
      ⊤ := by
  have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  have h1 : ∀ I : {I : Finset (Fin Tag.F4.rank) // I.card ≤ 2},
      perfectCore (centralizer ((((relLeviTorus K A I.1).subgroupOf
        (adjointGroup TwistTag.E6.tag K)).map (MulAut.conj g).toMonoidHom :
          Subgroup (adjointGroup TwistTag.E6.tag K)) : Set (adjointGroup TwistTag.E6.tag K))) =
      ((relLevi K I.1).subgroupOf (adjointGroup TwistTag.E6.tag K)).map
        (MulAut.conj g).toMonoidHom := by
    intro I
    rw [← F4Pilot.map_centralizer_mulEquiv, ← CFSG.Quasithin.map_perfectCore,
      perfectCore_centralizer_relLeviTorus_subgroupOf hA I.2 (hTC I.1)]
  simp_rw [h1]
  rw [← Subgroup.map_iSup, iSup_relLevi_subgroupOf_eq_top, ← MonoidHom.range_eq_map,
    MonoidHom.range_eq_top.2 (MulAut.conj g).surjective]

end Model

section Tori


variable {K : Type} [Field K]

theorem rootDiagUnit_mul_rootDiagUnit_mul_inv (a b : Fin TwistTag.E6.tag.rank → Kˣ) :
    rootDiagUnit TwistTag.E6.tag a * rootDiagUnit TwistTag.E6.tag b *
        (rootDiagUnit TwistTag.E6.tag a)⁻¹ = rootDiagUnit TwistTag.E6.tag b := by
  rw [← rootDiagUnit_mul, mul_comm, rootDiagUnit_mul, mul_inv_cancel_right]

theorem exists_map_relLeviTorus_eq_conj_twistedE6 {f : ℕ} (hf : 1 ≤ f) [Finite K]
    (hK : Nat.card K = (2 ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (2 ^ f))
    {A : Subgroup Kˣ} (hAσ : ∀ c ∈ A, Units.map σ.toRingHom.toMonoidHom c = c)
    (hAδ : ∀ δ : K ≃+* K, ∀ c ∈ A, Units.map δ.toRingHom.toMonoidHom c ∈ A)
    (δ : MulAut (graphFixedRootGroup TwistTag.E6 K σ.toRingHom)) :
    ∃ g : graphFixedRootGroup TwistTag.E6 K σ.toRingHom, ∀ I : Finset (Fin Tag.F4.rank),
      ((relLeviTorus K A I).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ.toRingHom)).map
          δ.toMonoidHom =
        ((relLeviTorus K A I).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ.toRingHom)).map
          (MulAut.conj g).toMonoidHom := by
  obtain ⟨-, -, -, -, -, hΔ, hδ0, hNF, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form Nat.prime_two hf K hK σ hσ
  obtain ⟨g, u, δ₀, hδ⟩ := hNF δ
  refine ⟨g, fun I => ?_⟩
  set ν : MulAut (graphFixedRootGroup TwistTag.E6 K σ.toRingHom) :=
    compatDiagAutHom TwistTag.E6 K σ.toRingHom u * fieldActor σ δ₀ with hνdef
  have hν : ∀ (B : Fin Tag.F4.rank → Kˣ) (x : graphFixedRootGroup TwistTag.E6 K σ.toRingHom),
      (x : ModGL TwistTag.E6.tag K) = rootDiagUnit TwistTag.E6.tag (relTuple B) →
      ((ν x : graphFixedRootGroup TwistTag.E6 K σ.toRingHom) : ModGL TwistTag.E6.tag K) =
        rootDiagUnit TwistTag.E6.tag
          (relTuple (fun a => Units.map δ₀.toRingHom.toMonoidHom (B a))) := by
    intro B x hx
    rw [hνdef, MulAut.mul_apply, hΔ, hδ0, hx, units_map_entrywiseHom_rootDiagUnit_ringEquiv,
      rootDiagUnit_mul_rootDiagUnit_mul_inv]
    rfl
  have hB' : ∀ (ε : K ≃+* K) {B : Fin Tag.F4.rank → Kˣ}, B ∈ F4Pilot.leviTupleSet A I →
      (fun a => Units.map ε.toRingHom.toMonoidHom (B a)) ∈ F4Pilot.leviTupleSet A I := by
    rintro ε B ⟨hB1, hBA⟩
    exact ⟨fun j hj => by simp only [hB1 j hj, map_one], fun i => hAδ ε _ (hBA i)⟩
  have hνT : ((relLeviTorus K A I).subgroupOf
      (graphFixedRootGroup TwistTag.E6 K σ.toRingHom)).map ν.toMonoidHom =
      (relLeviTorus K A I).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ.toRingHom) := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      obtain ⟨B, hB, hBx⟩ := mem_relLeviTorus.1 (mem_subgroupOf.1 hx)
      refine mem_subgroupOf.2 ?_
      change ((ν x : graphFixedRootGroup TwistTag.E6 K σ.toRingHom) : ModGL TwistTag.E6.tag K) ∈
        relLeviTorus K A I
      rw [hν B x hBx.symm]
      exact rootDiagUnit_relTuple_mem_relLeviTorus (hB' δ₀ hB)
    · intro y hy
      obtain ⟨B, hB, hBy⟩ := mem_relLeviTorus.1 (mem_subgroupOf.1 hy)
      have hmem := rootDiagUnit_relTuple_mem_relLeviTorus (hB' δ₀.symm hB)
      refine ⟨⟨_, relLeviTorus_le_C0 hAσ I hmem⟩, mem_subgroupOf.2 hmem, Subtype.ext ?_⟩
      change ((ν ⟨_, relLeviTorus_le_C0 hAσ I hmem⟩ :
        graphFixedRootGroup TwistTag.E6 K σ.toRingHom) : ModGL TwistTag.E6.tag K) = y
      rw [hν _ _ rfl, ← hBy]
      congr 2
      funext a
      exact Units.ext (δ₀.apply_symm_apply _)
  have hδν : δ.toMonoidHom = (MulAut.conj g).toMonoidHom.comp ν.toMonoidHom := by
    refine MonoidHom.ext fun x => ?_
    rw [hδ, hνdef, mul_assoc]
    rfl
  rw [hδν, ← Subgroup.map_map, hνT]

theorem unitsRange_stable_twistedE6 {f : ℕ} {k : Type} [Field k] [Algebra k K] [Finite k]
    (hk : Nat.card k = 2 ^ f) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    (∀ c ∈ (Units.map (algebraMap k K).toMonoidHom).range, Units.map σ.toMonoidHom c = c) ∧
    ∀ δ : K ≃+* K, ∀ c ∈ (Units.map (algebraMap k K).toMonoidHom).range,
      Units.map δ.toRingHom.toMonoidHom c ∈ (Units.map (algebraMap k K).toMonoidHom).range := by
  have hσι : ∀ c : k, σ (algebraMap k K c) = algebraMap k K c := fun c =>
    (sigma_eq_self_iff hk hσ _).2 ⟨c, rfl⟩
  refine ⟨?_, ?_⟩
  · rintro _ ⟨u, rfl⟩
    exact Units.ext (hσι u)
  · rintro δ _ ⟨u, rfl⟩
    have hfix : σ (δ (algebraMap k K u)) = δ (algebraMap k K u) := by
      rw [hσ, ← map_pow, ← hσ, hσι]
    obtain ⟨a, ha⟩ := (sigma_eq_self_iff hk hσ _).1 hfix
    have ha0 : a ≠ 0 := by
      rintro rfl
      rw [map_zero, eq_comm, map_eq_zero_iff _ δ.injective,
        map_eq_zero_iff _ (algebraMap k K).injective] at ha
      exact u.ne_zero ha
    refine ⟨Units.mk0 a ha0, Units.ext ?_⟩
    change algebraMap k K a = δ (algebraMap k K u)
    exact ha

end Tori

section Gen


variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem eq_one_of_mem_center_of_le_twistedE6 {M : Subgroup G} (hLM : L ≤ M) {t : G}
    (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hZ : Odd (Nat.card (center M))) {m : M} (hmL : (m : G) ∈ L) (hmZ : m ∈ center M) :
    m = 1 := by
  have htC : t ∈ centralizer (L : Set G) := (hKt ▸ mem_zpowers t :
    t ∈ centralizer (L : Set G) ⊓ centralizer ({t} : Set G)).1
  have hmt : (m : G) ∈ centralizer ({t} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    exact mem_centralizer_iff.1 htC _ hmL
  have hmCL : (m : G) ∈ centralizer (L : Set G) := by
    rw [mem_centralizer_iff]
    intro l hl
    exact congrArg Subtype.val (mem_center_iff.1 hmZ ⟨l, hLM hl⟩)
  have hmz : (m : G) ∈ zpowers t := hKt ▸ ⟨hmCL, hmt⟩
  have hmodd := E6Pilot.odd_orderOf_of_mem_center hZ hmZ
  have hdvd2 : orderOf m ∣ 2 := by
    rw [← Subgroup.orderOf_coe, ← ht]
    exact orderOf_dvd_of_mem_zpowers hmz
  rcases (Nat.dvd_prime Nat.prime_two).1 hdvd2 with h1 | h2
  · exact orderOf_eq_one_iff.1 h1
  · rw [h2] at hmodd
    exact absurd hmodd (by decide)

theorem le_iSup_perfectCore_of_mem_normalizer_twistedE6_cover (hset : StandardSetting G L)
    {f : ℕ} {K : Type} [Field K] (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ f) (e : L ≃* graphFixedRootGroup TwistTag.E6 K σ) {t : G}
    (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {A : Subgroup Kˣ} (hA3 : 3 ≤ Nat.card A) (hAσ : ∀ c ∈ A, Units.map σ.toMonoidHom c = c)
    (hAδ : ∀ δ : K ≃+* K, ∀ c ∈ A, Units.map δ.toRingHom.toMonoidHom c ∈ A)
    {M : Subgroup G} (hMp : ⁅M, M⁆ = M) (hZ : Odd (Nat.card (center M)))
    (eM : M ⧸ center M ≃* adjointGroup .E6 K) (htM : t ∈ normalizer (M : Set G)) :
    M ≤ ⨆ I : {I : Finset (Fin Tag.F4.rank) // I.card ≤ 2},
      perfectCore (M ⊓ centralizer (modelToG e (relLeviTorus K A I.1) : Set G)) := by
  have hf := one_le_of_card_sq_twistedE6 hK
  have := finite_of_card hK
  have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  obtain ⟨σE, rfl⟩ := exists_ringEquiv_toRingHom_eq σ
  have hσE : ∀ c, σE c = c ^ (2 ^ f) := fun c => hσ c
  have hσσ : ∀ c, σE (σE c) = c := fun c => apply_apply_eq hK hσ c
  obtain ⟨⟨σ₂, -, -, hσc, φ, hφ⟩, hML⟩ :=
    inf_centralizer_eq_of_mem_normalizer_twistedE6_cover hset hK hσ e ht hKt hMp hZ hK eM htM
  have hσ₂ : σ₂ = σE := RingEquiv.ext fun c => by rw [hσc, hσE]
  rw [hσ₂] at hφ
  have hLM : L ≤ M := hML ▸ inf_le_left
  have htC : t ∈ centralizer (L : Set G) := (hKt ▸ mem_zpowers t :
    t ∈ centralizer (L : Set G) ⊓ centralizer ({t} : Set G)).1
  have hC₀C : graphFixedRootGroup TwistTag.E6 K σE.toRingHom ≤ adjointGroup TwistTag.E6.tag K :=
    graphFixedRootGroup_le_adjointGroup' _
  set ψ : M ⧸ center M ≃* adjointGroup TwistTag.E6.tag K := eM.trans φ with hψdef
  set π : M →* adjointGroup TwistTag.E6.tag K :=
    ψ.toMonoidHom.comp (QuotientGroup.mk' (center M)) with hπdef
  have hfixL : ∀ x : graphFixedRootGroup TwistTag.E6 K σE.toRingHom,
      ((π ⟨(e.symm x : G), hLM (e.symm x).2⟩ : adjointGroup TwistTag.E6.tag K) :
        ModGL TwistTag.E6.tag K) ∈ graphFixedRootGroup TwistTag.E6 K σE.toRingHom := by
    intro x
    set m : M := ⟨(e.symm x : G), hLM (e.symm x).2⟩ with hm
    have hβm : M.normalizerMonoidHom ⟨t, htM⟩ m = m := by
      apply Subtype.ext
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
      have h := mem_centralizer_iff.1 htC _ (e.symm x).2
      change t * (e.symm x : G) * t⁻¹ = (e.symm x : G)
      rw [← h, mul_inv_cancel_right]
    have hα : normalizerQuotMulAut eM ⟨t, htM⟩ (eM (QuotientGroup.mk' (center M) m)) =
        eM (QuotientGroup.mk' (center M) m) := by
      rw [normalizerQuotMulAut_apply, hβm]
    have hfix : (diagramConjAut TwistTag.E6 K * entrywiseAdjointAut TwistTag.E6.tag σE)
        (π m) = π m := by
      rw [← hφ]
      change φ (normalizerQuotMulAut eM ⟨t, htM⟩ (φ.symm (φ (eM (QuotientGroup.mk' (center M) m)))))
        = φ (eM (QuotientGroup.mk' (center M) m))
      rw [MulEquiv.symm_apply_apply, hα]
    have hmem : π m ∈ E6Pilot.fixSubgroup
        (diagramConjAut TwistTag.E6 K * entrywiseAdjointAut TwistTag.E6.tag σE) := hfix
    rw [fixSubgroup_graphField_eq_twistedE6 σE hσσ] at hmem
    exact mem_subgroupOf.1 hmem
  set F₀ : graphFixedRootGroup TwistTag.E6 K σE.toRingHom →* adjointGroup TwistTag.E6.tag K :=
    π.comp ((Subgroup.inclusion hLM).comp e.symm.toMonoidHom) with hF₀
  have hF₀apply : ∀ x, F₀ x = π ⟨(e.symm x : G), hLM (e.symm x).2⟩ := fun _ => rfl
  have hF₀mem : ∀ x, F₀ x ∈ (graphFixedRootGroup TwistTag.E6 K σE.toRingHom).subgroupOf
      (adjointGroup TwistTag.E6.tag K) := fun x => mem_subgroupOf.2 (hfixL x)
  set F₁ : graphFixedRootGroup TwistTag.E6 K σE.toRingHom →*
      graphFixedRootGroup TwistTag.E6 K σE.toRingHom :=
    (Subgroup.subgroupOfEquivOfLe hC₀C).toMonoidHom.comp (F₀.codRestrict _ hF₀mem) with hF₁
  have hF₁coe : ∀ x, ((F₁ x : graphFixedRootGroup TwistTag.E6 K σE.toRingHom) :
      ModGL TwistTag.E6.tag K) = ((F₀ x : adjointGroup TwistTag.E6.tag K) :
        ModGL TwistTag.E6.tag K) := fun _ => rfl
  have hF₁inj : Function.Injective F₁ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have h1 : ((F₀ x : adjointGroup TwistTag.E6.tag K) : ModGL TwistTag.E6.tag K) = 1 := by
      rw [← hF₁coe, hx]
      rfl
    have h2 : F₀ x = 1 := Subtype.ext h1
    rw [hF₀apply, hπdef, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
    have h3 := eq_one_of_mem_center_of_le_twistedE6 hLM ht hKt hZ (e.symm x).2 h2
    have h4 : ((e.symm x : L) : G) = ((1 : L) : G) := by
      rw [OneMemClass.coe_one]
      exact congrArg Subtype.val h3
    exact (MulEquiv.map_eq_one_iff e.symm).1 (Subtype.ext h4)
  set δ : MulAut (graphFixedRootGroup TwistTag.E6 K σE.toRingHom) :=
    MulEquiv.ofBijective F₁ (Finite.injective_iff_bijective.1 hF₁inj) with hδdef
  have hδcoe : ∀ x, ((δ x : graphFixedRootGroup TwistTag.E6 K σE.toRingHom) :
      ModGL TwistTag.E6.tag K) = ((π ⟨(e.symm x : G), hLM (e.symm x).2⟩ :
        adjointGroup TwistTag.E6.tag K) : ModGL TwistTag.E6.tag K) := fun _ => rfl
  obtain ⟨g, hg⟩ := exists_map_relLeviTorus_eq_conj_twistedE6 hf hK σE hσE hAσ hAδ δ
  set g' : adjointGroup TwistTag.E6.tag K := ⟨(g : ModGL TwistTag.E6.tag K), hC₀C g.2⟩ with hg'
  have hkey : ∀ I : Finset (Fin Tag.F4.rank),
      ((modelToG e (relLeviTorus K A I)).subgroupOf M).map π =
        ((relLeviTorus K A I).subgroupOf (adjointGroup TwistTag.E6.tag K)).map
          (MulAut.conj g').toMonoidHom := by
    intro I
    have hTC : relLeviTorus K A I ≤ graphFixedRootGroup TwistTag.E6 K σE.toRingHom :=
      relLeviTorus_le_C0 hAσ I
    ext y
    constructor
    · rintro ⟨m, hm, rfl⟩
      obtain ⟨x, hxT, hxm⟩ := (mem_modelToG e).1 (mem_subgroupOf.1 hm)
      have hmx : m = ⟨(e.symm x : G), hLM (e.symm x).2⟩ := Subtype.ext hxm.symm
      have hδx : δ x ∈ ((relLeviTorus K A I).subgroupOf
          (graphFixedRootGroup TwistTag.E6 K σE.toRingHom)).map δ.toMonoidHom :=
        ⟨x, mem_subgroupOf.2 hxT, rfl⟩
      rw [hg I] at hδx
      obtain ⟨x', hx'T, hx'⟩ := hδx
      refine ⟨⟨(x' : ModGL TwistTag.E6.tag K), hC₀C x'.2⟩,
        mem_subgroupOf.2 (mem_subgroupOf.1 hx'T), Subtype.ext ?_⟩
      rw [hmx, ← hδcoe x]
      have h1 := congrArg (fun z : graphFixedRootGroup TwistTag.E6 K σE.toRingHom =>
        (z : ModGL TwistTag.E6.tag K)) hx'
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Subgroup.coe_mul,
        Subgroup.coe_inv] at h1
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv,
        hg']
      exact h1
    · rintro ⟨z, hz, rfl⟩
      have hzT : (z : ModGL TwistTag.E6.tag K) ∈ relLeviTorus K A I := mem_subgroupOf.1 hz
      have hz' : (MulAut.conj g).toMonoidHom ⟨(z : ModGL TwistTag.E6.tag K), hTC hzT⟩ ∈
          ((relLeviTorus K A I).subgroupOf
            (graphFixedRootGroup TwistTag.E6 K σE.toRingHom)).map (MulAut.conj g).toMonoidHom :=
        ⟨⟨(z : ModGL TwistTag.E6.tag K), hTC hzT⟩, mem_subgroupOf.2 hzT, rfl⟩
      rw [← hg I] at hz'
      obtain ⟨x, hxT, hx⟩ := hz'
      refine ⟨⟨(e.symm x : G), hLM (e.symm x).2⟩,
        mem_subgroupOf.2 (symm_mem_modelToG e (mem_subgroupOf.1 hxT)), Subtype.ext ?_⟩
      rw [← hδcoe x]
      have h1 := congrArg (fun z : graphFixedRootGroup TwistTag.E6 K σE.toRingHom =>
        (z : ModGL TwistTag.E6.tag K)) hx
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Subgroup.coe_mul,
        Subgroup.coe_inv] at h1
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv,
        hg']
      exact h1
  have hgen : ⨆ I : {I : Finset (Fin Tag.F4.rank) // I.card ≤ 2},
      perfectCore (centralizer ((((modelToG e (relLeviTorus K A I.1)).subgroupOf M).map
        (ψ.toMonoidHom.comp (QuotientGroup.mk' (center M))) :
          Subgroup (adjointGroup TwistTag.E6.tag K)) : Set (adjointGroup TwistTag.E6.tag K))) =
      ⊤ := by
    have h := iSup_perfectCore_centralizer_conj_relLeviTorus_eq_top hA3
      (fun I => (relLeviTorus_le_C0 hAσ I).trans hC₀C) g'
    simp_rw [← hkey] at h
    exact h
  exact le_iSup_perfectCore_of_quotient_mulEquiv hMp ψ
    (fun I : {I : Finset (Fin Tag.F4.rank) // I.card ≤ 2} => modelToG e (relLeviTorus K A I.1))
    (fun I => (modelToG_le e _).trans hLM) hgen

theorem pieceCore_le_of_neighbourCore_le {K : Type} [Field K] {σ : K →+* K}
    (e : L ≃* graphFixedRootGroup TwistTag.E6 K σ) (A : Subgroup Kˣ) {G₀ : Subgroup G}
    (hLG₀ : L ≤ G₀) (hX : neighbourCore e A .X ≤ G₀) (hY : neighbourCore e A .Y ≤ G₀)
    {I : Finset (Fin Tag.F4.rank)} (hI : I.card ≤ 2) : pieceCore e A I ≤ G₀ := by
  refine (pieceCore_le_neighbourCore e A (F4Pilot.amalgamPlacement I)
    (F4Pilot.subset_nodes_amalgamPlacement hI)).trans ?_
  generalize F4Pilot.amalgamPlacement I = N
  cases N with
  | X => exact hX
  | Y => exact hY
  | X' =>
    rw [neighbourCore_X'_eq_map_conj e A]
    rintro _ ⟨y, hy, rfl⟩
    have hn := hLG₀ (e.symm ⟨twistedE6RelWeyl K relWordXPrime,
      twistedE6RelWeyl_mem σ relWordXPrime⟩).2
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact mul_mem (mul_mem hn (hX hy)) (inv_mem hn)

theorem unique_of_fieldRow_twistedE6 (hset : StandardSetting G L) {f : ℕ} {K : Type} [Field K]
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f)
    (e : L ≃* graphFixedRootGroup TwistTag.E6 K σ) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {A : Subgroup Kˣ} (hA3 : 3 ≤ Nat.card A) (hAσ : ∀ c ∈ A, Units.map σ.toMonoidHom c = c)
    (hAδ : ∀ δ : K ≃+* K, ∀ c ∈ A, Units.map δ.toRingHom.toMonoidHom c ∈ A)
    {G₀ : Subgroup G} (hG₀p : ⁅G₀, G₀⁆ = G₀) (hZ : Odd (Nat.card (center G₀)))
    (Ψ : G₀ ⧸ center G₀ ≃* adjointGroup .E6 K)
    (hpieces : ∀ I : Finset (Fin Tag.F4.rank), I.card ≤ 2 → pieceCore e A I ≤ G₀) :
    ∀ g : G, g⁻¹ * t * g ∈ normalizer (G₀ : Set G) → g ∈ normalizer (G₀ : Set G) :=
  F4Pilot.unique_of_forall_conjugate_generation
    (J := fun I : {I : Finset (Fin Tag.F4.rank) // I.card ≤ 2} => modelToG e (relLeviTorus K A I.1))
    (fun I => hpieces I.1 I.2)
    (fun h htM => le_iSup_perfectCore_of_mem_normalizer_twistedE6_cover hset hK hσ e ht hKt hA3
      hAσ hAδ (E6Pilot.commutator_conjugate_eq hG₀p h)
      (by rw [E6Pilot.card_center_conjugate]; exact hZ)
      ((E6Pilot.coverConjugateQuotientCenterEquiv G₀ h).symm.trans Ψ) htM)

theorem unique_of_fieldRow_twistedE6_of_neighbourCore (hset : StandardSetting G L) {f : ℕ}
    (hf2 : 2 ≤ f) {k K : Type} [Field k] [Field K] [Algebra k K] (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f)
    (e : L ≃* graphFixedRootGroup TwistTag.E6 K σ) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {G₀ : Subgroup G} (hG₀p : ⁅G₀, G₀⁆ = G₀) (hZ : Odd (Nat.card (center G₀)))
    (Ψ : G₀ ⧸ center G₀ ≃* adjointGroup .E6 K) (hLG₀ : L ≤ G₀)
    (hX : neighbourCore e (Units.map (algebraMap k K).toMonoidHom).range .X ≤ G₀)
    (hY : neighbourCore e (Units.map (algebraMap k K).toMonoidHom).range .Y ≤ G₀) :
    ∀ g : G, g⁻¹ * t * g ∈ normalizer (G₀ : Set G) → g ∈ normalizer (G₀ : Set G) := by
  have : Finite k := F4Pilot.finite_of_natCard_eq_two_pow hk
  obtain ⟨hA3, -, hAσ, -⟩ := unitsRange_facts (K := K) hf2 hk hσ
  exact unique_of_fieldRow_twistedE6 hset hK hσ e ht hKt hA3 hAσ
    (unitsRange_stable_twistedE6 hk hσ).2 hG₀p hZ Ψ
    (fun I hI => pieceCore_le_of_neighbourCore_le e _ hLG₀ hX hY hI)

end Gen

end CFSG.SeitzReduction.TwistedE6Pilot
