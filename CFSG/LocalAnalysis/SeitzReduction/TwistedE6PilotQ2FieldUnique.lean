module

public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotUniqueFieldStep3
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotFieldNormalize

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.TwistedE6Pilot

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.EvenSmallLie CFSG.LieType.Chevalley.E6GraphLevi
open CFSG.Quasithin (perfectCore)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)
open CFSG.SeitzReduction.EPilot (normalizerQuotMulAut normalizerQuotMulAut_apply)

local instance twistedE6PilotQ2FieldUniqueNeZero : NeZero TwistTag.E6.tag.rank := ⟨by decide⟩

section HR15


variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem false_of_fieldModel_twistedE6 (hset : SeitzSetting G L) {f : ℕ} (hf : 1 ≤ f) {K : Type}
    [Field K] (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f)
    (e : L ≃* graphFixedRootGroup TwistTag.E6 K σ) {t : G} (htC : t ∈ centralizer (L : Set G))
    (ht : orderOf t = 2) {G₀ : Subgroup G} (hG₀p : ⁅G₀, G₀⁆ = G₀)
    (hZ : Odd (Nat.card (center G₀))) {K₂ : Type} [Field K₂] (hK₂ : Nat.card K₂ = (2 ^ f) ^ 2)
    (e₀ : G₀ ⧸ center G₀ ≃* adjointGroup .E6 K₂) (htN : t ∈ normalizer (G₀ : Set G))
    (huniq : ∀ g : G, g⁻¹ * t * g ∈ normalizer (G₀ : Set G) → g ∈ normalizer (G₀ : Set G)) :
    False := by
  have hKt := inf_centralizer_eq_zpowers_twistedE6 hset hf hK hσ e htC ht
  obtain ⟨⟨σ₂, -, -, -, φ, hφ⟩, -⟩ := inf_centralizer_eq_of_mem_normalizer_twistedE6_cover
    hset.standardSetting hK hσ e ht hKt hG₀p hZ hK₂ e₀ htN
  have := hset.standardSetting.simple
  have hK₂' := card_eq_two_pow_two_mul_twistedE6 hK₂
  have := F4Pilot.finite_of_natCard_eq_two_pow hK₂'
  exact EPilot.false_of_simple_of_E6_conj_graph_quot K₂ e₀ htN ht
    ⟨φ, 1, 1, σ₂, by
      rw [hφ, FieldGraphFieldPointwise.graphField_eq_exactNormalAut, map_one, one_mul]
      rfl⟩ huniq

theorem le_of_fieldModel_twistedE6 (hset : SeitzSetting G L) {f : ℕ} (hf : 1 ≤ f) {K : Type}
    [Field K] (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f)
    (e : L ≃* graphFixedRootGroup TwistTag.E6 K σ) {t : G} (htC : t ∈ centralizer (L : Set G))
    (ht : orderOf t = 2) {G₀ : Subgroup G} (hG₀p : ⁅G₀, G₀⁆ = G₀)
    (hZ : Odd (Nat.card (center G₀))) {K₂ : Type} [Field K₂] (hK₂ : Nat.card K₂ = (2 ^ f) ^ 2)
    (e₀ : G₀ ⧸ center G₀ ≃* adjointGroup .E6 K₂) (htN : t ∈ normalizer (G₀ : Set G)) :
    L ≤ G₀ := by
  have hKt := inf_centralizer_eq_zpowers_twistedE6 hset hf hK hσ e htC ht
  rw [← (inf_centralizer_eq_of_mem_normalizer_twistedE6_cover hset.standardSetting hK hσ e ht hKt
    hG₀p hZ hK₂ e₀ htN).2]
  exact inf_le_left

end HR15

section Model


variable {K : Type} [Field K]

theorem relWordXPrime_single_three :
    twistedE6RelAct relWordXPrime (Pi.single 3 1) = Pi.single 1 1 ∧
      twistedE6RelAct relWordXPrime (-Pi.single 3 1) = -Pi.single 1 1 := by
  decide +kernel

theorem relWordXPrime_conj_xUnit_yUnit_three [CharP K 2] (c : K) :
    twistedE6RelWeyl K relWordXPrime * xUnit TwistTag.E6.tag K 3 c *
        (twistedE6RelWeyl K relWordXPrime)⁻¹ = xUnit TwistTag.E6.tag K 1 c ∧
      twistedE6RelWeyl K relWordXPrime * yUnit TwistTag.E6.tag K 3 c *
        (twistedE6RelWeyl K relWordXPrime)⁻¹ = yUnit TwistTag.E6.tag K 1 c := by
  obtain ⟨h1, h2⟩ := relWordXPrime_single_three
  refine ⟨?_, ?_⟩
  · rw [← pinnedX_single, ← pinnedX_single,
      twistedE6RelWeyl_conj_pinnedX relWordXPrime (isRoot_single _ 3) c, h1]
  · rw [← pinnedX_neg_single, ← pinnedX_neg_single,
      twistedE6RelWeyl_conj_pinnedX relWordXPrime
        (CFSG.LieType.Chevalley.IsRoot.neg (isRoot_single _ 3)) c, h2]

theorem adjointGroup_le_sup_map_conj_subsystemGroup_setA [CharP K 2] :
    adjointGroup TwistTag.E6.tag K ≤
      subsystemGroup TwistTag.E6.tag K E6GraphLevi.setA ⊔
        (subsystemGroup TwistTag.E6.tag K E6GraphLevi.setA).map
          (MulAut.conj (twistedE6RelWeyl K relWordXPrime)).toMonoidHom := by
  rw [adjointGroup, Subgroup.closure_le]
  have h3 : (3 : Fin TwistTag.E6.tag.rank) ∈ E6GraphLevi.setA :=
    show (3 : Fin TwistTag.E6.tag.rank) ≠ E6GraphHighestRoot.e6Idx 1 by decide
  rintro g ⟨i, c, hg | hg⟩
  · have hg' : g = xUnit TwistTag.E6.tag K i c := Units.ext hg
    subst hg'
    by_cases hi : i = 1
    · subst hi
      refine Subgroup.mem_sup_right ⟨xUnit TwistTag.E6.tag K 3 c,
        Subgroup.subset_closure ⟨3, h3, c, Or.inl rfl⟩, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact (relWordXPrime_conj_xUnit_yUnit_three c).1
    · exact Subgroup.mem_sup_left (Subgroup.subset_closure ⟨i, hi, c, Or.inl rfl⟩)
  · have hg' : g = yUnit TwistTag.E6.tag K i c := Units.ext hg
    subst hg'
    by_cases hi : i = 1
    · subst hi
      refine Subgroup.mem_sup_right ⟨yUnit TwistTag.E6.tag K 3 c,
        Subgroup.subset_closure ⟨3, h3, c, Or.inr rfl⟩, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact (relWordXPrime_conj_xUnit_yUnit_three c).2
    · exact Subgroup.mem_sup_left (Subgroup.subset_closure ⟨i, hi, c, Or.inr rfl⟩)

theorem commutator_subsystemGroup_setA (h2 : (2 : K) = 0) :
    ⁅subsystemGroup TwistTag.E6.tag K E6GraphLevi.setA,
        subsystemGroup TwistTag.E6.tag K E6GraphLevi.setA⁆ =
      subsystemGroup TwistTag.E6.tag K E6GraphLevi.setA := by
  have hperf : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 6) K) :=
    CFSG.ClassicalModels.specialLinear_isPerfect_of_three_le (by norm_num)
  have h := hperf.commutator_eq_top
  rw [commutator_def] at h
  rw [← E6GraphLevi.range_realize h2, MonoidHom.range_eq_map, ← Subgroup.map_commutator, h]

theorem subsystemGroup_setA_le_centralizer_thetaRankOneGroup (h2 : (2 : K) = 0) {k : Type}
    [Field k] (ι : k →+* K) :
    subsystemGroup TwistTag.E6.tag K E6GraphLevi.setA ≤
      centralizer (thetaRankOneGroup ι : Set (ModGL TwistTag.E6.tag K)) :=
  (E6GraphLevi.subsystemGroup_le_centralizer_thetaSL2 h2).trans
    (centralizer_le (E6GraphLevi.thetaRankOneGroup_le_range h2 ι))

theorem twistedE6RelWeyl_relWordXPrime_mem_adjointGroup :
    twistedE6RelWeyl K relWordXPrime ∈ adjointGroup TwistTag.E6.tag K :=
  graphFixedRootGroup_le_adjointGroup' (RingHom.id K) (twistedE6RelWeyl_mem _ relWordXPrime)

theorem commutator_subgroupOf_of_le_of_perfect {M : Type*} [Group M] {H C : Subgroup M} (hHC : H ≤ C)
    (hH : ⁅H, H⁆ = H) : ⁅H.subgroupOf C, H.subgroupOf C⁆ = H.subgroupOf C := by
  apply Subgroup.map_injective C.subtype_injective
  rw [Subgroup.map_commutator, subgroupOf_map_subtype, inf_of_le_left hHC, hH]

theorem map_le_perfectCore_centralizer_map {M : Type*} [Group M] [Finite M] {H S : Subgroup M}
    (hH : ⁅H, H⁆ = H) (hHS : H ≤ centralizer (S : Set M)) (ε : MulAut M) :
    H.map ε.toMonoidHom ≤ perfectCore (centralizer ((S.map ε.toMonoidHom : Subgroup M) : Set M)) := by
  refine CFSG.Quasithin.le_perfectCore_of_perfect ?_ (by rw [← Subgroup.map_commutator, hH])
  rw [← F4Pilot.map_centralizer_mulEquiv]
  exact Subgroup.map_mono hHS

theorem map_conj_subsystemGroup_setA_le_adjointGroup :
    (subsystemGroup TwistTag.E6.tag K E6GraphLevi.setA).map
        (MulAut.conj (twistedE6RelWeyl K relWordXPrime)).toMonoidHom ≤
      adjointGroup TwistTag.E6.tag K := by
  rintro _ ⟨y, hy, rfl⟩
  exact mul_mem (mul_mem twistedE6RelWeyl_relWordXPrime_mem_adjointGroup
    (subsystemGroup_le_adjointGroup_E6 _ hy))
    (inv_mem twistedE6RelWeyl_relWordXPrime_mem_adjointGroup)

theorem subgroupOf_setA_sup_eq_top [CharP K 2] :
    (subsystemGroup TwistTag.E6.tag K E6GraphLevi.setA).subgroupOf
        (adjointGroup TwistTag.E6.tag K) ⊔
      ((subsystemGroup TwistTag.E6.tag K E6GraphLevi.setA).map
        (MulAut.conj (twistedE6RelWeyl K relWordXPrime)).toMonoidHom).subgroupOf
          (adjointGroup TwistTag.E6.tag K) = ⊤ := by
  rw [← Subgroup.subgroupOf_sup (subsystemGroup_le_adjointGroup_E6 _)
    map_conj_subsystemGroup_setA_le_adjointGroup, Subgroup.subgroupOf_eq_top]
  exact adjointGroup_le_sup_map_conj_subsystemGroup_setA

theorem subgroupOf_setA_le_centralizer (h2 : (2 : K) = 0) {k : Type} [Field k] (ι : k →+* K)
    {A : Subgroup (ModGL TwistTag.E6.tag K)} (hAJ : A ≤ thetaRankOneGroup ι) :
    (subsystemGroup TwistTag.E6.tag K E6GraphLevi.setA).subgroupOf
        (adjointGroup TwistTag.E6.tag K) ≤
      centralizer ((A.subgroupOf (adjointGroup TwistTag.E6.tag K) :
        Subgroup (adjointGroup TwistTag.E6.tag K)) : Set (adjointGroup TwistTag.E6.tag K)) := by
  intro p hp
  rw [mem_centralizer_iff]
  intro a ha
  exact Subtype.ext (mem_centralizer_iff.1
    (subsystemGroup_setA_le_centralizer_thetaRankOneGroup h2 ι (mem_subgroupOf.1 hp)) _
    (hAJ (mem_subgroupOf.1 ha)))

theorem subgroupOf_map_setA_le_centralizer (h2 : (2 : K) = 0) {k : Type} [Field k] (ι : k →+* K)
    {A : Subgroup (ModGL TwistTag.E6.tag K)} (hAJ : A ≤ thetaRankOneGroup ι) :
    ((subsystemGroup TwistTag.E6.tag K E6GraphLevi.setA).map
        (MulAut.conj (twistedE6RelWeyl K relWordXPrime)).toMonoidHom).subgroupOf
          (adjointGroup TwistTag.E6.tag K) ≤
      centralizer (((A.map (MulAut.conj (twistedE6RelWeyl K relWordXPrime)).toMonoidHom).subgroupOf
        (adjointGroup TwistTag.E6.tag K) : Subgroup (adjointGroup TwistTag.E6.tag K)) :
          Set (adjointGroup TwistTag.E6.tag K)) := by
  intro p hp
  rw [mem_centralizer_iff]
  intro a ha
  obtain ⟨y, hy, hyp⟩ := mem_subgroupOf.1 hp
  obtain ⟨x, hx, hxa⟩ := mem_subgroupOf.1 ha
  apply Subtype.ext
  have hc : x * y = y * x :=
    mem_centralizer_iff.1 (subsystemGroup_setA_le_centralizer_thetaRankOneGroup h2 ι hy) x (hAJ hx)
  have key : ∀ n : ModGL TwistTag.E6.tag K,
      n * x * n⁻¹ * (n * y * n⁻¹) = n * y * n⁻¹ * (n * x * n⁻¹) := fun n => by
    calc n * x * n⁻¹ * (n * y * n⁻¹) = n * (x * y) * n⁻¹ := by group
      _ = n * (y * x) * n⁻¹ := by rw [hc]
      _ = n * y * n⁻¹ * (n * x * n⁻¹) := by group
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hyp hxa
  rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hyp, ← hxa]
  exact key _

theorem perfectCore_sup_perfectCore_centralizer_nonsplitPair_eq_top [Finite K]
    (h2 : (2 : K) = 0) {k : Type} [Field k] (ι : k →+* K)
    {A : Subgroup (ModGL TwistTag.E6.tag K)} (hAJ : A ≤ thetaRankOneGroup ι)
    (ε : MulAut (adjointGroup TwistTag.E6.tag K)) :
    perfectCore (centralizer (((A.subgroupOf (adjointGroup TwistTag.E6.tag K)).map
        ε.toMonoidHom : Subgroup (adjointGroup TwistTag.E6.tag K)) :
          Set (adjointGroup TwistTag.E6.tag K))) ⊔
      perfectCore (centralizer ((((A.map (MulAut.conj (twistedE6RelWeyl K
        relWordXPrime)).toMonoidHom).subgroupOf (adjointGroup TwistTag.E6.tag K)).map
          ε.toMonoidHom : Subgroup (adjointGroup TwistTag.E6.tag K)) :
            Set (adjointGroup TwistTag.E6.tag K))) = ⊤ := by
  have : CharP K 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2
  have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  have hLAp := commutator_subsystemGroup_setA h2
  have hPp := commutator_subgroupOf_of_le_of_perfect (subsystemGroup_le_adjointGroup_E6 _) hLAp
  have hQp := commutator_subgroupOf_of_le_of_perfect map_conj_subsystemGroup_setA_le_adjointGroup
    (by rw [← Subgroup.map_commutator, hLAp])
  have hsurj : Function.Surjective ε.toMonoidHom := ε.surjective
  rw [eq_top_iff, ← Subgroup.map_top_of_surjective _ hsurj, ← subgroupOf_setA_sup_eq_top,
    Subgroup.map_sup]
  exact sup_le_sup
    (map_le_perfectCore_centralizer_map hPp (subgroupOf_setA_le_centralizer h2 ι hAJ) ε)
    (map_le_perfectCore_centralizer_map hQp (subgroupOf_map_setA_le_centralizer h2 ι hAJ) ε)

end Model

section Residue


variable {K : Type} [Field K]

theorem fixed_and_inv_of_card_four [Finite K] (hK : Nat.card K = (2 ^ 1) ^ 2) {σ : K →+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ 1) :
    (∀ c : K, σ c = c → c = 0 ∨ c = 1) ∧ ∀ u : Kˣ, σ (u : K) * (u : K) = 1 := by
  refine ⟨fun c hc => ?_, fun u => ?_⟩
  · rw [hσ, pow_one, sq] at hc
    by_cases h0 : c = 0
    · exact Or.inl h0
    · exact Or.inr (mul_left_cancel₀ h0 (hc.trans (mul_one c).symm))
  · have : Fintype K := Fintype.ofFinite K
    have hcard : Fintype.card K = 4 := by rw [← Nat.card_eq_fintype_card, hK]; norm_num
    have h := FiniteField.pow_card_sub_one_eq_one (u : K) u.ne_zero
    rw [hcard] at h
    rw [hσ]
    calc (u : K) ^ 2 ^ 1 * (u : K) = (u : K) ^ (4 - 1) := by ring
      _ = 1 := h

theorem prod_zpow_six_eq_one {M : Type*} [CommGroup M] (a : Fin 6 → M) (γ : Fin 6 → ℤ)
    (h1 : a 1 = 1) (h3 : a 3 = 1) (h4 : a 4 = (a 2)⁻¹) (h5 : a 5 = (a 0)⁻¹)
    (h05 : γ 0 = γ 5) (h24 : γ 2 = γ 4) : ∏ i, a i ^ γ i = 1 := by
  rw [Fin.prod_univ_six, h1, h3, h4, h5, ← h05, ← h24, one_zpow, one_zpow, inv_zpow', inv_zpow']
  group

theorem rootChar_compatDiag_eq_one_two [Finite K] (hK : Nat.card K = (2 ^ 1) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (2 ^ 1))
    (u : (a : Fin TwistTag.E6.foldedTag.rank) → (orbitField TwistTag.E6 K σ.toRingHom a)ˣ)
    {γ : Fin TwistTag.E6.tag.rank → ℤ} (h05 : γ 0 = γ 5) (h24 : γ 2 = γ 4) :
    LocalAnalysis.ComponentInitial.FourGroupChevalley.rootChar
      (compatDiag TwistTag.E6 σ.toRingHom u) γ = 1 := by
  obtain ⟨-, -, h3, h4, h5, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form Nat.prime_two le_rfl K hK σ hσ
  obtain ⟨hfix, hσu⟩ := fixed_and_inv_of_card_four hK (σ := σ.toRingHom) hσ
  have hone : ∀ (a : Fin TwistTag.E6.foldedTag.rank),
      (∀ c, c ∈ orbitField TwistTag.E6 K σ.toRingHom a ↔ σ c = c) →
      orbitFieldUnit TwistTag.E6 σ.toRingHom (u a) = 1 := by
    intro a ha
    apply Units.ext
    rw [coe_orbitFieldUnit, Units.val_one]
    have hσa := (ha _).1 ((u a : orbitField TwistTag.E6 K σ.toRingHom a)).2
    rcases hfix _ hσa with h | h
    · exact absurd h (Units.ne_zero (orbitFieldUnit TwistTag.E6 σ.toRingHom (u a)))
    · exact h
  have hinv : ∀ v : Kˣ, (Units.map (σ.toRingHom : K →* K)) v = v⁻¹ := by
    intro v
    rw [eq_inv_iff_mul_eq_one]
    apply Units.ext
    rw [Units.val_mul, Units.val_one]
    exact hσu v
  rw [h5]
  exact prod_zpow_six_eq_one _ γ (hone _ h4) (hone _ h3) (hinv _) (hinv _) h05 h24

theorem compatDiag_fieldActor_fix_two [Finite K] (hK : Nat.card K = (2 ^ 1) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (2 ^ 1))
    (u : (a : Fin TwistTag.E6.foldedTag.rank) → (orbitField TwistTag.E6 K σ.toRingHom a)ˣ)
    (δ₀ : K ≃+* K) {γ : Fin TwistTag.E6.tag.rank → ℤ} (hγ : IsRoot TwistTag.E6.tag γ)
    (h05 : γ 0 = γ 5) (h24 : γ 2 = γ 4) {c : K} (hc : σ c = c) (x : twistedE6RootGroup K σ)
    (hx : (x : ModGL TwistTag.E6.tag K) = pinnedX TwistTag.E6.tag K γ c) :
    (compatDiagAutHom TwistTag.E6 K σ.toRingHom u * fieldActor σ δ₀ :
      MulAut (twistedE6RootGroup K σ)) x = x := by
  obtain ⟨-, -, -, -, -, hΔ, hδ0, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form Nat.prime_two le_rfl K hK σ hσ
  obtain ⟨hfix, -⟩ := fixed_and_inv_of_card_four hK (σ := σ.toRingHom) hσ
  have hδc : δ₀.toRingHom c = c := by
    show δ₀ c = c
    rcases hfix c hc with rfl | rfl
    · exact map_zero δ₀
    · exact map_one δ₀
  apply Subtype.ext
  rw [MulAut.mul_apply, hΔ, hδ0, hx, units_map_entrywiseHom_pinnedX', hδc,
    rootDiagUnit_conj_pinnedX _ hγ, rootChar_compatDiag_eq_one_two hK σ hσ u h05 h24,
    Units.val_one, one_mul]

theorem relWordXPrime_highestRoot_check :
    twistedE6RelAct relWordXPrime e6HighestRoot = twistedE6ClassRootB ∧
      twistedE6RelAct relWordXPrime (-e6HighestRoot) = -twistedE6ClassRootB ∧
      e6HighestRoot 0 = e6HighestRoot 5 ∧ e6HighestRoot 2 = e6HighestRoot 4 ∧
      (-e6HighestRoot) 0 = (-e6HighestRoot) 5 ∧ (-e6HighestRoot) 2 = (-e6HighestRoot) 4 ∧
      twistedE6ClassRootB 0 = twistedE6ClassRootB 5 ∧
      twistedE6ClassRootB 2 = twistedE6ClassRootB 4 ∧
      (-twistedE6ClassRootB) 0 = (-twistedE6ClassRootB) 5 ∧
      (-twistedE6ClassRootB) 2 = (-twistedE6ClassRootB) 4 ∧
      permLattice TwistTag.E6.perm (-e6HighestRoot) = -e6HighestRoot := by
  decide +kernel

theorem exists_conj_eq_on_thetaRankOneGroup_two {k : Type} [Field k] [Algebra k K]
    (hk : Nat.card k = 2 ^ 1) (hK : Nat.card K = (2 ^ 1) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (2 ^ 1)) (δ : MulAut (twistedE6RootGroup K σ)) :
    ∃ g : twistedE6RootGroup K σ, ∀ x : twistedE6RootGroup K σ,
      ((x : ModGL TwistTag.E6.tag K) ∈ thetaRankOneGroup (algebraMap k K) ∨
        (x : ModGL TwistTag.E6.tag K) ∈ (thetaRankOneGroup (algebraMap k K)).map
          (MulAut.conj (twistedE6RelWeyl K relWordXPrime)).toMonoidHom) →
      δ x = g * x * g⁻¹ := by
  have := finite_of_card hK
  have : Finite k := F4Pilot.finite_of_natCard_eq_two_pow hk
  have : CharP K 2 := charP_two_of_card le_rfl hK
  obtain ⟨-, -, -, -, -, -, -, hNF, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form Nat.prime_two le_rfl K hK σ hσ
  obtain ⟨g, u, δ₀, hδ⟩ := hNF δ
  set ν : MulAut (twistedE6RootGroup K σ) :=
    compatDiagAutHom TwistTag.E6 K σ.toRingHom u * fieldActor σ δ₀ with hνdef
  set H : Subgroup (twistedE6RootGroup K σ) :=
    MonoidHom.eqLocus ν.toMonoidHom (MonoidHom.id _) with hH
  obtain ⟨hθβ, hθβ', h1, h2, h3, h4, h5, h6, h7, h8, hρθ'⟩ := relWordXPrime_highestRoot_check
  have hσι : ∀ c : k, σ (algebraMap k K c) = algebraMap k K c := fun c =>
    (sigma_eq_self_iff (σ := σ.toRingHom) hk hσ _).2 ⟨c, rfl⟩
  have hθ : IsRoot TwistTag.E6.tag e6HighestRoot := isRoot_e6HighestRoot
  have hβ : IsRoot TwistTag.E6.tag twistedE6ClassRootB := isRoot_twistedE6ClassRoots.2.2.2.2
  have hgen : ∀ {γ : Fin TwistTag.E6.tag.rank → ℤ}, IsRoot TwistTag.E6.tag γ →
      γ 0 = γ 5 → γ 2 = γ 4 → ∀ (c : k)
        (hm : pinnedX TwistTag.E6.tag K γ (algebraMap k K c) ∈ twistedE6RootGroup K σ),
      pinnedX TwistTag.E6.tag K γ (algebraMap k K c) ∈ H.map (twistedE6RootGroup K σ).subtype := by
    intro γ hγ h05 h24 c hm
    exact ⟨⟨_, hm⟩, compatDiag_fieldActor_fix_two hK σ hσ u δ₀ hγ h05 h24 (hσι c) _ rfl, rfl⟩
  have hJC := thetaRankOneGroup_le_C0 (k := k) le_rfl hk hK (σ := σ.toRingHom) hσ
  have hθmem : ∀ c : k, pinnedX TwistTag.E6.tag K e6HighestRoot (algebraMap k K c) ∈
      twistedE6RootGroup K σ := fun c =>
    hJC (Subgroup.mem_sup_left (Subgroup.subset_closure ⟨c, rfl⟩))
  have hθmem' : ∀ c : k, pinnedX TwistTag.E6.tag K (-e6HighestRoot) (algebraMap k K c) ∈
      twistedE6RootGroup K σ := fun c =>
    hJC (Subgroup.mem_sup_right (Subgroup.subset_closure ⟨c, rfl⟩))
  have hnC : twistedE6RelWeyl K relWordXPrime ∈ twistedE6RootGroup K σ :=
    twistedE6RelWeyl_mem _ relWordXPrime
  have hJH : thetaRankOneGroup (algebraMap k K) ≤ H.map (twistedE6RootGroup K σ).subtype := by
    refine sup_le ((Subgroup.closure_le _).2 ?_) ((Subgroup.closure_le _).2 ?_)
    · rintro _ ⟨c, rfl⟩
      exact hgen hθ h1 h2 c (hθmem c)
    · rintro _ ⟨c, rfl⟩
      exact hgen (CFSG.LieType.Chevalley.IsRoot.neg hθ) h3 h4 c (hθmem' c)
  have hnJH : (thetaRankOneGroup (algebraMap k K)).map
      (MulAut.conj (twistedE6RelWeyl K relWordXPrime)).toMonoidHom ≤
        H.map (twistedE6RootGroup K σ).subtype := by
    rw [Subgroup.map_le_iff_le_comap]
    refine sup_le ((Subgroup.closure_le _).2 ?_) ((Subgroup.closure_le _).2 ?_)
    · rintro _ ⟨c, rfl⟩
      have e := twistedE6RelWeyl_conj_pinnedX relWordXPrime hθ (algebraMap k K c)
      rw [hθβ] at e
      rw [SetLike.mem_coe, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, e]
      refine hgen hβ h5 h6 c ?_
      rw [← e]
      exact mul_mem (mul_mem hnC (hθmem c)) (inv_mem hnC)
    · rintro _ ⟨c, rfl⟩
      have e := twistedE6RelWeyl_conj_pinnedX relWordXPrime
        (CFSG.LieType.Chevalley.IsRoot.neg hθ) (algebraMap k K c)
      rw [hθβ'] at e
      rw [SetLike.mem_coe, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, e]
      refine hgen (CFSG.LieType.Chevalley.IsRoot.neg hβ) h7 h8 c ?_
      rw [← e]
      exact mul_mem (mul_mem hnC (hθmem' c)) (inv_mem hnC)
  refine ⟨g, fun x hx => ?_⟩
  have hxH : (x : ModGL TwistTag.E6.tag K) ∈ H.map (twistedE6RootGroup K σ).subtype :=
    hx.elim (fun h => hJH h) (fun h => hnJH h)
  obtain ⟨y, hyH, hyx⟩ := hxH
  have hyx' : y = x := Subtype.ext hyx
  subst hyx'
  have hν : ν y = y := hyH
  have hδy : δ y = MulAut.conj g (ν y) := by
    rw [hδ, hνdef, mul_assoc]
    rfl
  rw [hδy, hν, MulAut.conj_apply]

end Residue

section Step3


variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem exists_quotient_mulEquiv_eq_mulAut_twistedE6 (hset : StandardSetting G L) {f : ℕ}
    {K : Type} [Field K] (hK : Nat.card K = (2 ^ f) ^ 2) (σE : K ≃+* K)
    (hσ : ∀ c, σE.toRingHom c = c ^ 2 ^ f)
    (e : L ≃* graphFixedRootGroup TwistTag.E6 K σE.toRingHom) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) {M : Subgroup G}
    (hMp : ⁅M, M⁆ = M) (hZ : Odd (Nat.card (center M)))
    (eM : M ⧸ center M ≃* adjointGroup .E6 K) (htM : t ∈ normalizer (M : Set G)) :
    ∃ (hLM : L ≤ M) (ψ : M ⧸ center M ≃* adjointGroup TwistTag.E6.tag K)
      (δ : MulAut (graphFixedRootGroup TwistTag.E6 K σE.toRingHom)),
      ∀ x : graphFixedRootGroup TwistTag.E6 K σE.toRingHom,
        ((ψ (QuotientGroup.mk ⟨((e.symm x : L) : G), hLM (e.symm x).2⟩) :
          adjointGroup TwistTag.E6.tag K) : ModGL TwistTag.E6.tag K) =
          ((δ x : graphFixedRootGroup TwistTag.E6 K σE.toRingHom) : ModGL TwistTag.E6.tag K) := by
  have hf := one_le_of_card_sq_twistedE6 hK
  have := finite_of_card hK
  have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
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
  refine ⟨hLM, ψ, MulEquiv.ofBijective F₁ (Finite.injective_iff_bijective.1 hF₁inj),
    fun x => rfl⟩


theorem nonsplitPair_le_C0 {k K : Type} [Field k] [Field K] [Algebra k K]
    (hk : Nat.card k = 2 ^ 1) (hK : Nat.card K = (2 ^ 1) ^ 2) {σ : K →+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ 1) {A : Subgroup (ModGL TwistTag.E6.tag K)}
    (hAJ : A ≤ thetaRankOneGroup (algebraMap k K)) (b : Bool) :
    cond b A (A.map (MulAut.conj (twistedE6RelWeyl K relWordXPrime)).toMonoidHom) ≤
      graphFixedRootGroup TwistTag.E6 K σ := by
  have : Finite k := F4Pilot.finite_of_natCard_eq_two_pow hk
  have hJC := thetaRankOneGroup_le_C0 (k := k) le_rfl hk hK hσ
  have hnC : twistedE6RelWeyl K relWordXPrime ∈ graphFixedRootGroup TwistTag.E6 K σ :=
    twistedE6RelWeyl_mem _ relWordXPrime
  cases b
  · rintro _ ⟨y, hy, rfl⟩
    exact mul_mem (mul_mem hnC (hJC (hAJ hy))) (inv_mem hnC)
  · exact hAJ.trans hJC

theorem le_iSup_perfectCore_of_mem_normalizer_twistedE6_two (hset : StandardSetting G L)
    {k K : Type} [Field k] [Field K] [Algebra k K] (hk : Nat.card k = 2 ^ 1)
    (hK : Nat.card K = (2 ^ 1) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ 1)
    (e : L ≃* graphFixedRootGroup TwistTag.E6 K σ) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {A : Subgroup (ModGL TwistTag.E6.tag K)} (hAJ : A ≤ thetaRankOneGroup (algebraMap k K))
    {M : Subgroup G} (hMp : ⁅M, M⁆ = M) (hZ : Odd (Nat.card (center M)))
    (eM : M ⧸ center M ≃* adjointGroup .E6 K) (htM : t ∈ normalizer (M : Set G)) :
    M ≤ ⨆ b : Bool, perfectCore (M ⊓ centralizer (modelToG e (cond b A
      (A.map (MulAut.conj (twistedE6RelWeyl K relWordXPrime)).toMonoidHom)) : Set G)) := by
  have := finite_of_card hK
  have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  have : CharP K 2 := charP_two_of_card le_rfl hK
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  obtain ⟨σE, rfl⟩ := exists_ringEquiv_toRingHom_eq σ
  obtain ⟨hLM, ψ, δ, hψδ⟩ :=
    exists_quotient_mulEquiv_eq_mulAut_twistedE6 hset hK σE hσ e ht hKt hMp hZ eM htM
  obtain ⟨g, hg⟩ := exists_conj_eq_on_thetaRankOneGroup_two hk hK σE hσ δ
  have hC₀C : graphFixedRootGroup TwistTag.E6 K σE.toRingHom ≤ adjointGroup TwistTag.E6.tag K :=
    graphFixedRootGroup_le_adjointGroup' _
  set g' : adjointGroup TwistTag.E6.tag K := ⟨(g : ModGL TwistTag.E6.tag K), hC₀C g.2⟩ with hg'
  set n := twistedE6RelWeyl K relWordXPrime with hndef
  set T : Bool → Subgroup (ModGL TwistTag.E6.tag K) :=
    fun b => cond b A (A.map (MulAut.conj n).toMonoidHom) with hTdef
  have hTC : ∀ b, T b ≤ graphFixedRootGroup TwistTag.E6 K σE.toRingHom :=
    nonsplitPair_le_C0 hk hK hσ hAJ
  have hTJ : ∀ b, ∀ x ∈ T b, x ∈ thetaRankOneGroup (algebraMap k K) ∨
      x ∈ (thetaRankOneGroup (algebraMap k K)).map (MulAut.conj n).toMonoidHom := by
    intro b x hx
    cases b
    · exact Or.inr (Subgroup.map_mono hAJ hx)
    · exact Or.inl (hAJ hx)
  set π : M →* adjointGroup TwistTag.E6.tag K :=
    ψ.toMonoidHom.comp (QuotientGroup.mk' (center M)) with hπdef
  have hkey : ∀ b : Bool, ((modelToG e (T b)).subgroupOf M).map π =
      ((T b).subgroupOf (adjointGroup TwistTag.E6.tag K)).map (MulAut.conj g').toMonoidHom := by
    intro b
    ext y
    constructor
    · rintro ⟨m, hm, rfl⟩
      obtain ⟨x, hxT, hxm⟩ := (mem_modelToG e).1 (mem_subgroupOf.1 hm)
      have hmx : m = ⟨(e.symm x : G), hLM (e.symm x).2⟩ := Subtype.ext hxm.symm
      refine ⟨⟨(x : ModGL TwistTag.E6.tag K), hC₀C x.2⟩, mem_subgroupOf.2 hxT, Subtype.ext ?_⟩
      rw [hmx]
      change _ = ((ψ (QuotientGroup.mk ⟨((e.symm x : L) : G), hLM (e.symm x).2⟩) :
        adjointGroup TwistTag.E6.tag K) : ModGL TwistTag.E6.tag K)
      rw [hψδ x, hg x (hTJ b _ hxT)]
      rfl
    · rintro ⟨z, hz, rfl⟩
      have hzT : (z : ModGL TwistTag.E6.tag K) ∈ T b := mem_subgroupOf.1 hz
      set x : graphFixedRootGroup TwistTag.E6 K σE.toRingHom := ⟨(z : ModGL TwistTag.E6.tag K),
        hTC b hzT⟩ with hx
      refine ⟨⟨(e.symm x : G), hLM (e.symm x).2⟩,
        mem_subgroupOf.2 (symm_mem_modelToG e hzT), Subtype.ext ?_⟩
      change ((ψ (QuotientGroup.mk ⟨((e.symm x : L) : G), hLM (e.symm x).2⟩) :
        adjointGroup TwistTag.E6.tag K) : ModGL TwistTag.E6.tag K) = _
      rw [hψδ x, hg x (hTJ b _ hzT)]
      rfl
  have hgen : ⨆ b : Bool, perfectCore (centralizer ((((modelToG e (T b)).subgroupOf M).map
      (ψ.toMonoidHom.comp (QuotientGroup.mk' (center M))) :
        Subgroup (adjointGroup TwistTag.E6.tag K)) : Set (adjointGroup TwistTag.E6.tag K))) =
      ⊤ := by
    have h := perfectCore_sup_perfectCore_centralizer_nonsplitPair_eq_top h2 (algebraMap k K)
      hAJ (MulAut.conj g')
    rw [iSup_bool_eq]
    rw [← hπdef, hkey true, hkey false]
    exact h
  exact le_iSup_perfectCore_of_quotient_mulEquiv hMp ψ (fun b => modelToG e (T b))
    (fun b => (modelToG_le e _).trans hLM) hgen

theorem unique_of_fieldRow_twistedE6_two (hset : StandardSetting G L) {k K : Type} [Field k]
    [Field K] [Algebra k K] (hk : Nat.card k = 2 ^ 1) (hK : Nat.card K = (2 ^ 1) ^ 2)
    {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ 1) (e : L ≃* graphFixedRootGroup TwistTag.E6 K σ)
    {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {A : Subgroup (ModGL TwistTag.E6.tag K)} (hAJ : A ≤ thetaRankOneGroup (algebraMap k K))
    {G₀ : Subgroup G} (hG₀p : ⁅G₀, G₀⁆ = G₀) (hZ : Odd (Nat.card (center G₀)))
    (Ψ : G₀ ⧸ center G₀ ≃* adjointGroup .E6 K) (hLG₀ : L ≤ G₀)
    (hX : centralizerPerfectCore (modelToG e A) ≤ G₀) :
    ∀ g : G, g⁻¹ * t * g ∈ normalizer (G₀ : Set G) → g ∈ normalizer (G₀ : Set G) := by
  have hnC : twistedE6RelWeyl K relWordXPrime ∈ graphFixedRootGroup TwistTag.E6 K σ :=
    twistedE6RelWeyl_mem _ relWordXPrime
  set n : graphFixedRootGroup TwistTag.E6 K σ := ⟨twistedE6RelWeyl K relWordXPrime, hnC⟩ with hndef
  have hX' : centralizerPerfectCore (modelToG e
      (A.map (MulAut.conj (twistedE6RelWeyl K relWordXPrime)).toMonoidHom)) ≤ G₀ := by
    have h1 : modelToG e (A.map (MulAut.conj (twistedE6RelWeyl K relWordXPrime)).toMonoidHom) =
        (modelToG e A).map (MulAut.conj ((e.symm n : L) : G)).toMonoidHom :=
      modelToG_map_conj e A n
    rw [h1, ← F4Pilot.map_centralizerPerfectCore]
    rintro _ ⟨y, hy, rfl⟩
    have hn := hLG₀ (e.symm n).2
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact mul_mem (mul_mem hn (hX hy)) (inv_mem hn)
  refine F4Pilot.unique_of_forall_conjugate_generation
    (J := fun b : Bool => modelToG e (cond b A
      (A.map (MulAut.conj (twistedE6RelWeyl K relWordXPrime)).toMonoidHom)))
    (fun b => by cases b <;> assumption) (fun h htM => ?_)
  exact le_iSup_perfectCore_of_mem_normalizer_twistedE6_two hset hk hK hσ e ht hKt hAJ
    (E6Pilot.commutator_conjugate_eq hG₀p h) (by rw [E6Pilot.card_center_conjugate]; exact hZ)
    ((E6Pilot.coverConjugateQuotientCenterEquiv G₀ h).symm.trans Ψ) htM

end Step3

section Model2


variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem false_of_fieldModel_twistedE6_two (hset : SeitzSetting G L) {k K : Type} [Field k]
    [Field K] [Algebra k K] (hk : Nat.card k = 2 ^ 1) (hK : Nat.card K = (2 ^ 1) ^ 2)
    {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ 1) (e : L ≃* graphFixedRootGroup TwistTag.E6 K σ)
    {t : G} (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    {A : Subgroup (ModGL TwistTag.E6.tag K)} (hAJ : A ≤ thetaRankOneGroup (algebraMap k K))
    {G₀ : Subgroup G} (hG₀p : ⁅G₀, G₀⁆ = G₀) (hZ : Odd (Nat.card (center G₀)))
    (Ψ : G₀ ⧸ center G₀ ≃* adjointGroup .E6 K) (htN : t ∈ normalizer (G₀ : Set G))
    (hX : centralizerPerfectCore (modelToG e A) ≤ G₀) : False := by
  have hKt := inf_centralizer_eq_zpowers_twistedE6 hset le_rfl hK hσ e htC ht
  have hLG₀ := le_of_fieldModel_twistedE6 hset le_rfl hK hσ e htC ht hG₀p hZ hK Ψ htN
  exact false_of_fieldModel_twistedE6 hset le_rfl hK hσ e htC ht hG₀p hZ hK Ψ htN
    (unique_of_fieldRow_twistedE6_two hset.standardSetting hk hK hσ e ht hKt hAJ hG₀p hZ Ψ hLG₀ hX)

end Model2

end CFSG.SeitzReduction.TwistedE6Pilot
