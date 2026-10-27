module

public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotSwapPair

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.TwistedE6Pilot

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.E6GraphLevi
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)


theorem not_ordTwistedA_five_two_dvd_ordF4_two :
    ¬ ordTwistedA 5 (2 ^ 1) ∣ CFSG.Open.ordF4 (2 ^ 1) := by
  rw [ordTwistedA_five_two_eq]
  norm_num [CFSG.Open.ordF4]

section Rigidity

variable {f : ℕ} {k K : Type} [Field k] [Field K] [Algebra k K]

theorem centralizer_nonsplit_subgroupOf (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f)
    {X : Subgroup (ModGL TwistTag.E6.tag K)} (hXJ : X ≤ thetaRankOneGroup (algebraMap k K))
    (hX : Nat.card X = 2 ^ f + 1) (hcyc : IsCyclic X) :
    centralizer (X.subgroupOf (graphFixedRootGroup TwistTag.E6 K σ) :
        Set (graphFixedRootGroup TwistTag.E6 K σ)) =
      X.subgroupOf (graphFixedRootGroup TwistTag.E6 K σ) ⊔
        (su6Levi σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ) := by
  obtain ⟨hcen, -, -, hXC⟩ := centralizer_nonsplit_twistedE6 hf hk hK hσ hXJ hX hcyc
  exact centralizer_subgroupOf_eq_sup hXC hXC (su6Levi_le_graphFixedRootGroup σ) hcen

theorem mem_of_conj_fix_nonsplit (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f)
    {X : Subgroup (ModGL TwistTag.E6.tag K)} (hXJ : X ≤ thetaRankOneGroup (algebraMap k K))
    (hX : Nat.card X = 2 ^ f + 1) (hcyc : IsCyclic X) {x : graphFixedRootGroup TwistTag.E6 K σ}
    (hxX : ∀ a ∈ X.subgroupOf (graphFixedRootGroup TwistTag.E6 K σ), x * a * x⁻¹ = a)
    (hxD : ∀ y ∈ (su6Levi σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ),
      x * y * x⁻¹ = y) :
    x ∈ X.subgroupOf (graphFixedRootGroup TwistTag.E6 K σ) := by
  obtain ⟨-, -, hXD, -⟩ := centralizer_nonsplit_twistedE6 hf hk hK hσ hXJ hX hcyc
  obtain ⟨hDs, hDp, -⟩ := su6Levi_subgroupOf_facts hf hk hK hσ
  set D' := (su6Levi σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ) with hD'
  set A' := X.subgroupOf (graphFixedRootGroup TwistTag.E6 K σ) with hA'
  have hAD : A' ≤ centralizer (D' : Set (graphFixedRootGroup TwistTag.E6 K σ)) :=
    subgroupOf_le_centralizer_subgroupOf hXD
  have hxc : x ∈ centralizer (A' : Set (graphFixedRootGroup TwistTag.E6 K σ)) := by
    rw [mem_centralizer_iff]
    intro a ha
    calc a * x = x * a * x⁻¹ * x := by rw [hxX a ha]
      _ = x * a := by group
  rw [centralizer_nonsplit_subgroupOf hf hk hK hσ hXJ hX hcyc] at hxc
  have hAN : A' ≤ normalizer (D' : Set (graphFixedRootGroup TwistTag.E6 K σ)) :=
    hAD.trans (centralizer_le_normalizer _)
  have hxc' : x ∈ ((A' ⊔ D' : Subgroup _) : Set (graphFixedRootGroup TwistTag.E6 K σ)) := hxc
  rw [coe_mul_of_left_le_normalizer_right _ _ hAN] at hxc'
  obtain ⟨a, ha, d, hd, rfl⟩ := Set.mem_mul.1 hxc'
  have hdc : (⟨d, hd⟩ : D') ∈ center D' := by
    rw [mem_center_iff]
    intro y
    apply Subtype.ext
    have h1 := hxD y y.2
    have h2 : a * y = y * a := (mem_centralizer_iff.1 (hAD ha) y y.2).symm
    change (y : graphFixedRootGroup TwistTag.E6 K σ) * d = d * y
    have h3 : d * (y : graphFixedRootGroup TwistTag.E6 K σ) * d⁻¹ = y :=
      calc d * (y : graphFixedRootGroup TwistTag.E6 K σ) * d⁻¹ =
          a⁻¹ * (a * d * y * (a * d)⁻¹) * a := by group
        _ = a⁻¹ * y * a := by rw [h1]
        _ = a⁻¹ * (a * y) := by rw [mul_assoc, ← h2]
        _ = y := by group
    calc (y : graphFixedRootGroup TwistTag.E6 K σ) * d =
        d * y * d⁻¹ * d := by rw [h3]
      _ = d * y := by group
  rw [center_eq_bot_of_isSimpleGroup_of_isPerfect, mem_bot] at hdc
  have hd1 : d = 1 := congrArg Subtype.val hdc
  rw [hd1, mul_one]
  exact ha

theorem card_su6Levi_dvd_card_fixedSubgroup {σ : K →+* K}
    (β : MulAut (graphFixedRootGroup TwistTag.E6 K σ))
    (hβD : ∀ x ∈ (su6Levi σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ), β x = x) :
    Nat.card (su6Levi σ) ∣ Nat.card (fixedSubgroup β) := by
  have hle : (su6Levi σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ) ≤ fixedSubgroup β :=
    fun x hx => swapMem_fixedSubgroup_iff.2 (hβD x hx)
  rw [← Nat.card_congr (subgroupOfEquivOfLe (su6Levi_le_graphFixedRootGroup σ)).toEquiv]
  exact Subgroup.card_dvd_of_le hle

theorem eq_one_of_mul_self_of_fix_nonsplit_two (hk : Nat.card k = 2 ^ 1)
    (hK : Nat.card K = (2 ^ 1) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ 1)
    {X : Subgroup (ModGL TwistTag.E6.tag K)} (hXJ : X ≤ thetaRankOneGroup (algebraMap k K))
    (hX : Nat.card X = 2 ^ 1 + 1) (hcyc : IsCyclic X)
    (β : MulAut (graphFixedRootGroup TwistTag.E6 K σ)) (hβ : β * β = 1)
    (hβX : ∀ x ∈ X.subgroupOf (graphFixedRootGroup TwistTag.E6 K σ), β x = x)
    (hβD : ∀ x ∈ (su6Levi σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ), β x = x) :
    β = 1 := by
  have hf : 1 ≤ 1 := le_rfl
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; positivity)
  have := finite_of_card hK
  have : CharP K 2 := charP_two_of_card hf hK
  have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  have hZ : center (graphFixedRootGroup TwistTag.E6 K σ) = ⊥ :=
    center_graphFixedRootGroup_eq_bot (Finite.surjective_of_injective σ.injective)
  by_cases hin : β ∈ (MulAut.conj : graphFixedRootGroup TwistTag.E6 K σ →*
      MulAut (graphFixedRootGroup TwistTag.E6 K σ)).range
  · obtain ⟨x, rfl⟩ := hin
    have hx2 : x * x = 1 := by
      have hc : x * x ∈ center (graphFixedRootGroup TwistTag.E6 K σ) := by
        rw [mem_center_iff]
        intro g
        have h := congrArg (fun φ : MulAut (graphFixedRootGroup TwistTag.E6 K σ) => φ g) hβ
        simp only [MulAut.mul_apply, MulAut.conj_apply, MulAut.one_apply] at h
        calc g * (x * x) = x * (x * g * x⁻¹) * x⁻¹ * (x * x) := by rw [h]
          _ = x * x * g := by group
      rw [hZ, mem_bot] at hc
      exact hc
    have hxA := mem_of_conj_fix_nonsplit hf hk hK hσ hXJ hX hcyc
      (fun a ha => by rw [← MulAut.conj_apply]; exact hβX a ha)
      (fun y hy => by rw [← MulAut.conj_apply]; exact hβD y hy)
    have h3 : x ^ 3 = 1 := by
      have h : (⟨x, hxA⟩ : X.subgroupOf (graphFixedRootGroup TwistTag.E6 K σ)) ^
          Nat.card (X.subgroupOf (graphFixedRootGroup TwistTag.E6 K σ)) = 1 := pow_card_eq_one'
      have hcard : Nat.card (X.subgroupOf (graphFixedRootGroup TwistTag.E6 K σ)) = 3 := by
        rw [Nat.card_congr (subgroupOfEquivOfLe
          (centralizer_nonsplit_twistedE6 hf hk hK hσ hXJ hX hcyc).2.2.2).toEquiv, hX]
        norm_num
      rw [hcard] at h
      exact congrArg Subtype.val h
    have hx1 : x = 1 := by
      calc x = x ^ 3 * (x * x)⁻¹ := by group
        _ = 1 := by rw [h3, hx2, inv_one, mul_one]
    rw [hx1, map_one]
  · exfalso
    have hdvd : Nat.card (fixedSubgroup β) ∣ Nat.card (adjointGroup Tag.F4 k) := by
      have key : ∀ β₀ : MulAut (graphFixedRootGroup TwistTag.E6 K σ),
          (∃ φ : MulAut (graphFixedRootGroup TwistTag.E6 K σ), φ * β * φ⁻¹ = β₀) →
          Nat.card (fixedSubgroup β₀) ∣ Nat.card (adjointGroup Tag.F4 k) →
          Nat.card (fixedSubgroup β) ∣ Nat.card (adjointGroup Tag.F4 k) := by
        rintro β₀ ⟨φ, rfl⟩ h
        rwa [swapFixedSubgroup_conj, Subgroup.card_map_of_injective φ.injective] at h
      rcases (conj_etaAut_or_xiAut_of_outer hf hK σ hσ).1 β (by rw [sq]; exact hβ) hin with
        h | h
      · refine key _ h ?_
        change Nat.card ((etaAut σ (apply_apply_eq hK hσ)).toMonoidHom.eqLocus
          (MonoidHom.id (graphFixedRootGroup TwistTag.E6 K σ))) ∣ _
        rw [card_eqLocus_etaAut hf hk hK σ hσ]
      · refine key _ h ?_
        obtain ⟨ψ, h', hψ, hF, -⟩ := exists_eqLocus_xiAut_eq_map hf hk hK σ hσ
        change Nat.card ((xiAut σ (apply_apply_eq hK hσ)).toMonoidHom.eqLocus
          (MonoidHom.id (graphFixedRootGroup TwistTag.E6 K σ))) ∣ _
        rw [hF, Subgroup.card_map_of_injective hψ]
        exact Subgroup.card_subgroup_dvd_card _
    have hD := (card_su6Levi_dvd_card_fixedSubgroup β hβD).trans hdvd
    rw [card_of_lieModel_PSU_six_two (lieModel_su6Levi hf hk hK hσ),
      CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_F4, hk] at hD
    exact not_ordTwistedA_five_two_dvd_ordF4_two hD

theorem eq_one_of_fix_nonsplit_two (hk : Nat.card k = 2 ^ 1)
    (hK : Nat.card K = (2 ^ 1) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ 1)
    {X : Subgroup (ModGL TwistTag.E6.tag K)} (hXJ : X ≤ thetaRankOneGroup (algebraMap k K))
    (hX : Nat.card X = 2 ^ 1 + 1) (hcyc : IsCyclic X)
    (β : MulAut (graphFixedRootGroup TwistTag.E6 K σ))
    (hβX : ∀ x ∈ X.subgroupOf (graphFixedRootGroup TwistTag.E6 K σ), β x = x)
    (hβD : ∀ x ∈ (su6Levi σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ), β x = x)
    (n : ℕ) (hβn : β ^ 2 ^ n = 1) : β = 1 := by
  induction n generalizing β with
  | zero => simpa using hβn
  | succ n ih =>
    have h2 : β * β = 1 := by
      refine ih (β * β) (fun x hx => by rw [MulAut.mul_apply, hβX x hx, hβX x hx])
        (fun x hx => by rw [MulAut.mul_apply, hβD x hx, hβD x hx]) ?_
      rw [← sq, ← pow_mul, ← pow_succ']
      exact hβn
    exact eq_one_of_mul_self_of_fix_nonsplit_two hk hK hσ hXJ hX hcyc β h2 hβX hβD

end Rigidity

section Setting

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {k K : Type} [Field k] [Field K]
  [Algebra k K]

theorem neighbour_layer_2E6_nonsplit_two (hk : Nat.card k = 2 ^ 1)
    (hK : Nat.card K = (2 ^ 1) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ 1)
    (e : L ≃* graphFixedRootGroup TwistTag.E6 K σ) {A : Subgroup (ModGL TwistTag.E6.tag K)}
    (hAJ : A ≤ thetaRankOneGroup (algebraMap k K)) (hA : Nat.card A = 2 ^ 1 + 1)
    (hcyc : IsCyclic A) {X : Subgroup G}
    (hX : X = ((A.subgroupOf (graphFixedRootGroup TwistTag.E6 K σ)).map
      e.symm.toMonoidHom).map L.subtype)
    {D : Subgroup G} (hDe : D = (((su6Levi σ).subgroupOf
      (graphFixedRootGroup TwistTag.E6 K σ)).map e.symm.toMonoidHom).map L.subtype) :
    D = inSubgroup layer (L ⊓ centralizer (X : Set G)) ∧ CFSG.IsQuasisimple D := by
  have hf : 1 ≤ 1 := le_rfl
  obtain ⟨-, -, hXD, -⟩ := centralizer_nonsplit_twistedE6 hf hk hK hσ hAJ hA hcyc
  obtain ⟨x, -, rfl⟩ := exists_eq_zpowers_of_isCyclic hcyc
  subst hX hDe
  exact ⟨(F4Pilot.inSubgroup_layer_inf_centralizer_map_symm e
      (centralizer_nonsplit_subgroupOf hf hk hK hσ hAJ hA hcyc)
      (subgroupOf_le_centralizer_subgroupOf hXD)
      (subgroupOf_le_centralizer_subgroupOf (zpowers_le_centralizer_zpowers x))
      (isQuasisimple_su6Levi_subgroupOf hf hk hK hσ)).symm,
    isQuasisimple_map_symm e (isQuasisimple_su6Levi_subgroupOf hf hk hK hσ)⟩

theorem neighbour_standard_2E6_nonsplit_two (hset : SeitzSetting G L)
    (hk : Nat.card k = 2 ^ 1) (hK : Nat.card K = (2 ^ 1) ^ 2) {σ : K →+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ 1) (e : L ≃* graphFixedRootGroup TwistTag.E6 K σ) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    {A : Subgroup (ModGL TwistTag.E6.tag K)} (hAJ : A ≤ thetaRankOneGroup (algebraMap k K))
    (hA : Nat.card A = 2 ^ 1 + 1) (hcyc : IsCyclic A) {X : Subgroup G}
    (hX : X = ((A.subgroupOf (graphFixedRootGroup TwistTag.E6 K σ)).map
      e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G)) {D : Subgroup G}
    (hDe : D = (((su6Levi σ).subgroupOf
      (graphFixedRootGroup TwistTag.E6 K σ)).map e.symm.toMonoidHom).map L.subtype) :
    CFSG.Open.IsComponentOf
        ((D.subgroupOf (centralizer (X : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))))
        (centralizer ({QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩} :
          Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))))) ∧
      (∀ U : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))),
        IsPGroup 2 U →
        U ≤ centralizer ((D.subgroupOf (centralizer (X : Set G))).map
            (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))) :
          Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))) →
        Nat.card U ≤ 2) ∧
      standardComponentIsStandard ((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) := by
  have hf : 1 ≤ 1 := le_rfl
  obtain ⟨-, -, hXD, -⟩ := centralizer_nonsplit_twistedE6 hf hk hK hσ hAJ hA hcyc
  obtain ⟨x, -, hx⟩ := exists_eq_zpowers_of_isCyclic hcyc
  have hAc : A ≤ centralizer (A : Set (ModGL TwistTag.E6.tag K)) := by
    rw [hx]
    exact zpowers_le_centralizer_zpowers x
  exact neighbour_standard_of_centralizer_eq_sup_gen hset.standardSetting.standard htC ht
    (inf_centralizer_eq_zpowers_twistedE6 hset hf hK hσ e htC ht) e
    (centralizer_nonsplit_subgroupOf hf hk hK hσ hAJ hA hcyc)
    (subgroupOf_le_centralizer_subgroupOf hXD) (subgroupOf_le_centralizer_subgroupOf hAc)
    (isQuasisimple_su6Levi_subgroupOf hf hk hK hσ)
    (fun β hβX hβD n hβn => eq_one_of_fix_nonsplit_two hk hK hσ hAJ hA hcyc β hβX hβD n hβn)
    hX htX hDe

end Setting

end CFSG.SeitzReduction.TwistedE6Pilot
