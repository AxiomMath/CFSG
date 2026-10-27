module

public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotSwapPairV
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotSwapNormalize

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.TwistedE6Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.EvenSmallLie
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.SeitzReduction.F4Pilot.ClassReps (frameT posUnipotentSylow mem_posUnipotentSylow)

variable {f : ℕ} {k K : Type} [Field k] [Field K] [Algebra k K]

theorem swapMem_fixedSubgroup_iff {C : Type*} [Group C] {θ : MulAut C} {y : C} :
    y ∈ fixedSubgroup θ ↔ θ y = y :=
  Iff.rfl

theorem swapFixedSubgroup_conj {C : Type*} [Group C] (φ θ : MulAut C) :
    fixedSubgroup (φ * θ * φ⁻¹) = (fixedSubgroup θ).map φ.toMonoidHom := by
  ext y
  rw [swapMem_fixedSubgroup_iff, mem_map_equiv, swapMem_fixedSubgroup_iff]
  change φ (θ (φ.symm y)) = y ↔ θ (φ.symm y) = φ.symm y
  constructor
  · intro h
    have h' := congrArg φ.symm h
    rwa [MulEquiv.symm_apply_apply] at h'
  · intro h
    rw [h, MulEquiv.apply_symm_apply]

theorem swapFixedSubgroup_conj_eq_centralizer {C : Type*} [Group C] (x : C) :
    fixedSubgroup (MulAut.conj x) = centralizer ({x} : Set C) := by
  ext y
  rw [swapMem_fixedSubgroup_iff, MulAut.conj_apply, mem_centralizer_singleton_iff]
  constructor
  · intro h
    calc y * x = x * y * x⁻¹ * x := by rw [h]
      _ = x * y := by group
  · intro h
    rw [← h]
    group

theorem two_pow_dvd_card_centralizer_of_sq_eq_one [CharP K 2] (hf : 2 ≤ f)
    (hk : Nat.card k = 2 ^ f) (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ f) {x : graphFixedRootGroup TwistTag.E6 K σ} (hx : x ^ 2 = 1)
    (hx1 : x ≠ 1) :
    2 ^ (24 * f) ∣ Nat.card (centralizer ({x} : Set (graphFixedRootGroup TwistTag.E6 K σ))) := by
  have := finite_of_card hK
  obtain ⟨σE, rfl⟩ := exists_ringEquiv_toRingHom_eq σ
  obtain ⟨g, hg⟩ := exists_conj_mem_twistedE6ClassReps_of_frameReduction (by omega) hK
    (fun c => hσ c) (twistedE6FrameReduction (by omega) hK (fun c => hσ c)) hx hx1
  rw [← E6Pilot.card_centralizer_conj g x]
  rcases hg with h | h | h
  · have hs : g * x * g⁻¹ = stdRepC (apply_apply_eq hK hσ) 0 := Subtype.ext h
    rw [hs]
    exact (pow_dvd_pow 2 (by omega : 24 * f ≤ 36 * f)).trans
      (two_pow_dvd_card_centralizer_stdRepC_zero (by omega) hK hσ)
  · have hs : g * x * g⁻¹ = stdRepC (apply_apply_eq hK hσ) 1 := Subtype.ext h
    rw [hs]
    exact (pow_dvd_pow 2 (by omega : 24 * f ≤ 33 * f)).trans
      (two_pow_dvd_card_centralizer_stdRepC_one (k := k) hf hk hK hσ)
  · have hs : g * x * g⁻¹ = ⟨twistedE6ClassV K,
        twistedE6ClassV_mem_graphFixedRootGroup (apply_apply_eq hK hσ)⟩ := Subtype.ext h
    rw [hs]
    exact two_pow_dvd_card_centralizer_classV (by omega) hK hσ

theorem two_pow_dvd_card_centralizer_frameT [CharP k 2] (hk : Nat.card k = 2 ^ f) :
    2 ^ (24 * f) ∣ Nat.card (centralizer ({frameT k} : Set (adjointGroup Tag.F4 k))) := by
  have : Finite k := F4Pilot.finite_of_natCard_eq_two_pow hk
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P := (posUnipotentSylow (K := k) : Subgroup (adjointGroup Tag.F4 k)) with hP
  have hle : P ≤ centralizer ({frameT k} : Set (adjointGroup Tag.F4 k)) := by
    intro x hx
    have hx' := mem_posUnipotentSylow.1 hx
    have h := mem_centralizer_frameT_of_mem_posUnipotent hx'
    exact h
  have hcard : Nat.card P = 2 ^ (24 * f) := by
    rw [hP, Sylow.card_eq_multiplicity, E6Pilot.factorization_card_adjointGroup hk,
      CFSG.Timmesfeld.ExceptionalOrders.ncard_posRoots_F4, mul_comm]
  rw [← hcard]
  exact Subgroup.card_dvd_of_le hle

theorem two_pow_dvd_card_fixedSubgroup_of_outer [CharP K 2] (hf : 1 ≤ f)
    (hk : Nat.card k = 2 ^ f) (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ f) (θ : MulAut (graphFixedRootGroup TwistTag.E6 K σ))
    (hθ : θ ^ 2 = 1) (hθo : θ ∉ (MulAut.conj : graphFixedRootGroup TwistTag.E6 K σ →*
      MulAut (graphFixedRootGroup TwistTag.E6 K σ)).range) :
    2 ^ (24 * f) ∣ Nat.card (fixedSubgroup θ) := by
  have := finite_of_card hK
  have : Finite k := F4Pilot.finite_of_natCard_eq_two_pow hk
  have : CharP k 2 := F4Pilot.charP_two_of_natCard_eq_two_pow hk
  have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  have key : ∀ β₀ : MulAut (graphFixedRootGroup TwistTag.E6 K σ),
      (∃ φ : MulAut (graphFixedRootGroup TwistTag.E6 K σ), φ * θ * φ⁻¹ = β₀) →
      2 ^ (24 * f) ∣ Nat.card (fixedSubgroup β₀) → 2 ^ (24 * f) ∣ Nat.card (fixedSubgroup θ) := by
    rintro β₀ ⟨φ, rfl⟩ h
    rwa [swapFixedSubgroup_conj, Subgroup.card_map_of_injective φ.injective] at h
  rcases (conj_etaAut_or_xiAut_of_outer hf hK σ hσ).1 θ hθ hθo with h | h
  · refine key _ h ?_
    have h24 := factorization_card_eqLocus_etaAut hf hk hK σ hσ
    have h1 := Nat.ordProj_dvd (Nat.card (fixedSubgroup (etaAut σ (apply_apply_eq hK hσ)))) 2
    change 2 ^ (Nat.card ((etaAut σ (apply_apply_eq hK hσ)).toMonoidHom.eqLocus
      (MonoidHom.id (graphFixedRootGroup TwistTag.E6 K σ)))).factorization 2 ∣ _ at h1
    rwa [h24] at h1
  · refine key _ h ?_
    obtain ⟨ψ, h', hψ, hF, -⟩ := exists_eqLocus_xiAut_eq_map hf hk hK σ hσ
    change 2 ^ (24 * f) ∣ Nat.card ((xiAut σ (apply_apply_eq hK hσ)).toMonoidHom.eqLocus
      (MonoidHom.id (graphFixedRootGroup TwistTag.E6 K σ)))
    rw [hF, Subgroup.card_map_of_injective hψ, E6Pilot.card_centralizer_conj h' (frameT k)]
    exact two_pow_dvd_card_centralizer_frameT hk

theorem two_pow_dvd_card_fixedSubgroup_twistedE6 [CharP K 2] (hf : 2 ≤ f)
    (hk : Nat.card k = 2 ^ f) (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ f) (θ : MulAut (graphFixedRootGroup TwistTag.E6 K σ))
    (hθ : θ * θ = 1) (hθ1 : θ ≠ 1) : 2 ^ (24 * f) ∣ Nat.card (fixedSubgroup θ) := by
  have := finite_of_card hK
  have hZ : center (graphFixedRootGroup TwistTag.E6 K σ) = ⊥ :=
    center_graphFixedRootGroup_eq_bot (Finite.surjective_of_injective σ.injective)
  by_cases hin : θ ∈ (MulAut.conj : graphFixedRootGroup TwistTag.E6 K σ →*
      MulAut (graphFixedRootGroup TwistTag.E6 K σ)).range
  · obtain ⟨x, rfl⟩ := hin
    rw [swapFixedSubgroup_conj_eq_centralizer]
    have hx1 : x ≠ 1 := by
      rintro rfl
      exact hθ1 (map_one _)
    have hx2 : x ^ 2 = 1 := by
      have hc : x * x ∈ center (graphFixedRootGroup TwistTag.E6 K σ) := by
        rw [mem_center_iff]
        intro g
        have h := congrArg (fun φ : MulAut (graphFixedRootGroup TwistTag.E6 K σ) => φ g) hθ
        simp only [MulAut.mul_apply, MulAut.conj_apply, MulAut.one_apply] at h
        calc g * (x * x) = x * (x * g * x⁻¹) * x⁻¹ * (x * x) := by rw [h]
          _ = x * x * g := by group
      rw [hZ, mem_bot] at hc
      rw [sq]
      exact hc
    exact two_pow_dvd_card_centralizer_of_sq_eq_one hf hk hK hσ hx2 hx1
  · exact two_pow_dvd_card_fixedSubgroup_of_outer (by omega) hk hK hσ θ (by rw [sq]; exact hθ)
      hin

theorem factorization_two_mul_card_mulAut_twistedE6_le [CharP K 2] (hf : 1 ≤ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    (2 * Nat.card (MulAut (graphFixedRootGroup TwistTag.E6 K σ))).factorization 2 ≤
      36 * f + 2 + f.factorization 2 := by
  have := finite_of_card hK
  have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  have : Finite (MulAut (graphFixedRootGroup TwistTag.E6 K σ)) := MulEquiv.finite_left
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hC : (Nat.card (graphFixedRootGroup TwistTag.E6 K σ)).factorization 2 = 36 * f := by
    obtain ⟨σE, rfl⟩ := exists_ringEquiv_toRingHom_eq σ
    obtain ⟨w₀, hw₀⟩ := Finite.exists_max fun w : WeylGroup TwistTag.E6.tag =>
      (coxeterSystem TwistTag.E6.tag).length w
    obtain ⟨P, hP⟩ := (exceptional_fixed_Sylow_opposition TwistTag.E6 K 2 σE w₀ hw₀).1
    have hcard : Nat.card (P : Subgroup (graphFixedRootGroup TwistTag.E6 K σE.toRingHom)) =
        2 ^ (36 * f) := by
      rw [hP, Nat.card_congr (subgroupOfEquivOfLe
        (graphFixedPosUnipotent_le_graphFixedRootGroup _ _ _)).toEquiv,
        card_graphFixedPosUnipotent_twistedE6 hf hK hσ, ← pow_mul, mul_comm f 36]
    rw [Sylow.card_eq_multiplicity] at hcard
    exact Nat.pow_right_injective (le_refl 2) hcard
  have hOut := factorization_card_outer_twistedE6 hf hK σ hσ
  have hdvd := E6Pilot.card_mulAut_dvd_card_mul_card_outer (graphFixedRootGroup TwistTag.E6 K σ)
  have hA0 : Nat.card (MulAut (graphFixedRootGroup TwistTag.E6 K σ)) ≠ 0 := Nat.card_pos.ne'
  have hC0 : Nat.card (graphFixedRootGroup TwistTag.E6 K σ) ≠ 0 := Nat.card_pos.ne'
  have hO0 : Nat.card (Outer (graphFixedRootGroup TwistTag.E6 K σ)) ≠ 0 := Nat.card_pos.ne'
  have hle := (Nat.factorization_le_iff_dvd hA0 (mul_ne_zero hC0 hO0)).2 hdvd 2
  rw [Nat.factorization_mul hC0 hO0, Finsupp.add_apply, hC, hOut] at hle
  rw [Nat.factorization_mul (by norm_num) hA0, Finsupp.add_apply,
    Nat.Prime.factorization_self Nat.prime_two]
  omega

theorem swapPairExclusion_twistedE6 [CharP K 2] (hf : 2 ≤ f) (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    SeitzQ2.SwapPairExclusion (graphFixedRootGroup TwistTag.E6 K σ) := by
  have := finite_of_card hK
  intro θ θ' h1 h2 h3 h4 hsum _
  have hb : ∀ θ : MulAut (graphFixedRootGroup TwistTag.E6 K σ), θ * θ = 1 → θ ≠ 1 →
      24 * f ≤ (Nat.card (fixedSubgroup θ)).factorization 2 := fun θ hθ hθ1 =>
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').1
      (two_pow_dvd_card_fixedSubgroup_twistedE6 hf hk hK hσ θ hθ hθ1)
  have hA := factorization_two_mul_card_mulAut_twistedE6_le (by omega) hK hσ
  have hlt : f.factorization 2 < f := Nat.factorization_lt 2 (by omega)
  have := hb θ h1 h2
  have := hb θ' h3 h4
  omega

theorem false_of_swapRow_2E6_of_components' {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hset : SeitzSetting G L) (hf2 : 2 ≤ f)
    (hk : Nat.card k = 2 ^ f) (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ f) (e : L ≃* graphFixedRootGroup TwistTag.E6 K σ) {t : G}
    (ht : orderOf t = 2) (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {X : Subgroup G} (hX : X = (((E6GraphLevi.thetaTorus (algebraMap k K)).subgroupOf
      (graphFixedRootGroup TwistTag.E6 K σ)).map e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G)) {D : Subgroup G} (hDe : D = (((su6Levi σ).subgroupOf
      (graphFixedRootGroup TwistTag.E6 K σ)).map e.symm.toMonoidHom).map L.subtype)
    {Kc : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))}
    (hKc : CFSG.IsComponent Kc)
    (hDKK : (D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))) ≤
      Kc ⊔ Kc.map (MulAut.conj
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)).toMonoidHom)
    (hne : Kc.map (MulAut.conj
      (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)).toMonoidHom ≠ Kc)
    (hcomm : ⁅Kc, Kc.map (MulAut.conj
      (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)).toMonoidHom⁆ = ⊥)
    (hZ : center Kc = ⊥)
    (hφ : Nonempty (Kc ≃* (D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))))
    {Y : Subgroup G} (hY : Y = (((shortRootTorus (algebraMap k K)).subgroupOf
      (graphFixedRootGroup TwistTag.E6 K σ)).map e.symm.toMonoidHom).map L.subtype)
    (htY : t ∈ centralizer (Y : Set G)) {DY : Subgroup G}
    (hDYe : DY = (((omegaMinusLevi σ).subgroupOf
      (graphFixedRootGroup TwistTag.E6 K σ)).map e.symm.toMonoidHom).map L.subtype)
    {KY : Subgroup (centralizer (Y : Set G) ⧸ oddCore (centralizer (Y : Set G)))}
    (hKY : CFSG.IsComponent KY)
    (hDKY : (DY.subgroupOf (centralizer (Y : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (Y : Set G)))) ≤
      KY ⊔ KY.map (MulAut.conj
        (QuotientGroup.mk' (oddCore (centralizer (Y : Set G))) ⟨t, htY⟩)).toMonoidHom)
    (hneY : KY.map (MulAut.conj
      (QuotientGroup.mk' (oddCore (centralizer (Y : Set G))) ⟨t, htY⟩)).toMonoidHom ≠ KY)
    (hcommY : ⁅KY, KY.map (MulAut.conj
      (QuotientGroup.mk' (oddCore (centralizer (Y : Set G))) ⟨t, htY⟩)).toMonoidHom⁆ = ⊥)
    (hφY : Nonempty (KY ≃* (DY.subgroupOf (centralizer (Y : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (Y : Set G)))))) :
    False := by
  have : CharP K 2 := F4Pilot.charP_two_of_natCard_eq_two_pow
    (show Nat.card K = 2 ^ (2 * f) by rw [hK, ← pow_mul, mul_comm])
  exact false_of_swapRow_2E6_of_components hset hf2 hk hK hσ e
    (swapPairExclusion_twistedE6 hf2 hk hK hσ) ht hKt hX htX hDe hKc hDKK hne hcomm hZ hφ hY htY
    hDYe hKY hDKY hneY hcommY hφY

end CFSG.SeitzReduction.TwistedE6Pilot
