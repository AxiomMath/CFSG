module

public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotPerfectT
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotPerfectV
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotPositionPerfect
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotPositionClass
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotCatAlt

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.TwistedE6Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley RootOps
  CFSG.LieType.Steinberg.Adjoint CFSG.EvenSmallLie
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.Quasithin (perfectCore perfectCore_le perfectCore_perfect)


section Classes

variable {f : ℕ} {k K : Type} [Field k] [Field K] [Algebra k K]

theorem exists_perfect_le_centralizer_of_mem_twistedE6ClassReps [CharP K 2] (hf : 2 ≤ f)
    (hk : Nat.card k = 2 ^ f) (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ f) {s : graphFixedRootGroup TwistTag.E6 K σ}
    (hs : s ∈ twistedE6ClassReps K σ) :
    ∃ P : Subgroup (graphFixedRootGroup TwistTag.E6 K σ), ⁅P, P⁆ = P ∧ s ∈ P ∧
      P ≤ centralizer ({s} : Set (graphFixedRootGroup TwistTag.E6 K σ)) := by
  have := finite_of_card hK
  have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  rcases hs with h | h | h
  ·
    have hs : s = stdRepC (apply_apply_eq hK hσ) 0 := Subtype.ext h
    subst hs
    exact ⟨_, commutator_centralizer_stdRepC_zero (k := k) hf hk hK hσ,
      mem_centralizer_singleton_iff.2 rfl, le_rfl⟩
  ·
    have hs : s = stdRepC (apply_apply_eq hK hσ) 1 := Subtype.ext h
    subst hs
    exact ⟨_, perfectCore_perfect _, stdRepC_one_mem_perfectCore (k := k) hf hk hK hσ,
      perfectCore_le _⟩
  ·
    have hs : s = ⟨twistedE6ClassV K,
        twistedE6ClassV_mem_graphFixedRootGroup (apply_apply_eq hK hσ)⟩ := Subtype.ext h
    subst hs
    exact exists_perfect_le_centralizer_classV (k := k) hf hk hK hσ

theorem exists_perfect_le_centralizer_of_orderOf_eq_two_twistedE6 [CharP K 2] (hf : 2 ≤ f)
    (hk : Nat.card k = 2 ^ f) (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ f) {w : graphFixedRootGroup TwistTag.E6 K σ} (hw : orderOf w = 2) :
    ∃ P : Subgroup (graphFixedRootGroup TwistTag.E6 K σ), ⁅P, P⁆ = P ∧ w ∈ P ∧
      P ≤ centralizer ({w} : Set (graphFixedRootGroup TwistTag.E6 K σ)) := by
  have := finite_of_card hK
  have hw2 : w ^ 2 = 1 := by rw [← hw]; exact pow_orderOf_eq_one w
  have hw1 : w ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hw
    exact absurd hw (by norm_num)
  obtain ⟨σE, rfl⟩ := exists_ringEquiv_toRingHom_eq σ
  obtain ⟨g, hg⟩ := exists_conj_mem_twistedE6ClassReps_of_frameReduction (by omega) hK
    (fun c => hσ c) (twistedE6FrameReduction (by omega) hK (fun c => hσ c)) hw2 hw1
  obtain ⟨P, hP, hsP, hPc⟩ :=
    exists_perfect_le_centralizer_of_mem_twistedE6ClassReps (k := k) hf hk hK hσ hg
  exact F4Pilot.exists_perfect_of_conj hP hsP hPc

theorem card_graphFixedPosUnipotent_twistedE6 (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 2)
    {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    Nat.card (graphFixedPosUnipotent TwistTag.E6 K σ) = (2 ^ f) ^ 36 := by
  have := finite_of_card hK
  have hsurj : Function.Surjective σ := Finite.surjective_of_injective σ.injective
  have hq := CFSG.Timmesfeld.ExceptionalOrders.card_orbitField (t := TwistTag.E6)
    Nat.prime_two hf hK hσ
  obtain ⟨hposS, hposρ, hposcl⟩ := posRoots_twistedE6_facts
  have hc := CFSG.Timmesfeld.ExceptionalOrders.card_rootSpan_inf_twistedFixedGroup
    (t := TwistTag.E6) hsurj hq hposS hposρ hposcl
  have hn : {α : Fin TwistTag.E6.tag.rank → ℤ | IsRoot TwistTag.E6.tag α ∧ 0 < height α}.ncard =
      36 := by
    have e : {α : Fin TwistTag.E6.tag.rank → ℤ | IsRoot TwistTag.E6.tag α ∧ 0 < height α} =
        ↑((rootFinset TwistTag.E6.tag).filter fun α => 0 < height α) := by
      ext α
      simp [mem_rootFinset]
    rw [e, Set.ncard_coe_finset]
    decide +kernel
  rw [graphFixedPosUnipotent, posUnipotent]
  exact hc.trans (congrArg (fun n => (2 ^ f) ^ n) hn)

theorem two_pow_dvd_card_centralizer_stdRepC_zero [CharP K 2] (hf : 1 ≤ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    2 ^ (36 * f) ∣ Nat.card (centralizer ({stdRepC (apply_apply_eq hK hσ) 0} :
      Set (graphFixedRootGroup TwistTag.E6 K σ))) := by
  have := finite_of_card hK
  have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  set U := (graphFixedPosUnipotent TwistTag.E6 K σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ)
  have hU : Nat.card U = (2 ^ f) ^ 36 := by
    rw [← card_graphFixedPosUnipotent_twistedE6 hf hK hσ]
    exact Nat.card_congr (subgroupOfEquivOfLe
      (graphFixedPosUnipotent_le_graphFixedRootGroup _ _ _)).toEquiv
  have hle : U ≤ centralizer ({stdRepC (apply_apply_eq hK hσ) 0} :
      Set (graphFixedRootGroup TwistTag.E6 K σ)) := by
    intro x hx
    rw [mem_centralizer_subtype_iff]
    rw [mem_subgroupOf] at hx
    exact mem_centralizer_singleton_iff.2
      (commute_e6HighestRoot_of_mem_posUnipotent K (mem_inf.1 hx).1 1).eq
  have h := Subgroup.card_dvd_of_le hle
  rw [hU, ← pow_mul, mul_comm f 36] at h
  exact h

theorem two_pow_dvd_card_centralizer_stdRepC_one [CharP K 2] (hf : 2 ≤ f)
    (hk : Nat.card k = 2 ^ f) (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    2 ^ (33 * f) ∣ Nat.card (centralizer ({stdRepC (apply_apply_eq hK hσ) 1} :
      Set (graphFixedRootGroup TwistTag.E6 K σ))) := by
  have := finite_of_card hK
  have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  obtain ⟨Qu, Ku, h1, -, h3, h4, -, h6, h7⟩ := factF3u_twistedE6_full (k := k) hf hk hK hσ
  have hcard : Nat.card (perfectCore (centralizer ({stdRepC (apply_apply_eq hK hσ) 1} :
      Set (graphFixedRootGroup TwistTag.E6 K σ)))) = (2 ^ f) ^ 24 * Nat.card Ku := by
    rw [h1, CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer Qu Ku h3 h4, h7]
  have hKu : 2 ^ (9 * f) ∣ Nat.card Ku := by
    rw [CFSG.SeitzReduction.SymplecticPilot.card_of_lieModel_PSp_two_pow h6]
    have := (CFSG.SeitzReduction.SymplecticPilot.ordBC_two_pow_bounds (m := 3) (by omega :
      1 ≤ f)).1
    rwa [show f * (3 * 3) = 9 * f by ring] at this
  have hdvd : 2 ^ (33 * f) ∣ Nat.card (perfectCore (centralizer
      ({stdRepC (apply_apply_eq hK hσ) 1} : Set (graphFixedRootGroup TwistTag.E6 K σ)))) := by
    rw [hcard, show 33 * f = 24 * f + 9 * f by ring, pow_add, ← pow_mul, mul_comm f 24]
    exact mul_dvd_mul_left _ hKu
  exact hdvd.trans (Subgroup.card_dvd_of_le (perfectCore_le _))

end Classes

section Transport

theorem exists_perfect_le_of_mulEquiv_of_forall' {G : Type*} [Group G] {L : Subgroup G}
    {C : Type*} [Group C] (e : L ≃* C)
    (hC : ∀ w : C, orderOf w = 2 → ∃ P : Subgroup C, ⁅P, P⁆ = P ∧ w ∈ P ∧
      P ≤ centralizer ({w} : Set C)) :
    ∀ w ∈ L, orderOf w = 2 → ∃ P : Subgroup G, ⁅P, P⁆ = P ∧ w ∈ P ∧ P ≤ L ∧
      P ≤ centralizer ({w} : Set G) := by
  intro w hwL hw
  set φ : C →* G := L.subtype.comp e.symm.toMonoidHom with hφdef
  have hwC : orderOf (e ⟨w, hwL⟩) = 2 := by
    rw [MulEquiv.orderOf_eq, orderOf_mk, hw]
  obtain ⟨P, hP, hwP, hPc⟩ := hC _ hwC
  have hφw : φ (e ⟨w, hwL⟩) = w := by simp [hφdef]
  refine ⟨P.map φ, by rw [← map_commutator, hP], ⟨_, hwP, hφw⟩, ?_, ?_⟩
  · rintro _ ⟨p, -, rfl⟩
    exact (e.symm p).2
  · rintro _ ⟨p, hp, rfl⟩
    have h := mem_centralizer_singleton_iff.1 (hPc hp)
    rw [mem_centralizer_singleton_iff, ← hφw, ← map_mul, ← map_mul, h]

variable {f : ℕ} {k K : Type} [Field k] [Field K] [Algebra k K]

theorem exists_perfect_le_of_mulEquiv_twistedE6 {G : Type*} [Group G] {L : Subgroup G}
    [CharP K 2] (hf : 2 ≤ f) (hk : Nat.card k = 2 ^ f) (hK : Nat.card K = (2 ^ f) ^ 2)
    {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) (e : L ≃* graphFixedRootGroup TwistTag.E6 K σ) :
    ∀ w ∈ L, orderOf w = 2 → ∃ P : Subgroup G, ⁅P, P⁆ = P ∧ w ∈ P ∧ P ≤ L ∧
      P ≤ centralizer ({w} : Set G) :=
  exists_perfect_le_of_mulEquiv_of_forall' e fun _ hw =>
    exists_perfect_le_centralizer_of_orderOf_eq_two_twistedE6 (k := k) hf hk hK hσ hw

theorem conj_not_mem_of_mulEquiv_twistedE6 {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hset : StandardSetting G L) [CharP K 2] (hf : 2 ≤ f) (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f)
    (e : L ≃* graphFixedRootGroup TwistTag.E6 K σ) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) (g : G) : g⁻¹ * t * g ∉ L := by
  have := finite_of_card hK
  have hperf := exists_perfect_le_of_mulEquiv_twistedE6 (k := k) hf hk hK hσ e
  obtain ⟨σE, rfl⟩ := exists_ringEquiv_toRingHom_eq σ
  have hOut : Group.IsSolvable (Outer L) :=
    ⟨⟨5, derivedSeries_outer_eq_bot_of_mulEquiv e
      ((exceptional_fixed_root_group_Schreier TwistTag.E6 K σE).1 rfl)⟩⟩
  have hZ : center L = ⊥ :=
    F4Pilot.center_eq_bot_congr e.symm (exceptional_fixed_center_trivial TwistTag.E6 K σE)
  exact F4Pilot.conj_not_mem_of_forall_perfect hset hOut hZ hperf htC ht g

end Transport

end CFSG.SeitzReduction.TwistedE6Pilot
