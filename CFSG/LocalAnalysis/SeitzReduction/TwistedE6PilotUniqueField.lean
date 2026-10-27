module

public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotUniqueFieldInner
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotUniqueFieldTorus

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.TwistedE6Pilot

open Subgroup CFSG.Open CFSG.EvenSmallLie CFSG.Blueprint CFSG.Blueprint.Chevalley
open CFSG.LieType.Chevalley
open CFSG.ComponentClassification (OuterAutomorphisms.inner OuterAutomorphisms.Outer)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

theorem not_ordE6_dvd_ordTwistedE6 {f : ℕ} (hf : 1 ≤ f) :
    ¬ ordE6 (2 ^ f) ∣ ordTwistedE6 (2 ^ f) := by
  intro hdvd
  have hk : 0 < 5 * f := by omega
  obtain ⟨p, hp⟩ := CFSG.Timmesfeld.exists_isPrimitivePrimeDivisor (k := 5 * f) (by omega)
    (by omega)
  set q := 2 ^ f with hq
  have hf0 : f ≠ 0 := by omega
  have hsub : ∀ i : ℕ, ¬ 5 ∣ i → ¬ p ∣ q ^ i - 1 := by
    intro i hi
    rw [hq, ← pow_mul, hp.dvd_sub_one_iff hk]
    rintro ⟨m, hm⟩
    refine hi ⟨m, Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hf0) ?_⟩
    rw [hm]
    ring
  have hp2 : p ≠ 2 := hp.ne_two hk
  have hq36 : ¬ p ∣ q ^ 36 := by
    rw [hq, ← pow_mul]
    intro h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.prime Nat.prime_two).1
      (hp.prime.dvd_of_dvd_pow h))
  have hp3 : ¬ p ∣ 3 := fun h => by
    have := hp.eq_two_of_dvd_three hk h
    omega
  have h5 : p ∣ q ^ 5 - 1 := by
    rw [hq, ← pow_mul, hp.dvd_sub_one_iff hk]
    exact ⟨1, by ring⟩
  have h5' : ¬ p ∣ q ^ 5 + 1 := by
    rw [hq, ← pow_mul, hp.dvd_add_one_iff hk]
    rintro ⟨-, h⟩
    exact h ⟨1, by ring⟩
  have h9' : ¬ p ∣ q ^ 9 + 1 := by
    rw [hq, ← pow_mul, hp.dvd_add_one_iff hk]
    rintro ⟨⟨m, hm⟩, -⟩
    have h18 : 18 = 5 * m := Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hf0) (by
      rw [show f * 18 = 2 * (f * 9) by ring, hm]
      ring)
    omega
  set N := q ^ 36 * (q ^ 12 - 1) * (q ^ 9 - 1) * (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 5 - 1) *
    (q ^ 2 - 1) with hN
  set N' := q ^ 36 * (q ^ 12 - 1) * (q ^ 9 + 1) * (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 5 + 1) *
    (q ^ 2 - 1) with hN'
  have hg : Nat.gcd 3 (q - 1) ∣ N := (Nat.gcd_dvd_right 3 (q - 1)).trans
    (Dvd.dvd.mul_left (Nat.sub_one_dvd_pow_sub_one q 2) _)
  have hE : ordE6 q * Nat.gcd 3 (q - 1) = N := Nat.div_mul_cancel hg
  have h2E : ordTwistedE6 q ∣ N' := Nat.div_dvd_of_dvd (Nat.gcd_dvd_right 3 (q + 1) |>.trans (by
    refine Dvd.dvd.mul_right (Dvd.dvd.mul_right (Dvd.dvd.mul_right (Dvd.dvd.mul_right
      (Dvd.dvd.mul_left ?_ _) _) _) _) _
    simpa using Odd.nat_add_dvd_pow_add_pow q 1 (by decide : Odd 9)))
  have hpN : p ∣ N := by
    refine Dvd.dvd.mul_right ?_ _
    exact Dvd.dvd.mul_left h5 _
  have hpE : p ∣ ordE6 q := by
    rw [← hE] at hpN
    rcases hp.prime.dvd_mul.1 hpN with h | h
    · exact h
    · exact absurd (h.trans (Nat.gcd_dvd_left 3 (q - 1))) hp3
  have hpN' := (hpE.trans hdvd).trans h2E
  rcases hp.prime.dvd_mul.1 hpN' with h | h
  · rcases hp.prime.dvd_mul.1 h with h | h
    · rcases hp.prime.dvd_mul.1 h with h | h
      · rcases hp.prime.dvd_mul.1 h with h | h
        · rcases hp.prime.dvd_mul.1 h with h | h
          · rcases hp.prime.dvd_mul.1 h with h | h
            · exact hq36 h
            · exact hsub 12 (by norm_num) h
          · exact h9' h
        · exact hsub 8 (by norm_num) h
      · exact hsub 6 (by norm_num) h
    · exact h5' h
  · exact hsub 2 (by norm_num) h

section Cover

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

open CFSG.SeitzReduction.EPilot (normalizerQuotMulAut)
open CFSG.Quasithin (perfectCore)

theorem inf_centralizer_eq_of_mem_normalizer_twistedE6_cover (hset : StandardSetting G L)
    {f : ℕ} {K : Type} [Field K] (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ f) (e : L ≃* graphFixedRootGroup TwistTag.E6 K σ) {t : G}
    (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) {M : Subgroup G}
    (hMp : ⁅M, M⁆ = M) (hZ : Odd (Nat.card (center M))) {K₂ : Type} [Field K₂]
    (hK₂ : Nat.card K₂ = (2 ^ f) ^ 2) (eM : M ⧸ center M ≃* adjointGroup .E6 K₂)
    (htM : t ∈ normalizer (M : Set G)) :
    (∃ σ₂ : K₂ ≃+* K₂, σ₂ ^ 2 = 1 ∧ σ₂ ≠ 1 ∧ (∀ c, σ₂ c = c ^ (2 ^ f)) ∧
      ∃ φ : MulAut (adjointGroup .E6 K₂), φ * normalizerQuotMulAut eM ⟨t, htM⟩ * φ⁻¹ =
        diagramConjAut TwistTag.E6 K₂ * entrywiseAdjointAut TwistTag.E6.tag σ₂) ∧
    M ⊓ centralizer ({t} : Set G) = L := by
  have hf := one_le_of_card_sq_twistedE6 hK
  have hK₂' := card_eq_two_pow_two_mul_twistedE6 hK₂
  have := finite_of_card hK
  have := charP_two_of_card hf hK
  have := F4Pilot.finite_of_natCard_eq_two_pow hK₂'
  have := F4Pilot.charP_two_of_natCard_eq_two_pow hK₂'
  have : Finite (adjointGroup .E6 K₂) := by
    have : Finite (ModGL Tag.E6 K₂) := finite_modGL
    infer_instance
  have hq : 4 ≤ Nat.card K₂ := by
    rw [hK₂']
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (2 * f) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hOut : Group.IsSolvable (Outer L) := (outer_solvable_and_center_eq_bot_twistedE6 hK σ e).1
  have htC : t ∈ centralizer (L : Set G) := (hKt ▸ mem_zpowers t :
    t ∈ centralizer (L : Set G) ⊓ centralizer ({t} : Set G)).1
  set C := adjointGroup TwistTag.E6.tag K₂ with hCdef
  set α : MulAut C := normalizerQuotMulAut eM ⟨t, htM⟩ with hαdef
  have hα2 : α ^ 2 = 1 := E6Pilot.normalizerQuotMulAut_sq_eq_one eM ht htM
  have hαo : α ∉ OuterAutomorphisms.inner C :=
    not_inner_quot_twistedE6 hset hK hσ e ht hKt hMp hZ hK₂ eM htM
  set π₀ : M →* C := eM.toMonoidHom.comp (QuotientGroup.mk' (center M)) with hπ₀
  set Xm : Subgroup M := (centralizer ({t} : Set G)).subgroupOf M with hXm
  set X : Subgroup G := M ⊓ centralizer ({t} : Set G) with hXdef
  have hXmX : Xm.map M.subtype = X := by
    rw [hXm, subgroupOf_map_subtype, inf_comm]
  have hXt : X ≤ centralizer ({t} : Set G) := inf_le_right
  have hcardX : Nat.card Xm = Nat.card X := by
    rw [← hXmX, card_map_of_injective M.subtype_injective]
  have hfix : Xm.map π₀ = E6Pilot.fixSubgroup α :=
    E6Pilot.map_subgroupOf_centralizer_eq_fixSubgroup hZ eM ht htM
  have hcardfix : Nat.card (E6Pilot.fixSubgroup α) ∣ Nat.card X := by
    rw [← hfix, ← hcardX]
    exact Subgroup.card_map_dvd _ _
  have hPX : (perfectCore Xm).map M.subtype = perfectCore X := by
    rw [CFSG.Quasithin.map_perfectCore, hXmX]
  have hPfix : (perfectCore Xm).map π₀ = perfectCore (E6Pilot.fixSubgroup α) := by
    rw [CFSG.Quasithin.map_perfectCore, hfix]
  have hPL : perfectCore X ≤ L :=
    std_perfect_le hset hOut htC ht (CFSG.Quasithin.perfectCore_perfect X)
      ((CFSG.Quasithin.perfectCore_le X).trans hXt)
  have hcardP : Nat.card (perfectCore (E6Pilot.fixSubgroup α)) ∣ Nat.card L := by
    rw [← hPfix]
    refine (Subgroup.card_map_dvd _ _).trans ?_
    rw [← card_map_of_injective M.subtype_injective, hPX]
    exact card_dvd_of_le hPL
  have hgraph : ∀ β₀ : MulAut C, (∃ φ, φ * α * φ⁻¹ = β₀) →
      Nat.card K₂ ^ 20 ∣ Nat.card (E6Pilot.fixSubgroup β₀) → False := by
    rintro β₀ ⟨φ, rfl⟩ hdvd
    rw [E6Pilot.card_fixSubgroup_conj, hK₂', ← pow_mul] at hdvd
    have hb := factorization_card_le_of_le_centralizer_twistedE6 hset.standard hK hσ e ht hKt hXt
    have h1 := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').1
      (hdvd.trans hcardfix)
    have hlt : f.factorization 2 < f := Nat.factorization_lt 2 (by omega)
    omega
  have hDL : ∀ β₀ : MulAut C, ∀ φ, φ * α * φ⁻¹ = β₀ →
      (⁅⁅E6Pilot.fixSubgroup β₀, E6Pilot.fixSubgroup β₀⁆,
          ⁅E6Pilot.fixSubgroup β₀, E6Pilot.fixSubgroup β₀⁆⁆ : Subgroup C) =
        ⁅E6Pilot.fixSubgroup β₀, E6Pilot.fixSubgroup β₀⁆ →
      Nat.card (⁅E6Pilot.fixSubgroup β₀, E6Pilot.fixSubgroup β₀⁆ : Subgroup C) ∣
        Nat.card (perfectCore (E6Pilot.fixSubgroup α)) := by
    rintro β₀ φ rfl hperf
    set D : Subgroup C := ⁅E6Pilot.fixSubgroup α, E6Pilot.fixSubgroup α⁆ with hD
    have hDφ : D.map φ.toMonoidHom = ⁅E6Pilot.fixSubgroup (φ * α * φ⁻¹),
        E6Pilot.fixSubgroup (φ * α * φ⁻¹)⁆ :=
      E6Pilot.map_commutator_fixSubgroup_conj φ α
    have hDD : ⁅D, D⁆ = D := by
      apply Subgroup.map_injective (f := φ.toMonoidHom) φ.injective
      rw [map_commutator, hDφ, hperf]
    rw [← hDφ, card_map_of_injective φ.injective]
    exact card_dvd_of_le (CFSG.Quasithin.le_perfectCore_of_perfect
      (Subgroup.commutator_le_self _) hDD)
  have hLcard : Nat.card L = ordTwistedE6 (2 ^ f) := by
    rw [Nat.card_congr e.toEquiv,
      CFSG.Timmesfeld.ExceptionalOrders.card_graphFixedRootGroup_E6_two hf hK σ hσ]
  rcases E6Pilot.outer_involution_cases_E6 (by omega : 1 ≤ 2 * f) K₂ hK₂' α hα2 hαo with
    ⟨η, hη, ⟨φ, hφ⟩ | ⟨ht', φ, hφ⟩⟩ | ⟨σ₂, hσ2, hσ1, ⟨φ, hφ⟩ | ⟨φ, hφ⟩⟩
  · exact (hgraph η ⟨φ, hφ⟩
      (E6Pilot.card_pow_twenty_dvd_card_fixSubgroup_graph_E6 hq η hη).1).elim
  · exact (hgraph _ ⟨φ, hφ⟩
      ((E6Pilot.card_pow_twenty_dvd_card_fixSubgroup_graph_E6 hq η hη).2 ht')).elim
  ·
    exfalso
    obtain ⟨hD, hperf, hcard⟩ := E6Pilot.commutator_fixSubgroup_field_E6 hf hK₂' σ₂ hσ2 hσ1
    have hdvd := hDL _ φ hφ (by rw [hD]; exact hperf)
    rw [hD, hcard] at hdvd
    have h := hdvd.trans hcardP
    rw [hLcard] at h
    exact not_ordE6_dvd_ordTwistedE6 hf h
  ·
    obtain ⟨hperf, hcard⟩ := fixSubgroup_graphField_perfect_card_twistedE6 hf hK₂' σ₂ hσ2 hσ1
    have hdvd := hDL _ φ hφ (by rw [hperf, hperf])
    rw [hperf, hcard] at hdvd
    have hPeq : perfectCore X = L := by
      refine Subgroup.eq_of_le_of_card_ge hPL ?_
      rw [hLcard, ← hPX, card_map_of_injective M.subtype_injective]
      refine Nat.le_of_dvd Nat.card_pos (hdvd.trans ?_)
      rw [← hPfix]
      exact Subgroup.card_map_dvd _ _
    have hLX : L ≤ X := hPeq ▸ CFSG.Quasithin.perfectCore_le X
    have hLM : L ≤ M := hLX.trans inf_le_left
    have hinj : Xm ⊓ π₀.ker = ⊥ := by
      rw [eq_bot_iff]
      rintro z ⟨hzX, hzk⟩
      have hzZ : z ∈ center M := by
        have h1 : eM (QuotientGroup.mk' (center M) z) = 1 := hzk
        rw [← QuotientGroup.ker_mk' (center M), MonoidHom.mem_ker]
        exact eM.injective (h1.trans (map_one eM).symm)
      have hzt : (z : G) ∈ centralizer ({t} : Set G) := mem_subgroupOf.1 hzX
      have hzL : (z : G) ∈ centralizer (L : Set G) := by
        rw [mem_centralizer_iff]
        intro l hl
        have h1 := mem_center_iff.1 hzZ ⟨l, hLM hl⟩
        exact (congrArg Subtype.val h1)
      have hzz : (z : G) ∈ zpowers t := hKt ▸ ⟨hzL, hzt⟩
      have hzodd := E6Pilot.odd_orderOf_of_mem_center hZ hzZ
      have hdvd2 : orderOf z ∣ 2 := by
        rw [← Subgroup.orderOf_coe, ← ht]
        exact orderOf_dvd_of_mem_zpowers hzz
      rcases (Nat.dvd_prime Nat.prime_two).1 hdvd2 with h1 | h2
      · exact orderOf_eq_one_iff.1 h1
      · rw [h2] at hzodd
        exact absurd hzodd (by decide)
    set πX : Xm →* C := π₀.comp Xm.subtype with hπX
    have hπXinj : Function.Injective πX := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro z hz
      have hz' : (z : M) ∈ Xm ⊓ π₀.ker := ⟨z.2, hz⟩
      rw [hinj, mem_bot] at hz'
      exact (mem_bot).2 (Subtype.ext hz')
    have hπXrange : πX.range = Xm.map π₀ := by
      rw [hπX, MonoidHom.range_comp, range_subtype]
    have hcardXfix : Nat.card X = Nat.card (E6Pilot.fixSubgroup α) := by
      rw [← hcardX, ← hfix, ← hπXrange]
      exact Nat.card_congr (MonoidHom.ofInjective hπXinj).toEquiv
    have hcardα : Nat.card (E6Pilot.fixSubgroup α) = ordTwistedE6 (2 ^ f) := by
      rw [← E6Pilot.card_fixSubgroup_conj φ α, hφ, hcard]
    refine ⟨⟨σ₂, hσ2, hσ1, (E6Pilot.field_involution_facts_E6 hf hK₂' σ₂ hσ2 hσ1).1, φ, hφ⟩, ?_⟩
    refine (Subgroup.eq_of_le_of_card_ge hLX ?_).symm
    rw [hcardXfix, hcardα, hLcard]

end Cover

end CFSG.SeitzReduction.TwistedE6Pilot
