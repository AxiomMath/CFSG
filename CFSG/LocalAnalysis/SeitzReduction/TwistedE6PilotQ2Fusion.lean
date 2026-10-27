module

public import CFSG.LocalAnalysis.SeitzReduction.E6PilotQ2Fusion
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotSwapPair

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.TwistedE6Pilot

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.EvenSmallLie
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms


section Model

variable {k K : Type} [Field k] [Field K] [Algebra k K]

theorem commutator_centralizer_stdRepC_zero_two [CharP K 2] (hk : Nat.card k = 2 ^ 1)
    (hK : Nat.card K = (2 ^ 1) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ 1) :
    ⁅centralizer ({stdRepC (apply_apply_eq hK hσ) 0} : Set (graphFixedRootGroup TwistTag.E6 K σ)),
        centralizer ({stdRepC (apply_apply_eq hK hσ) 0} :
          Set (graphFixedRootGroup TwistTag.E6 K σ))⁆ =
      centralizer ({stdRepC (apply_apply_eq hK hσ) 0} :
        Set (graphFixedRootGroup TwistTag.E6 K σ)) := by
  have hf : 1 ≤ 1 := le_rfl
  have := finite_of_card hK
  have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  set C₀ := graphFixedRootGroup TwistTag.E6 K σ with hC₀
  have hC := centralizer_stdRepC_zero_eq (k := k) hf hk hK hσ
  obtain ⟨-, hLN, -⟩ := centralizer_stdRep_zero_inf_eq (k := k) hf hk hK hσ
  have hLC : su6Levi σ ≤ C₀ := su6Levi_le_graphFixedRootGroup σ
  have hperf : ⁅(su6Levi σ).subgroupOf C₀, (su6Levi σ).subgroupOf C₀⁆ =
      (su6Levi σ).subgroupOf C₀ := by
    apply map_injective C₀.subtype_injective
    rw [map_commutator, subgroupOf_map_subtype, inf_of_le_left hLC,
      commutator_su6Levi hf hk hK hσ]
  have hQU : ∀ x : C₀, x ∈ (tRadical σ).subgroupOf C₀ →
      (x : ModGL TwistTag.E6.tag K) ∈ graphFixedPosUnipotent TwistTag.E6 K σ := by
    intro x hx
    rw [mem_subgroupOf] at hx
    exact mem_inf.2 ⟨parabolicRadical_le_posUnipotent _ (mem_inf.1 hx).1,
      graphFixedRootGroup_le _ _ _ x.2⟩
  have hQ2 : IsPGroup 2 ((tRadical σ).subgroupOf C₀) := by
    have hle : (tRadical σ).subgroupOf C₀ ≤ (graphFixedPosUnipotent TwistTag.E6 K σ).subgroupOf C₀ :=
      fun x hx => mem_subgroupOf.2 (hQU x hx)
    exact (isPGroup_graphFixedPosUnipotent_subgroupOf (p := 2) (t := TwistTag.E6)).to_le hle
  have hLN' : (su6Levi σ).subgroupOf C₀ ≤ normalizer ((tRadical σ).subgroupOf C₀ : Set C₀) := by
    intro x hx
    rw [mem_subgroupOf] at hx
    rw [mem_normalizer_iff]
    intro y
    simp only [mem_subgroupOf, coe_mul, coe_inv]
    exact mem_normalizer_iff.1 (hLN hx) y
  set t₀ := stdRepC (apply_apply_eq hK hσ) 0 with ht₀
  have hQS : (tRadical σ).subgroupOf C₀ ≤
      closure {c : C₀ | c * t₀ = t₀ * c ∧ Odd (orderOf c)} := by
    intro x hx
    obtain ⟨σE, hσE⟩ := exists_ringEquiv_toRingHom_eq σ
    subst hσE
    exact graphFixedPosUnipotent_le_closure_odd_two (by rw [hK]; norm_num)
      (fun c => by simpa using hσ c) (t := t₀) rfl (hQU x hx)
  have hSN : ∀ c ∈ {c : C₀ | c * t₀ = t₀ * c ∧ Odd (orderOf c)},
      c ∈ (tRadical σ).subgroupOf C₀ ⊔ (su6Levi σ).subgroupOf C₀ := by
    intro c hc
    have hc1 : c * t₀ = t₀ * c := hc.1
    have hc' : c ∈ centralizer ({t₀} : Set C₀) := mem_centralizer_singleton_iff.2 hc1
    rw [hC] at hc'
    exact hc'
  rw [hC]
  exact F4Pilot.commutator_sup_eq_self_of_closure_odd hQ2 hLN' hperf hSN (fun c hc => hc.2) hQS

theorem commutator_centralizer_of_twoCentral_two [CharP K 2] (hk : Nat.card k = 2 ^ 1)
    (hK : Nat.card K = (2 ^ 1) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ 1)
    {w : graphFixedRootGroup TwistTag.E6 K σ} (hw : orderOf w = 2)
    (hwS : ∃ S : Sylow 2 (graphFixedRootGroup TwistTag.E6 K σ),
      ∀ s ∈ (S : Subgroup (graphFixedRootGroup TwistTag.E6 K σ)), s * w = w * s) :
    ⁅centralizer ({w} : Set (graphFixedRootGroup TwistTag.E6 K σ)),
        centralizer ({w} : Set (graphFixedRootGroup TwistTag.E6 K σ))⁆ =
      centralizer ({w} : Set (graphFixedRootGroup TwistTag.E6 K σ)) := by
  obtain ⟨g, hg⟩ := (conj_repX_zero_iff_twoCentral le_rfl hK hσ hw).2 hwS
  obtain ⟨h, hhC, hh⟩ := isConj_stdRep_repX (K := K) σ 0
  set hC : graphFixedRootGroup TwistTag.E6 K σ := ⟨h, hhC⟩ with hhCdef
  set n : graphFixedRootGroup TwistTag.E6 K σ := hC⁻¹ * g with hndef
  have hn : n * w * n⁻¹ = stdRepC (apply_apply_eq hK hσ) 0 := by
    apply Subtype.ext
    have e1 : ((n * w * n⁻¹ : graphFixedRootGroup TwistTag.E6 K σ) : ModGL TwistTag.E6.tag K) =
        h⁻¹ * ((g * w * g⁻¹ : graphFixedRootGroup TwistTag.E6 K σ) : ModGL TwistTag.E6.tag K) *
          h := by
      simp only [hndef, hhCdef, coe_mul, coe_inv, mul_inv_rev, inv_inv]
      group
    rw [e1, hg, ← hh]
    change h⁻¹ * (h * stdRep K 0 * h⁻¹) * h = stdRep K 0
    group
  have hwn : w = n⁻¹ * stdRepC (apply_apply_eq hK hσ) 0 * n⁻¹⁻¹ := by
    rw [← hn]
    group
  rw [hwn, ← E6Pilot.map_conj_centralizer_singleton_q2, ← map_commutator,
    commutator_centralizer_stdRepC_zero_two hk hK hσ]

theorem card_fixedSubgroup_dvd_of_outer_two [CharP K 2] (hk : Nat.card k = 2 ^ 1)
    (hK : Nat.card K = (2 ^ 1) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ 1)
    (β : MulAut (graphFixedRootGroup TwistTag.E6 K σ)) (hβ : β ^ 2 = 1)
    (hin : β ∉ (MulAut.conj : graphFixedRootGroup TwistTag.E6 K σ →*
      MulAut (graphFixedRootGroup TwistTag.E6 K σ)).range) :
    Nat.card (fixedSubgroup β) ∣ Nat.card (adjointGroup Tag.F4 k) := by
  have hf : 1 ≤ 1 := le_rfl
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; positivity)
  have := finite_of_card hK
  have key : ∀ β₀ : MulAut (graphFixedRootGroup TwistTag.E6 K σ),
      (∃ φ : MulAut (graphFixedRootGroup TwistTag.E6 K σ), φ * β * φ⁻¹ = β₀) →
      Nat.card (fixedSubgroup β₀) ∣ Nat.card (adjointGroup Tag.F4 k) →
      Nat.card (fixedSubgroup β) ∣ Nat.card (adjointGroup Tag.F4 k) := by
    rintro β₀ ⟨φ, rfl⟩ h
    rwa [swapFixedSubgroup_conj, Subgroup.card_map_of_injective φ.injective] at h
  rcases (conj_etaAut_or_xiAut_of_outer hf hK σ hσ).1 β hβ hin with h | h
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

theorem two_pow_dvd_card_sylow_twistedE6_two (hK : Nat.card K = (2 ^ 1) ^ 2) {σ : K →+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ 1) (S : Sylow 2 (graphFixedRootGroup TwistTag.E6 K σ)) :
    2 ^ 36 ∣ Nat.card (S : Subgroup (graphFixedRootGroup TwistTag.E6 K σ)) := by
  have := finite_of_card hK
  have : CharP K 2 := charP_two_of_card le_rfl hK
  have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set U₀ := (graphFixedPosUnipotent TwistTag.E6 K σ).subgroupOf
    (graphFixedRootGroup TwistTag.E6 K σ) with hU₀
  have hU₀2 : IsPGroup 2 U₀ := isPGroup_graphFixedPosUnipotent_subgroupOf (p := 2) (t := TwistTag.E6)
  have hcard : Nat.card U₀ = 2 ^ 36 := by
    rw [hU₀, Nat.card_congr (subgroupOfEquivOfLe
      (graphFixedPosUnipotent_le_graphFixedRootGroup _ _ _)).toEquiv,
      card_graphFixedPosUnipotent_twistedE6 le_rfl hK hσ]
    norm_num
  obtain ⟨S', hS'⟩ := hU₀2.exists_le_sylow
  have h1 : 2 ^ 36 ∣ Nat.card (S' : Subgroup (graphFixedRootGroup TwistTag.E6 K σ)) := by
    rw [← hcard]
    exact Subgroup.card_dvd_of_le hS'
  rwa [Sylow.card_eq_multiplicity, ← Sylow.card_eq_multiplicity S] at h1

end Model

section Fusion

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {k K : Type} [Field k] [Field K]
  [Algebra k K]

theorem not_forall_commute_sylow_conj_twistedE6_two (hset : StandardSetting G L)
    (hk : Nat.card k = 2 ^ 1) (hK : Nat.card K = (2 ^ 1) ^ 2) {σ : K →+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ 1) (e : L ≃* graphFixedRootGroup TwistTag.E6 K σ) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) :
    ∀ (U : Sylow 2 L) (g : G), g⁻¹ * t * g ∈ L →
      ¬ ∀ u ∈ (U : Subgroup L), (u : G) * (g⁻¹ * t * g) = (g⁻¹ * t * g) * u := by
  intro U g hwL hwU
  have : CharP K 2 := charP_two_of_card le_rfl hK
  have := finite_of_card hK
  have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  obtain ⟨hOut, hZ⟩ := outer_solvable_and_center_eq_bot_twistedE6 hK σ e
  set w := g⁻¹ * t * g with hwdef
  set φ : graphFixedRootGroup TwistTag.E6 K σ →* G := L.subtype.comp e.symm.toMonoidHom
    with hφdef
  have hφ : Function.Injective φ := L.subtype_injective.comp e.symm.injective
  have hφr : φ.range = L := F4Pilot.range_subtype_comp_symm e
  set wC : graphFixedRootGroup TwistTag.E6 K σ := e ⟨w, hwL⟩ with hwCdef
  have hφw : φ wC = w := by simp [hφdef, hwCdef]
  have hw2 : orderOf w = 2 := by
    have h := orderOf_injective (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective t
    rw [← ht, ← h]
    congr 1
    simp [hwdef]
  have hwC2 : orderOf wC = 2 := by
    rw [← orderOf_injective φ hφ wC, hφw]
    exact hw2
  have hUtop : (U : Subgroup L) ≤ (e.symm.toMonoidHom).range := by
    rw [MonoidHom.range_eq_top.2 e.symm.surjective]
    exact le_top
  have hinj : Function.Injective e.symm.toMonoidHom := e.symm.injective
  set UC : Sylow 2 (graphFixedRootGroup TwistTag.E6 K σ) :=
    U.comapOfInjective e.symm.toMonoidHom hinj hUtop with hUC
  have hmemUC : ∀ c, c ∈ (UC : Subgroup (graphFixedRootGroup TwistTag.E6 K σ)) ↔
      e.symm c ∈ (U : Subgroup L) := by
    intro c
    rw [hUC, Sylow.coe_comapOfInjective, mem_comap]
    rfl
  have hwCU : ∀ s ∈ (UC : Subgroup (graphFixedRootGroup TwistTag.E6 K σ)), s * wC = wC * s := by
    intro c hc
    have h := hwU _ ((hmemUC c).1 hc)
    apply hφ
    rw [map_mul, map_mul, hφw]
    exact h
  have hPC := commutator_centralizer_of_twoCentral_two hk hK hσ hwC2 ⟨UC, hwCU⟩
  set P := (centralizer ({wC} : Set (graphFixedRootGroup TwistTag.E6 K σ))).map φ with hPdef
  have hPeq : P = L ⊓ centralizer ({w} : Set G) := by
    rw [hPdef, F4Pilot.map_centralizer_singleton hφ, hφr, hφw]
  have hP : ⁅P, P⁆ = P := by rw [hPdef, ← map_commutator, hPC]
  have hPL : P ≤ L := hPeq ▸ inf_le_left
  have hPw : P ≤ centralizer ({g⁻¹ * t * g} : Set G) := hPeq ▸ inf_le_right
  have hwP : g⁻¹ * t * g ∈ P := hPeq ▸ ⟨hwL, mem_centralizer_singleton_iff.2 rfl⟩
  exact LinearPilot.conj_not_mem_perfect hset hOut hZ htC ht g hP hPL hPw hwP

theorem mem_range_conj_of_sq_eq_one_of_fix_sylow_twistedE6_two (hk : Nat.card k = 2 ^ 1)
    (hK : Nat.card K = (2 ^ 1) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ 1)
    (e : L ≃* graphFixedRootGroup TwistTag.E6 K σ) :
    ∀ (U : Sylow 2 L) (β : MulAut L), β ^ 2 = 1 → (∀ u ∈ (U : Subgroup L), β u = u) →
      β ∈ (MulAut.conj : L →* MulAut L).range := by
  intro U β hβ hβU
  have : CharP K 2 := charP_two_of_card le_rfl hK
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; positivity)
  have := finite_of_card hK
  by_contra hin
  set β' := MulAut.congr e β with hβ'
  have hβ'2 : β' ^ 2 = 1 := by rw [hβ', ← map_pow, hβ, map_one]
  have hin' : β' ∉ (MulAut.conj : graphFixedRootGroup TwistTag.E6 K σ →*
      MulAut (graphFixedRootGroup TwistTag.E6 K σ)).range := by
    rintro ⟨c, hc⟩
    apply hin
    refine ⟨e.symm c, ?_⟩
    have h1 : MulAut.congr e (MulAut.conj (e.symm c)) = β' := by
      rw [congr_conj, MulEquiv.apply_symm_apply, hc]
    exact (MulAut.congr e).injective (h1.trans hβ')
  have hUtop : (U : Subgroup L) ≤ (e.symm.toMonoidHom).range := by
    rw [MonoidHom.range_eq_top.2 e.symm.surjective]
    exact le_top
  have hinj : Function.Injective e.symm.toMonoidHom := e.symm.injective
  set UC : Sylow 2 (graphFixedRootGroup TwistTag.E6 K σ) :=
    U.comapOfInjective e.symm.toMonoidHom hinj hUtop with hUC
  have hmemUC : ∀ c, c ∈ (UC : Subgroup (graphFixedRootGroup TwistTag.E6 K σ)) ↔
      e.symm c ∈ (U : Subgroup L) := by
    intro c
    rw [hUC, Sylow.coe_comapOfInjective, mem_comap]
    rfl
  have hUfix : (UC : Subgroup (graphFixedRootGroup TwistTag.E6 K σ)) ≤ fixedSubgroup β' := by
    intro c hc
    apply swapMem_fixedSubgroup_iff.2
    rw [hβ', MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
      hβU _ ((hmemUC c).1 hc), MulEquiv.apply_symm_apply]
  have h1 := (two_pow_dvd_card_sylow_twistedE6_two hK hσ UC).trans
    ((Subgroup.card_dvd_of_le hUfix).trans (card_fixedSubgroup_dvd_of_outer_two hk hK hσ β' hβ'2 hin'))
  rw [CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_F4, hk] at h1
  norm_num [CFSG.Open.ordF4] at h1

theorem isCyclic_map_outer_of_isPGroup_twistedE6_two (hK : Nat.card K = (2 ^ 1) ^ 2)
    {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ 1) (e : L ≃* graphFixedRootGroup TwistTag.E6 K σ) :
    ∀ B : Subgroup (MulAut L), IsPGroup 2 B →
      IsCyclic (B.map (QuotientGroup.mk' (inner L))) := by
  intro B hB
  have := finite_of_card hK
  have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  have : Finite (MulAut (graphFixedRootGroup TwistTag.E6 K σ)) := MulEquiv.finite_left
  have : Finite (MulAut L) := Finite.of_equiv _ (MulAut.congr e).symm.toEquiv
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set I := B.map (QuotientGroup.mk' (inner L)) with hI
  have hI2 : IsPGroup 2 I := hB.map _
  obtain ⟨m, hm⟩ := hI2.exists_card_eq
  have hdvd : Nat.card I ∣ Nat.card (Outer (graphFixedRootGroup TwistTag.E6 K σ)) := by
    rw [← Nat.card_congr (equivalence e).toEquiv]
    exact Subgroup.card_subgroup_dvd_card I
  have hv := factorization_card_outer_twistedE6 le_rfl hK σ hσ
  have hO0 : Nat.card (Outer (graphFixedRootGroup TwistTag.E6 K σ)) ≠ 0 := Nat.card_pos.ne'
  rw [hm] at hdvd
  have hle := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hO0).1 hdvd
  rw [hv] at hle
  have h1f : (1 : ℕ).factorization 2 = 0 := by simp
  rw [h1f] at hle
  rcases (by omega : m = 0 ∨ m = 1) with rfl | rfl
  · rw [pow_zero] at hm
    have : Subsingleton I := (Nat.card_eq_one_iff_unique.1 hm).1
    exact isCyclic_of_subsingleton
  · rw [pow_one] at hm
    exact isCyclic_of_prime_card hm

theorem exists_conj_eq_mul_twoSided_twistedE6_two (hset : StandardSetting G L)
    (hk : Nat.card k = 2 ^ 1) (hK : Nat.card K = (2 ^ 1) ^ 2) {σ : K →+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ 1) (e : L ≃* graphFixedRootGroup TwistTag.E6 K σ) {t : G}
    (ht : orderOf t = 2) (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) :
    ∃ x : G, ∃ z ∈ L ⊓ CFSG.conjugate L x, x⁻¹ * t * x = t * z ∧ z ≠ 1 ∧
      (∃ U : Sylow 2 L, ∀ u ∈ (U : Subgroup L), (u : G) * z = z * u) ∧
      (∃ U' : Sylow 2 (CFSG.conjugate L x),
        ∀ u ∈ (U' : Subgroup (CFSG.conjugate L x)), (u : G) * z = z * u) ∧
      ∀ l ∈ CFSG.conjugate L x, t * l * t⁻¹ = z * l * z⁻¹ := by
  have htK : t ∈ centralizer (L : Set G) ⊓ centralizer ({t} : Set G) := hKt ▸ mem_zpowers t
  have htC : t ∈ centralizer (L : Set G) := htK.1
  have hLt : L ≤ centralizer ({t} : Set G) := le_centralizer_of_mem_centralizer htC
  have hCN : centralizer ({t} : Set G) ≤ normalizer (L : Set G) :=
    centralizer_le_normalizer_of_standard hset.standard htC ht
  exact exists_conj_eq_mul_twoSided_of_commutator_eq_top_of_autU2
    (SeitzQ2.commutator_eq_top_of_standardSetting hset) ht hLt hCN hKt
    (not_forall_commute_sylow_conj_twistedE6_two hset hk hK hσ e htC ht)
    (mem_range_conj_of_sq_eq_one_of_fix_sylow_twistedE6_two hk hK hσ e)
    (commutator_mem_of_sylow_le_centralizer_of_isCyclic_outer_two htC ht hCN hKt
      (isCyclic_map_outer_of_isPGroup_twistedE6_two hK hσ e))

end Fusion

end CFSG.SeitzReduction.TwistedE6Pilot
