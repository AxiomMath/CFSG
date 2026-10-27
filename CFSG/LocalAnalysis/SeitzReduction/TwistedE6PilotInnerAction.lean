module

public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotInnerActionBasic
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotPerfect
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotInnerActionOuter
public import CFSG.LieType.Chevalley.GraphTwistedOuterTwoPart
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotOuterFusionEta

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.TwistedE6Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.EvenSmallLie
open CFSG.ComponentClassification.OuterAutomorphisms

section Fixed

variable {f : ℕ} {k K : Type} [Field k] [Field K] [Algebra k K]

theorem eqLocus_etaAut_eq [CharP K 2] (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) (σ : K →+* K) (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    (etaAut σ (apply_apply_eq hK hσ)).toMonoidHom.eqLocus
        (MonoidHom.id (graphFixedRootGroup TwistTag.E6 K σ)) =
      ((twistedFixedGroup TwistTag.E6 k (RingHom.id k)).map
        (baseChangeGL (algebraMap k K))).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ) := by
  obtain ⟨-, ⟨⟨η', hη', -, -, hfixJ, -⟩, -, -⟩⟩ :=
    even_E6_twisted_E6_canonical_graph_fixed_subgroup f hf k K hk hK σ hσ
  have hη'e : η' = etaAut σ (apply_apply_eq hK hσ) :=
    MulEquiv.ext fun g => Subtype.ext (by rw [hη', coe_etaAut])
  ext g
  rw [mem_subgroupOf, ← hfixJ g, hη'e]
  rfl

theorem card_eqLocus_etaAut [CharP K 2] (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) (σ : K →+* K) (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    Nat.card ((etaAut σ (apply_apply_eq hK hσ)).toMonoidHom.eqLocus
        (MonoidHom.id (graphFixedRootGroup TwistTag.E6 K σ))) =
      Nat.card (adjointGroup Tag.F4 k) := by
  obtain ⟨-, ⟨⟨-, -, -, hJC, -, -⟩, e, -⟩⟩ :=
    even_E6_twisted_E6_canonical_graph_fixed_subgroup f hf k K hk hK σ hσ
  rw [eqLocus_etaAut_eq hf hk hK σ hσ, ← Nat.card_congr e.toEquiv]
  exact Nat.card_congr (subgroupOfEquivOfLe hJC).toEquiv

theorem factorization_card_eqLocus_etaAut [CharP K 2] (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) (σ : K →+* K) (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    (Nat.card ((etaAut σ (apply_apply_eq hK hσ)).toMonoidHom.eqLocus
        (MonoidHom.id (graphFixedRootGroup TwistTag.E6 K σ)))).factorization 2 = 24 * f := by
  have : Finite k := F4Pilot.finite_of_natCard_eq_two_pow hk
  have : CharP k 2 := F4Pilot.charP_two_of_natCard_eq_two_pow hk
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [card_eqLocus_etaAut hf hk hK σ hσ, E6Pilot.factorization_card_adjointGroup hk,
    CFSG.Timmesfeld.ExceptionalOrders.ncard_posRoots_F4, mul_comm]

theorem eqLocus_xiAut_le_etaAut [CharP K 2] (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) (σ : K →+* K) (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    (xiAut σ (apply_apply_eq hK hσ)).toMonoidHom.eqLocus
        (MonoidHom.id (graphFixedRootGroup TwistTag.E6 K σ)) ≤
      (etaAut σ (apply_apply_eq hK hσ)).toMonoidHom.eqLocus
        (MonoidHom.id (graphFixedRootGroup TwistTag.E6 K σ)) := by
  set hσσ := apply_apply_eq hK hσ with hσσdef
  obtain ⟨-, -, -, -, -, ⟨e₂, -, -, hsec⟩⟩ :=
    even_E6_twisted_E6_second_graph_fixed_subgroup f hf k K hk hK σ hσ
  obtain ⟨htJ, hJC', η₀, hη₀, -, -, -, hfixξ, -, -, -, -⟩ := hsec
  have hη₀e : η₀ = etaAut σ hσσ := MulEquiv.ext fun g => Subtype.ext (by rw [hη₀, coe_etaAut])
  have hξe : MulAut.conj (⟨_, hJC' htJ⟩ : graphFixedRootGroup TwistTag.E6 K σ) * η₀ =
      xiAut σ hσσ := by
    rw [hη₀e]
    rfl
  intro g hg
  have hg' : (g : ModGL TwistTag.E6.tag K) ∈
      (twistedFixedGroup TwistTag.E6 k (RingHom.id k)).map (baseChangeGL (algebraMap k K)) := by
    have h := (hfixξ g).1 (by rw [hξe]; exact hg)
    exact h.1
  have h := eqLocus_etaAut_eq hf hk hK σ hσ
  rw [← hσσdef] at h
  rw [h]
  exact mem_subgroupOf.2 hg'

theorem factorization_card_eqLocus_xiAut_le [CharP K 2] (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) (σ : K →+* K) (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    (Nat.card ((xiAut σ (apply_apply_eq hK hσ)).toMonoidHom.eqLocus
        (MonoidHom.id (graphFixedRootGroup TwistTag.E6 K σ)))).factorization 2 ≤ 24 * f := by
  have := finite_of_card hK
  have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  rw [← factorization_card_eqLocus_etaAut hf hk hK σ hσ]
  exact (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').2
    (Subgroup.card_dvd_of_le (eqLocus_xiAut_le_etaAut hf hk hK σ hσ)) 2

end Fixed

section Outer

variable {f : ℕ} {k K : Type} [Field k] [Field K] [Algebra k K]

theorem factorization_card_outer_twistedE6 (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 2)
    (σ : K →+* K) (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    (Nat.card (Outer (graphFixedRootGroup TwistTag.E6 K σ))).factorization 2 =
      f.factorization 2 + 1 := by
  have := finite_of_card hK
  obtain ⟨σE, rfl⟩ := exists_ringEquiv_toRingHom_eq σ
  have h := ordProj_two_card_outer_twistedE6 Nat.prime_two hf hK σE (fun c => hσ c)
  rw [← pow_succ'] at h
  exact Nat.pow_right_injective (le_refl 2) h

theorem not_two_pow_dvd_card_centralizer_outer_twistedE6 [CharP K 2] (hf : 1 ≤ f)
    (hk : Nat.card k = 2 ^ f) (hK : Nat.card K = (2 ^ f) ^ 2) (σ : K →+* K)
    (hσ : ∀ c, σ c = c ^ 2 ^ f) (β : MulAut (graphFixedRootGroup TwistTag.E6 K σ))
    (hβ : orderOf β = 2) (hβo : β ∉ inner (graphFixedRootGroup TwistTag.E6 K σ)) :
    ¬ 2 ^ (26 * f) ∣
      Nat.card (centralizer ({β} : Set (MulAut (graphFixedRootGroup TwistTag.E6 K σ)))) := by
  have := finite_of_card hK
  have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  have : Finite (MulAut (graphFixedRootGroup TwistTag.E6 K σ)) := MulEquiv.finite_left
  have hZ : center (graphFixedRootGroup TwistTag.E6 K σ) = ⊥ :=
    center_graphFixedRootGroup_eq_bot (Finite.surjective_of_injective σ.injective)
  have hβ2 : β ^ 2 = 1 := hβ ▸ pow_orderOf_eq_one β
  have hOut := factorization_card_outer_twistedE6 hf hK σ hσ
  have hlt : f.factorization 2 < f := Nat.factorization_lt 2 (by omega)
  have key : ∀ β₀ : MulAut (graphFixedRootGroup TwistTag.E6 K σ),
      (∃ φ : MulAut (graphFixedRootGroup TwistTag.E6 K σ), φ * β * φ⁻¹ = β₀) →
      (Nat.card (β₀.toMonoidHom.eqLocus
        (MonoidHom.id (graphFixedRootGroup TwistTag.E6 K σ)))).factorization 2 ≤ 24 * f →
      ¬ 2 ^ (26 * f) ∣
        Nat.card (centralizer ({β} : Set (MulAut (graphFixedRootGroup TwistTag.E6 K σ)))) := by
    rintro β₀ ⟨φ, rfl⟩ hb hdvd
    rw [← E6Pilot.card_centralizer_conj φ β] at hdvd
    have h3 := hdvd.trans (E6Pilot.card_centralizer_dvd_card_eqLocus_mul_card_outer hZ
      (φ * β * φ⁻¹))
    have hF0 : Nat.card ((φ * β * φ⁻¹).toMonoidHom.eqLocus
        (MonoidHom.id (graphFixedRootGroup TwistTag.E6 K σ))) ≠ 0 :=
      Nat.card_pos.ne'
    have hO0 : Nat.card (Outer (graphFixedRootGroup TwistTag.E6 K σ)) ≠ 0 := Nat.card_pos.ne'
    have h4 := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two (mul_ne_zero hF0 hO0)).1 h3
    rw [Nat.factorization_mul hF0 hO0, Finsupp.add_apply, hOut] at h4
    omega
  rcases (conj_etaAut_or_xiAut_of_outer hf hK σ hσ).1 β hβ2 (fun h => hβo h) with h | h
  · exact key _ h (factorization_card_eqLocus_etaAut hf hk hK σ hσ).le
  · exact key _ h (factorization_card_eqLocus_xiAut_le hf hk hK σ hσ)

end Outer

section Inner

variable {f : ℕ} {k K : Type} [Field k] [Field K] [Algebra k K]

theorem two_pow_dvd_card_centralizer_stdRepC [CharP K 2] (hf : 2 ≤ f) (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) (κ : Fin 2) :
    2 ^ (26 * f) ∣ Nat.card (centralizer ({stdRepC (apply_apply_eq hK hσ) κ} :
      Set (graphFixedRootGroup TwistTag.E6 K σ))) := by
  obtain rfl | rfl : κ = 0 ∨ κ = 1 := by
    rcases κ with ⟨_ | _ | κ, hκ⟩
    · exact Or.inl rfl
    · exact Or.inr rfl
    · omega
  · exact (pow_dvd_pow 2 (by omega : 26 * f ≤ 36 * f)).trans
      (two_pow_dvd_card_centralizer_stdRepC_zero (by omega) hK hσ)
  · exact (pow_dvd_pow 2 (by omega : 26 * f ≤ 33 * f)).trans
      (two_pow_dvd_card_centralizer_stdRepC_one (k := k) hf hk hK hσ)

theorem two_pow_dvd_card_centralizer_of_isConj_stdRepC [CharP K 2] (hf : 2 ≤ f)
    (hk : Nat.card k = 2 ^ f) (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ f) {x : graphFixedRootGroup TwistTag.E6 K σ} {κ : Fin 2}
    (hx : IsConj x (stdRepC (apply_apply_eq hK hσ) κ)) :
    2 ^ (26 * f) ∣ Nat.card (centralizer ({x} : Set (graphFixedRootGroup TwistTag.E6 K σ))) := by
  obtain ⟨c, hc⟩ := isConj_iff.1 hx
  rw [← E6Pilot.card_centralizer_conj c x, hc]
  exact two_pow_dvd_card_centralizer_stdRepC hf hk hK hσ κ

theorem isConj_repXC_stdRepC [CharP K 2] {σ : K →+* K} (hσσ : ∀ c, σ (σ c) = c) (κ : Fin 2) :
    IsConj (repXC hσσ κ) (stdRepC hσσ κ) := by
  rw [repXC_eq_conj hσσ κ]
  exact (isConj_iff.2 ⟨relWeylC σ (repWordX κ), rfl⟩).symm

theorem two_pow_dvd_card_centralizer_of_mem_classTU [CharP K 2] (hf : 2 ≤ f)
    (hk : Nat.card k = 2 ^ f) (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ f) {x : graphFixedRootGroup TwistTag.E6 K σ}
    (hx : x ∈ classTU (apply_apply_eq hK hσ)) :
    2 ^ (26 * f) ∣ Nat.card (centralizer ({x} : Set (graphFixedRootGroup TwistTag.E6 K σ))) := by
  rcases hx with hx | hx
  · exact two_pow_dvd_card_centralizer_of_isConj_stdRepC hf hk hK hσ
      (hx.trans (isConj_repXC_stdRepC _ 0))
  · exact two_pow_dvd_card_centralizer_of_isConj_stdRepC hf hk hK hσ
      (hx.trans (isConj_repXC_stdRepC _ 1))

theorem repYC_mem_classTU [CharP K 2] {σ : K →+* K} (hσσ : ∀ c, σ (σ c) = c) (κ : Fin 2) :
    repYC hσσ κ ∈ classTU hσσ := by
  obtain rfl | rfl : κ = 0 ∨ κ = 1 := by
    rcases κ with ⟨_ | _ | κ, hκ⟩
    · exact Or.inl rfl
    · exact Or.inr rfl
    · omega
  · exact Or.inl (isConj_repXC_repYC hσσ 0).symm
  · exact Or.inr (isConj_repXC_repYC hσσ 1).symm

theorem repXC_mem_classTU [CharP K 2] {σ : K →+* K} (hσσ : ∀ c, σ (σ c) = c) (κ : Fin 2) :
    repXC hσσ κ ∈ classTU hσσ := by
  obtain rfl | rfl : κ = 0 ∨ κ = 1 := by
    rcases κ with ⟨_ | _ | κ, hκ⟩
    · exact Or.inl rfl
    · exact Or.inr rfl
    · omega
  · exact Or.inl (IsConj.refl _)
  · exact Or.inr (IsConj.refl _)

end Inner

section Action

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {k K : Type} [Field k]
  [Field K] [Algebra k K]

theorem exists_inner_twistedE6 (hset : StandardSetting G L) [CharP K 2] (hf : 2 ≤ f)
    (hk : Nat.card k = 2 ^ f) (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ f) (e : L ≃* graphFixedRootGroup TwistTag.E6 K σ) {t : G}
    (ht : orderOf t = 2) (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {x : graphFixedRootGroup TwistTag.E6 K σ} (hx : x ∈ classTU (apply_apply_eq hK hσ)) {g : G}
    (hg : g⁻¹ * t * g = (e.symm x : G) ∨ g⁻¹ * t * g = t * (e.symm x : G))
    (hne : g⁻¹ * t * g ≠ t) :
    ∃ w' ∈ CFSG.conjugate L g, ∀ l ∈ CFSG.conjugate L g, t * l * t⁻¹ = w' * l * w'⁻¹ := by
  have := finite_of_card hK
  exact exists_inner_of_two_pow_dvd_of_eq hset e
    (center_graphFixedRootGroup_eq_bot (Finite.surjective_of_injective σ.injective)) ht hKt
    (26 * f) (fun β hβ hβo => not_two_pow_dvd_card_centralizer_outer_twistedE6 (k := k)
      (by omega) hk hK σ hσ β hβ hβo)
    (two_pow_dvd_card_centralizer_of_mem_classTU hf hk hK hσ hx) hg hne

theorem mul_ne_self_of_ne_one {t y : G} (hy : y ≠ 1) : t * y ≠ t := fun h =>
  hy (by simpa using h)

theorem coe_symm_ne_one_of_orderOf {M : Type*} [Group M] (e : L ≃* M) {x : M}
    (hx : orderOf x = 2) : (e.symm x : G) ≠ 1 := by
  intro h
  have h1 : e.symm x = 1 := Subtype.ext h
  have hx1 : x = 1 := by rw [← e.apply_symm_apply x, h1, map_one]
  rw [hx1, orderOf_one] at hx
  exact absurd hx (by norm_num)

theorem exists_inner_repXC_twistedE6 (hset : StandardSetting G L) [CharP K 2] (hf : 2 ≤ f)
    (hk : Nat.card k = 2 ^ f) (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ f) (e : L ≃* graphFixedRootGroup TwistTag.E6 K σ) {t : G}
    (ht : orderOf t = 2) (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {κ : Fin 2} {g : G} (hg : g⁻¹ * t * g = t * (e.symm (repXC (apply_apply_eq hK hσ) κ) : G)) :
    ∃ w' ∈ CFSG.conjugate L g, ∀ l ∈ CFSG.conjugate L g, t * l * t⁻¹ = w' * l * w'⁻¹ := by
  have hord : orderOf (repXC (apply_apply_eq hK hσ) κ) = 2 := by
    rw [← Subgroup.orderOf_coe]
    exact orderOf_repX κ
  exact exists_inner_twistedE6 hset hf hk hK hσ e ht hKt (repXC_mem_classTU _ κ) (Or.inr hg)
    (hg ▸ mul_ne_self_of_ne_one (coe_symm_ne_one_of_orderOf e hord))

theorem exists_inner_repYC_twistedE6 (hset : StandardSetting G L) [CharP K 2] (hf : 2 ≤ f)
    (hk : Nat.card k = 2 ^ f) (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ f) (e : L ≃* graphFixedRootGroup TwistTag.E6 K σ) {t : G}
    (ht : orderOf t = 2) (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {κ : Fin 2} {g : G} (hg : g⁻¹ * t * g = t * (e.symm (repYC (apply_apply_eq hK hσ) κ) : G)) :
    ∃ w' ∈ CFSG.conjugate L g, ∀ l ∈ CFSG.conjugate L g, t * l * t⁻¹ = w' * l * w'⁻¹ := by
  have hord : orderOf (repYC (apply_apply_eq hK hσ) κ) = 2 := by
    rw [← Subgroup.orderOf_coe]
    exact orderOf_repY κ
  exact exists_inner_twistedE6 hset hf hk hK hσ e ht hKt (repYC_mem_classTU _ κ) (Or.inr hg)
    (hg ▸ mul_ne_self_of_ne_one (coe_symm_ne_one_of_orderOf e hord))

end Action

end CFSG.SeitzReduction.TwistedE6Pilot
