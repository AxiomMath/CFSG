module

public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotOuterFusionEta
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotFusionC2

public section

namespace CFSG.SeitzReduction.TwistedE6Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.EvenSmallLie
open CFSG.ComponentClassification.OuterAutomorphisms


section Invariance

variable {f : ℕ} {K : Type} [Field K] [CharP K 2]

theorem isConj_repXC_zero_map (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ f) (β : MulAut (graphFixedRootGroup TwistTag.E6 K σ))
    {x : graphFixedRootGroup TwistTag.E6 K σ} (hx : IsConj x (repXC (apply_apply_eq hK hσ) 0)) :
    IsConj (β x) (repXC (apply_apply_eq hK hσ) 0) := by
  have hr : orderOf (repXC (apply_apply_eq hK hσ) 0) = 2 := by
    rw [← Subgroup.orderOf_coe]
    exact orderOf_repX 0
  have hx2 : orderOf x = 2 := by
    obtain ⟨c, hc⟩ := isConj_iff.1 hx
    rw [← hr, ← hc, ← MulAut.conj_apply, MulEquiv.orderOf_eq]
  obtain ⟨S, hS⟩ := (isConj_repXC_zero_iff_twoCentral hf hK hσ hx2).1 hx
  refine (isConj_repXC_zero_iff_twoCentral hf hK hσ (by rw [MulEquiv.orderOf_eq]; exact hx2)).2
    ⟨β • S, fun s hs => ?_⟩
  rw [Sylow.pointwise_smul_def, mem_smul_pointwise_iff_exists] at hs
  obtain ⟨v, hv, rfl⟩ := hs
  rw [MulAut.smul_def, ← map_mul, ← map_mul, hS v hv]

@[expose] noncomputable def classVC {σ : K →+* K} (hσσ : ∀ c, σ (σ c) = c) :
    graphFixedRootGroup TwistTag.E6 K σ :=
  ⟨twistedE6ClassV K, twistedE6ClassV_mem_graphFixedRootGroup hσσ⟩

theorem isConj_repXC_or_classVC (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ f) {x : graphFixedRootGroup TwistTag.E6 K σ} (hx : orderOf x = 2) :
    IsConj x (repXC (apply_apply_eq hK hσ) 0) ∨ IsConj x (repXC (apply_apply_eq hK hσ) 1) ∨
      IsConj x (classVC (apply_apply_eq hK hσ)) := by
  have hx2 : x ^ 2 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  have hx1 : x ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hx
    omega
  obtain ⟨g, hg | hg | hg⟩ := exists_conj_repX_or_classV hf hK hσ hx2 hx1
  · exact Or.inl (isConj_iff.2 ⟨g, Subtype.ext hg⟩)
  · exact Or.inr (Or.inl (isConj_iff.2 ⟨g, Subtype.ext hg⟩))
  · exact Or.inr (Or.inr (isConj_iff.2 ⟨g, Subtype.ext hg⟩))

theorem isConj_repXC_one_map_of_pow_three (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 2)
    {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) (κ : MulAut (graphFixedRootGroup TwistTag.E6 K σ))
    (hκ : κ ^ 3 ∈ (MulAut.conj : graphFixedRootGroup TwistTag.E6 K σ →*
      MulAut (graphFixedRootGroup TwistTag.E6 K σ)).range) :
    IsConj (κ (repXC (apply_apply_eq hK hσ) 1)) (repXC (apply_apply_eq hK hσ) 1) := by
  have hu2 : orderOf (repXC (apply_apply_eq hK hσ) 1) = 2 := by
    rw [← Subgroup.orderOf_coe]
    exact orderOf_repX 1
  have hmap : ∀ (β : MulAut (graphFixedRootGroup TwistTag.E6 K σ)) {a b}, IsConj a b →
      IsConj (β a) (β b) := fun β _ _ h => (β.toMonoidHom).map_isConj h
  have hback : ∀ {a b}, IsConj (κ a) (κ b) → IsConj a b := fun h => by
    have h' := hmap κ⁻¹ h
    rwa [MulAut.inv_apply, MulAut.inv_apply, MulEquiv.symm_apply_apply,
      MulEquiv.symm_apply_apply] at h'
  have htback : ∀ {a}, IsConj (κ a) (repXC (apply_apply_eq hK hσ) 0) →
      IsConj a (repXC (apply_apply_eq hK hσ) 0) := fun h => by
    have h' := isConj_repXC_zero_map hf hK hσ κ⁻¹ h
    rwa [MulAut.inv_apply, MulEquiv.symm_apply_apply] at h'
  by_contra hne
  have hκu2 : orderOf (κ (repXC (apply_apply_eq hK hσ) 1)) = 2 := by
    rw [MulEquiv.orderOf_eq]; exact hu2
  rcases isConj_repXC_or_classVC hf hK hσ hκu2 with h | h | hv
  · exact hne (h.trans (htback h).symm)
  · exact hne h
  ·
    have hv1 : classVC (apply_apply_eq hK hσ) ≠ 1 := by
      intro h1
      rw [h1, isConj_one_left] at hv
      have : repXC (apply_apply_eq hK hσ) 1 = 1 := κ.injective (hv.trans (map_one κ).symm)
      rw [this, orderOf_one] at hu2
      omega
    have hv2 : orderOf (classVC (apply_apply_eq hK hσ)) = 2 := by
      refine orderOf_eq_prime ?_ hv1
      exact Subtype.ext (twistedE6ClassV_sq (K := K))
    have hκv2 : orderOf (κ (classVC (apply_apply_eq hK hσ))) = 2 := by
      rw [MulEquiv.orderOf_eq]; exact hv2
    rcases isConj_repXC_or_classVC hf hK hσ hκv2 with h | h | h
    · have hvt := htback h
      have hut := htback (hv.trans hvt)
      exact hne ((hv.trans hvt).trans hut.symm)
    ·
      have h2 := (hmap κ hv).trans h
      have h3 := (hmap κ h2).trans hv
      obtain ⟨c, hc⟩ := hκ
      have h4 : IsConj (κ (κ (κ (repXC (apply_apply_eq hK hσ) 1))))
          (repXC (apply_apply_eq hK hσ) 1) := by
        have e : κ (κ (κ (repXC (apply_apply_eq hK hσ) 1))) =
            (κ ^ 3) (repXC (apply_apply_eq hK hσ) 1) := by
          rw [pow_three]
          rfl
        rw [e, ← hc, MulAut.conj_apply]
        exact (isConj_iff.2 ⟨c, rfl⟩).symm
      exact hne (hv.trans (h3.symm.trans h4))
    ·
      exact hne (hv.trans (hback (h.trans hv.symm)))

theorem classTU_map (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ f) (β : MulAut (graphFixedRootGroup TwistTag.E6 K σ))
    {x : graphFixedRootGroup TwistTag.E6 K σ} (hx : x ∈ classTU (apply_apply_eq hK hσ)) :
    β x ∈ classTU (apply_apply_eq hK hσ) := by
  have hmap : ∀ (γ : MulAut (graphFixedRootGroup TwistTag.E6 K σ)) {a b}, IsConj a b →
      IsConj (γ a) (γ b) := fun γ _ _ h => (γ.toMonoidHom).map_isConj h
  rcases hx with hx | hx
  · exact Or.inl (isConj_repXC_zero_map hf hK hσ β hx)
  · refine Or.inr ((hmap β hx).trans ?_)
    have := finite_of_card hK
    obtain ⟨σE, rfl⟩ := exists_ringEquiv_toRingHom_eq σ
    obtain ⟨-, -, -, -, -, -, hcoeδ, hNF, ⟨Θ, -, -, hΘker, -, hexp, -⟩, -⟩ :=
      twisted_E6_all_characteristic_exact_automorphism_normal_form Nat.prime_two hf K hK σE hσ
    obtain ⟨g, u, δ, rfl⟩ := hNF β
    have hδ : fieldActor σE δ (repXC (apply_apply_eq hK hσ) 1) = repXC (apply_apply_eq hK hσ) 1 := by
      refine Subtype.ext ?_
      rw [hcoeδ]
      change Units.map (entrywiseHom δ.toRingHom)
          (pinnedX TwistTag.E6.tag K rootE15 1 * pinnedX TwistTag.E6.tag K rootE26 1) =
        pinnedX TwistTag.E6.tag K rootE15 1 * pinnedX TwistTag.E6.tag K rootE26 1
      have hfix : ∀ r : Fin TwistTag.E6.tag.rank → ℤ,
          Units.map (entrywiseHom δ.toRingHom) (pinnedX TwistTag.E6.tag K r 1) =
            pinnedX TwistTag.E6.tag K r 1 := fun r =>
        Units.ext ((entrywise_pinnedX δ.toRingHom r 1).trans (by rw [map_one]))
      rw [map_mul, hfix, hfix]
    have hΔ3 : compatDiagAutHom TwistTag.E6 K σE.toRingHom u ^ 3 ∈
        (MulAut.conj : graphFixedRootGroup TwistTag.E6 K σE.toRingHom →*
          MulAut (graphFixedRootGroup TwistTag.E6 K σE.toRingHom)).range := by
      have hmem : compatDiagAutHom TwistTag.E6 K σE.toRingHom u ∈
          twistedE6Inn K σE ⊔ twistedE6Diag K σE := mem_sup_right ⟨u, rfl⟩
      have h1 := hexp (QuotientGroup.mk ⟨_, hmem⟩)
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, mem_subgroupOf] at h1
      exact h1
    have hκ := isConj_repXC_one_map_of_pow_three hf hK hσ _ hΔ3
    rw [MulAut.mul_apply, MulAut.mul_apply, hδ, MulAut.conj_apply]
    exact (isConj_iff.2 ⟨g, rfl⟩).symm.trans hκ

end Invariance

section Dist


theorem card_eqLocus_xiAut_lt_etaAut {f : ℕ} (hf : 1 ≤ f) {k K : Type} [Field k] [Field K]
    [CharP K 2] [Algebra k K] (hk : Nat.card k = 2 ^ f) (hK : Nat.card K = (2 ^ f) ^ 2)
    (σ : K →+* K) (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    Nat.card ((xiAut σ (apply_apply_eq hK hσ)).toMonoidHom.eqLocus
        (MonoidHom.id (graphFixedRootGroup TwistTag.E6 K σ))) <
      Nat.card ((etaAut σ (apply_apply_eq hK hσ)).toMonoidHom.eqLocus
        (MonoidHom.id (graphFixedRootGroup TwistTag.E6 K σ))) := by
  have := finite_of_card hK
  have : Finite k := F4Pilot.finite_of_natCard_eq_two_pow hk
  set hσσ := apply_apply_eq hK hσ with hσσdef
  obtain ⟨-, ⟨⟨η', hη', -, hJC, hfixJ, -⟩, e, -⟩⟩ :=
    even_E6_twisted_E6_canonical_graph_fixed_subgroup f hf k K hk hK σ hσ
  obtain ⟨-, -, -, -, -, ⟨e₂, -, -, hsec⟩⟩ :=
    even_E6_twisted_E6_second_graph_fixed_subgroup f hf k K hk hK σ hσ
  obtain ⟨htJ, hJC', η₀, hη₀, -, -, -, hfixξ, -, -, -, -⟩ := hsec
  have hη'e : η' = etaAut σ hσσ := MulEquiv.ext fun g => Subtype.ext (by rw [hη', coe_etaAut])
  have hη₀e : η₀ = etaAut σ hσσ := MulEquiv.ext fun g => Subtype.ext (by rw [hη₀, coe_etaAut])
  have hξe : MulAut.conj (⟨_, hJC' htJ⟩ : graphFixedRootGroup TwistTag.E6 K σ) * η₀ =
      xiAut σ hσσ := by
    rw [hη₀e]
    rfl
  set Fξ := (xiAut σ hσσ).toMonoidHom.eqLocus (MonoidHom.id (graphFixedRootGroup TwistTag.E6 K σ))
  set Fη := (etaAut σ hσσ).toMonoidHom.eqLocus (MonoidHom.id (graphFixedRootGroup TwistTag.E6 K σ))
  have hmemξ : ∀ g, g ∈ Fξ ↔ ((g : ModGL TwistTag.E6.tag K) ∈
      (twistedFixedGroup TwistTag.E6 k (RingHom.id k)).map (baseChangeGL (algebraMap k K)) ∧
        pinnedX TwistTag.E6.tag K e6HighestRoot 1 * g = g * pinnedX TwistTag.E6.tag K e6HighestRoot 1) :=
    fun g => by
      rw [← hfixξ g, hξe]
      rfl
  have hmemη : ∀ g, g ∈ Fη ↔ (g : ModGL TwistTag.E6.tag K) ∈
      (twistedFixedGroup TwistTag.E6 k (RingHom.id k)).map (baseChangeGL (algebraMap k K)) :=
    fun g => by
      rw [← hfixJ g, hη'e]
      rfl
  have hle : Fξ ≤ Fη := fun g hg => (hmemη g).2 ((hmemξ g).1 hg).1
  refine card_lt_of_lt (lt_of_le_of_ne hle fun heq => ?_)
  have hcomm : ∀ x : (twistedFixedGroup TwistTag.E6 k (RingHom.id k)).map
      (baseChangeGL (algebraMap k K)), x * ⟨_, htJ⟩ = ⟨_, htJ⟩ * x := by
    intro x
    have hx : (⟨x, hJC x.2⟩ : graphFixedRootGroup TwistTag.E6 K σ) ∈ Fξ :=
      heq ▸ (hmemη _).2 x.2
    exact Subtype.ext ((hmemξ _).1 hx).2.symm
  have hZ : e ⟨_, htJ⟩ ∈ center (adjointGroup Tag.F4 k) := mem_center_iff.2 fun y => by
    obtain ⟨x, rfl⟩ := e.surjective y
    rw [← map_mul, ← map_mul, hcomm x]
  rw [center_adjointGroup_eq_bot, mem_bot, ← map_one e] at hZ
  have h1 := congrArg Subtype.val (e.injective hZ)
  exact pinnedX_highRoot_one_ne_one h1

end Dist

section C1

variable
  {G : Type} [Group G] [Finite G] {L : Subgroup G}

omit
  [Finite G] in
theorem outer_solvable_and_center_eq_bot_twistedE6 {f : ℕ} {K : Type} [Field K]
    (hK : Nat.card K = (2 ^ f) ^ 2) (σ : K →+* K) (e : L ≃* graphFixedRootGroup TwistTag.E6 K σ) :
    Group.IsSolvable (Outer L) ∧ center L = ⊥ := by
  have := finite_of_card hK
  obtain ⟨σE, hσE⟩ := exists_ringEquiv_toRingHom_eq σ
  subst hσE
  exact ⟨⟨⟨5, derivedSeries_outer_eq_bot_of_mulEquiv e
      ((exceptional_fixed_root_group_Schreier TwistTag.E6 K σE).1 rfl)⟩⟩,
    F4Pilot.center_eq_bot_congr e.symm (exceptional_fixed_center_trivial TwistTag.E6 K σE)⟩

theorem outerFusionIn_twistedE6 (hset : StandardSetting G L) {f : ℕ} (hf : 1 ≤ f) {k K : Type}
    [Field k] [Field K] [CharP K 2] [Algebra k K] (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) (σ : K →+* K) (hσ : ∀ c, σ c = c ^ 2 ^ f)
    (e : L ≃* graphFixedRootGroup TwistTag.E6 K σ)
    (hperf : ∀ w ∈ L, orderOf w = 2 → ∃ P : Subgroup G, ⁅P, P⁆ = P ∧ w ∈ P ∧ P ≤ L ∧
      P ≤ centralizer ({w} : Set G))
    (hξ : TwistedFusionIn (xiAut σ (apply_apply_eq hK hσ)) (classTU (apply_apply_eq hK hσ)))
    {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) :
    OuterFusionIn L e t (classTU (apply_apply_eq hK hσ)) := by
  set hσσ := apply_apply_eq hK hσ with hσσdef
  obtain ⟨hOut, hZ⟩ := outer_solvable_and_center_eq_bot_twistedE6 hK σ e
  set η : Fin 2 → MulAut (graphFixedRootGroup TwistTag.E6 K σ) := ![etaAut σ hσσ, xiAut σ hσσ]
    with hηdef
  have hcan : ∀ α : MulAut (graphFixedRootGroup TwistTag.E6 K σ), α ^ 2 = 1 →
      α ∉ (MulAut.conj : graphFixedRootGroup TwistTag.E6 K σ →*
        MulAut (graphFixedRootGroup TwistTag.E6 K σ)).range →
      ∃ (i : Fin 2) (ψ : MulAut (graphFixedRootGroup TwistTag.E6 K σ)), ψ * α * ψ⁻¹ = η i := by
    intro α hα hαo
    rcases (conj_etaAut_or_xiAut_of_outer hf hK σ hσ).1 α hα hαo with ⟨ψ, hψ⟩ | ⟨ψ, hψ⟩
    · exact ⟨0, ψ, hψ⟩
    · exact ⟨1, ψ, hψ⟩
  have hlt := card_eqLocus_xiAut_lt_etaAut hf hk hK σ hσ
  have hdist : ∀ i j, Nat.card ((η i).toMonoidHom.eqLocus
      (MonoidHom.id (graphFixedRootGroup TwistTag.E6 K σ))) =
      Nat.card ((η j).toMonoidHom.eqLocus
        (MonoidHom.id (graphFixedRootGroup TwistTag.E6 K σ))) → i = j := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · rfl
    · exact absurd hij (by simpa [hηdef] using hlt.ne')
    · exact absurd hij (by simpa [hηdef] using hlt.ne)
    · rfl
  have hη : ∀ i, TwistedFusionIn (η i) (classTU hσσ) := by
    intro i
    fin_cases i
    · exact twistedFusionIn_etaAut hf hk hK σ hσ
    · exact hξ
  exact outerFusionIn_of_twistedFusionIn hset hOut hZ hperf e η hcan hdist (classTU hσσ)
    (fun β x hx => classTU_map hf hK hσ β hx) hη ht hKt

theorem exists_conj_eq_mul_repXC_of_outer_twistedE6 (hset : StandardSetting G L) {f : ℕ}
    (hf : 1 ≤ f) {k K : Type} [Field k] [Field K] [CharP K 2] [Algebra k K]
    (hk : Nat.card k = 2 ^ f) (hK : Nat.card K = (2 ^ f) ^ 2) (σ : K →+* K)
    (hσ : ∀ c, σ c = c ^ 2 ^ f) (e : L ≃* graphFixedRootGroup TwistTag.E6 K σ)
    (hperf : ∀ w ∈ L, orderOf w = 2 → ∃ P : Subgroup G, ⁅P, P⁆ = P ∧ w ∈ P ∧ P ≤ L ∧
      P ≤ centralizer ({w} : Set G))
    (hξ : TwistedFusionIn (xiAut σ (apply_apply_eq hK hσ)) (classTU (apply_apply_eq hK hσ)))
    {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) {g : G}
    (hsC : g⁻¹ * t * g ∈ centralizer ({t} : Set G)) (hsL : g⁻¹ * t * g ∉ L ⊔ zpowers t) :
    ∃ (κ : Fin 2) (h : G), h⁻¹ * t * h = t * (e.symm (repXC (apply_apply_eq hK hσ) κ) : G) := by
  have htK : t ∈ centralizer (L : Set G) ⊓ centralizer ({t} : Set G) := hKt ▸ mem_zpowers t
  exact exists_conj_eq_mul_rep_of_outerFusionIn
    (outerFusionIn_twistedE6 hset hf hk hK σ hσ e hperf hξ ht hKt) htK.1
    (repXC (apply_apply_eq hK hσ)) (fun x hx => by
      rcases hx with hx | hx
      · exact ⟨0, hx⟩
      · exact ⟨1, hx⟩) hsC hsL

theorem exists_conj_eq_mul_repXC_twistedE6 (hset : StandardSetting G L) {f : ℕ} (hf : 1 ≤ f)
    {k K : Type} [Field k] [Field K] [CharP K 2] [Algebra k K] (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) (σ : K →+* K) (hσ : ∀ c, σ c = c ^ 2 ^ f)
    (e : L ≃* graphFixedRootGroup TwistTag.E6 K σ)
    (hperf : ∀ w ∈ L, orderOf w = 2 → ∃ P : Subgroup G, ⁅P, P⁆ = P ∧ w ∈ P ∧ P ≤ L ∧
      P ≤ centralizer ({w} : Set G))
    (hξ : TwistedFusionIn (xiAut σ (apply_apply_eq hK hσ)) (classTU (apply_apply_eq hK hσ)))
    {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) :
    ∃ (κ : Fin 2) (h : G), h⁻¹ * t * h = t * (e.symm (repXC (apply_apply_eq hK hσ) κ) : G) := by
  by_cases hout : ∃ g : G, g⁻¹ * t * g ∈ centralizer ({t} : Set G) ∧
      g⁻¹ * t * g ∉ L ⊔ zpowers t
  · obtain ⟨g, hsC, hsL⟩ := hout
    exact exists_conj_eq_mul_repXC_of_outer_twistedE6 hset hf hk hK σ hσ e hperf hξ ht hKt hsC hsL
  · simp only [not_exists, not_and, not_not] at hout
    have htK : t ∈ centralizer (L : Set G) ⊓ centralizer ({t} : Set G) := hKt ▸ mem_zpowers t
    obtain ⟨hOut, hZ⟩ := outer_solvable_and_center_eq_bot_twistedE6 hK σ e
    exact ⟨0, exists_conj_eq_mul_repXC_zero_of_forall_inner_twistedE6 hset hf hK σ hσ e ht hKt
      (F4Pilot.conj_not_mem_of_forall_perfect hset hOut hZ hperf htK.1 ht) hout⟩

end C1

end CFSG.SeitzReduction.TwistedE6Pilot
