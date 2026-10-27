module

public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotSwapPair

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.TwistedE6Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.EvenSmallLie
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

@[expose] def uCentRootList : List (Fin TwistTag.E6.tag.rank → ℤ) :=
  [![0, 0, 0, 0, 0, 1], ![0, 0, 0, 1, 0, 0], ![0, 1, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 1, 1], ![0, 1, 0, 1, 0, 0], ![1, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 1, 1],
    ![0, 0, 1, 1, 1, 0], ![1, 0, 1, 1, 0, 0], ![0, 0, 1, 1, 1, 1], ![0, 1, 0, 1, 1, 1],
    ![0, 1, 1, 1, 1, 0], ![1, 0, 1, 1, 1, 0], ![1, 1, 1, 1, 0, 0], ![0, 1, 1, 1, 1, 1],
    ![0, 1, 1, 2, 1, 0], ![1, 0, 1, 1, 1, 1], ![1, 1, 1, 1, 1, 0], ![0, 1, 1, 2, 1, 1],
    ![1, 1, 1, 1, 1, 1], ![1, 1, 1, 2, 1, 0], ![0, 1, 1, 2, 2, 1], ![1, 1, 1, 2, 1, 1],
    ![1, 1, 2, 2, 1, 0], ![1, 1, 1, 2, 2, 1], ![1, 1, 2, 2, 1, 1], ![1, 1, 2, 2, 2, 1],
    ![1, 1, 2, 3, 2, 1], ![1, 2, 2, 3, 2, 1]]

@[expose] def uCentRoots : Set (Fin TwistTag.E6.tag.rank → ℤ) := {α | α ∈ uCentRootList}

theorem uCentRoots_check :
    (∀ α ∈ uCentRootList, α ∈ rootFinset TwistTag.E6.tag ∧ 0 < height α) ∧
    (∀ α ∈ uCentRootList, permLattice TwistTag.E6.perm α ∈ uCentRootList) ∧
    (∀ α ∈ uCentRootList, ∀ β ∈ uCentRootList,
      α + β ∈ rootFinset TwistTag.E6.tag → α + β ∈ uCentRootList) ∧
    (∀ α ∈ uCentRootList, ∀ γ ∈ [twistedE6ClassRootU, twistedE6ClassRootU'],
      α + γ ∉ rootFinset TwistTag.E6.tag ∧ α ≠ -γ) ∧
    uCentRootList.Nodup ∧ uCentRootList.length = 30 := by
  decide +kernel

theorem ncard_uCentRoots : uCentRoots.ncard = 30 := by
  have h : uCentRoots = ↑(uCentRootList.toFinset) := by
    ext α
    simp [uCentRoots]
  rw [h, Set.ncard_coe_finset, List.toFinset_card_of_nodup uCentRoots_check.2.2.2.2.1,
    uCentRoots_check.2.2.2.2.2]


theorem uCentRoots_facts :
    (∀ α ∈ uCentRoots, IsRoot TwistTag.E6.tag α ∧ 0 < height α) ∧
    (∀ α ∈ uCentRoots, permLattice TwistTag.E6.perm α ∈ uCentRoots) ∧
    (∀ α ∈ uCentRoots, ∀ β ∈ uCentRoots, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b →
      IsRoot TwistTag.E6.tag (a • α + b • β) → a • α + b • β ∈ uCentRoots) := by
  obtain ⟨h1, h2, h3, -⟩ := uCentRoots_check
  refine ⟨fun α hα => ⟨mem_rootFinset.1 (h1 α hα).1, (h1 α hα).2⟩, fun α hα => h2 α hα,
    fun α hα β hβ a b ha hb hr => ?_⟩
  have hαr := mem_rootFinset.1 (h1 α hα).1
  have hβr := mem_rootFinset.1 (h1 β hβ).1
  have hne : α + β ≠ 0 := by
    intro h0
    have e1 := congrArg height h0
    rw [height_add] at e1
    have e2 : height (0 : Fin TwistTag.E6.tag.rank → ℤ) = 0 := by
      simp [height]
    have e3 := (h1 α hα).2
    have e4 := (h1 β hβ).2
    omega
  obtain ⟨rfl, rfl⟩ := CFSG.LieType.Steinberg.Minuscule.eq_one_of_isRoot_nsmul_add_nsmul
    CFSG.LieType.Steinberg.Minuscule.posDef_cartan_E6 hαr hβr hne ha hb hr
  rw [one_smul, one_smul] at hr ⊢
  exact h3 α hα β hβ (mem_rootFinset.2 hr)

variable {K : Type} [Field K]

theorem rootSubgroup_le_centralizer_pinnedX_classU {α γ : Fin TwistTag.E6.tag.rank → ℤ}
    (hα : α ∈ uCentRoots) (hγ : γ ∈ [twistedE6ClassRootU, twistedE6ClassRootU']) :
    rootSubgroup TwistTag.E6.tag K α ≤
      centralizer ({pinnedX TwistTag.E6.tag K γ 1} : Set (ModGL TwistTag.E6.tag K)) := by
  obtain ⟨h1, -, -, h4, -⟩ := uCentRoots_check
  have hαr := mem_rootFinset.1 (h1 α hα).1
  have hγr : IsRoot TwistTag.E6.tag γ := by
    obtain ⟨hU, hU', -⟩ := isRoot_twistedE6ClassRoots
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hγ
    rcases hγ with rfl | rfl
    exacts [hU, hU']
  obtain ⟨hnr, hneg⟩ := h4 α hα γ hγ
  intro x hx
  rw [mem_centralizer_singleton_iff]
  by_cases hαγ : α = γ
  · subst hαγ
    obtain ⟨c, rfl⟩ := mem_rootSubgroup.1 hx
    rw [← pinnedX_add, ← pinnedX_add, add_comm]
  · exact ((CFSG.LieType.Chevalley.simply_laced_root_commutator_unit TwistTag.E6.tag
      (Or.inr (Or.inl rfl)) hαr hγr hαγ hneg).2 (fun h => hnr (mem_rootFinset.2 h)) K x hx
        (pinnedX TwistTag.E6.tag K γ 1) (mem_rootSubgroup.2 ⟨1, rfl⟩)).eq

theorem rootSpan_uCentRoots_le_centralizer :
    rootSpan TwistTag.E6.tag K uCentRoots ≤
      centralizer ({twistedE6ClassU K} : Set (ModGL TwistTag.E6.tag K)) := by
  refine iSup₂_le fun α hα => ?_
  intro x hx
  rw [mem_centralizer_singleton_iff, twistedE6ClassU]
  have hU := mem_centralizer_singleton_iff.1 (rootSubgroup_le_centralizer_pinnedX_classU
    (K := K) hα (γ := twistedE6ClassRootU) (by simp) hx)
  have hU' := mem_centralizer_singleton_iff.1 (rootSubgroup_le_centralizer_pinnedX_classU
    (K := K) hα (γ := twistedE6ClassRootU') (by simp) hx)
  calc x * (pinnedX TwistTag.E6.tag K twistedE6ClassRootU 1 *
        pinnedX TwistTag.E6.tag K twistedE6ClassRootU' 1) =
      pinnedX TwistTag.E6.tag K twistedE6ClassRootU 1 * x *
        pinnedX TwistTag.E6.tag K twistedE6ClassRootU' 1 := by rw [← mul_assoc, hU]
    _ = _ := by rw [mul_assoc _ x, hU', ← mul_assoc]

theorem two_pow_dvd_card_centralizer_classU [CharP K 2] {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    2 ^ (30 * f) ∣ Nat.card (centralizer ({stdRepC (apply_apply_eq hK hσ) 1} :
      Set (graphFixedRootGroup TwistTag.E6 K σ))) := by
  have := finite_of_card hK
  have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  have hsurj : Function.Surjective σ := Finite.surjective_of_injective σ.injective
  have hq := CFSG.Timmesfeld.ExceptionalOrders.card_orbitField (t := TwistTag.E6)
    Nat.prime_two hf hK hσ
  obtain ⟨hS, hSρ, hScl⟩ := uCentRoots_facts
  have hc := CFSG.Timmesfeld.ExceptionalOrders.card_rootSpan_inf_twistedFixedGroup
    (t := TwistTag.E6) hsurj hq hS hSρ hScl
  rw [ncard_uCentRoots] at hc
  set Q : Subgroup (ModGL TwistTag.E6.tag K) :=
    rootSpan TwistTag.E6.tag K uCentRoots ⊓ twistedFixedGroup TwistTag.E6 K σ with hQ
  have hQC : Q ≤ graphFixedRootGroup TwistTag.E6 K σ := fun x hx =>
    graphFixedPosUnipotent_le_graphFixedRootGroup _ _ _
      ⟨rootSpan_le_posUnipotent hS hx.1, hx.2⟩
  have hle : Q.subgroupOf (graphFixedRootGroup TwistTag.E6 K σ) ≤
      centralizer ({stdRepC (apply_apply_eq hK hσ) 1} :
        Set (graphFixedRootGroup TwistTag.E6 K σ)) := by
    intro x hx
    rw [mem_subgroupOf] at hx
    rw [mem_centralizer_singleton_iff]
    exact Subtype.ext (mem_centralizer_singleton_iff.1 (rootSpan_uCentRoots_le_centralizer hx.1))
  have h := Subgroup.card_dvd_of_le hle
  rw [Nat.card_congr (subgroupOfEquivOfLe hQC).toEquiv, hc, ← pow_mul, mul_comm f 30] at h
  exact h

theorem two_pow_dvd_card_centralizer_of_sq_eq_one_of_one_le {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ f) {x : graphFixedRootGroup TwistTag.E6 K σ} (hx : x ^ 2 = 1)
    (hx1 : x ≠ 1) :
    2 ^ (24 * f) ∣ Nat.card (centralizer ({x} : Set (graphFixedRootGroup TwistTag.E6 K σ))) := by
  have : CharP K 2 := charP_two_of_card hf hK
  have := finite_of_card hK
  obtain ⟨σE, rfl⟩ := exists_ringEquiv_toRingHom_eq σ
  obtain ⟨g, hg⟩ := exists_conj_mem_twistedE6ClassReps_of_frameReduction hf hK
    (fun c => hσ c) (twistedE6FrameReduction hf hK (fun c => hσ c)) hx hx1
  rw [← E6Pilot.card_centralizer_conj g x]
  rcases hg with h | h | h
  · have hs : g * x * g⁻¹ = stdRepC (apply_apply_eq hK hσ) 0 := Subtype.ext h
    rw [hs]
    exact (pow_dvd_pow 2 (by omega : 24 * f ≤ 36 * f)).trans
      (two_pow_dvd_card_centralizer_stdRepC_zero hf hK hσ)
  · have hs : g * x * g⁻¹ = stdRepC (apply_apply_eq hK hσ) 1 := Subtype.ext h
    rw [hs]
    exact (pow_dvd_pow 2 (by omega : 24 * f ≤ 30 * f)).trans
      (two_pow_dvd_card_centralizer_classU hf hK hσ)
  · have hs : g * x * g⁻¹ = ⟨twistedE6ClassV K,
        twistedE6ClassV_mem_graphFixedRootGroup (apply_apply_eq hK hσ)⟩ := Subtype.ext h
    rw [hs]
    exact two_pow_dvd_card_centralizer_classV hf hK hσ

section Exclusion

variable {f : ℕ} {k : Type} [Field k] [Algebra k K]

theorem two_pow_dvd_card_fixedSubgroup_twistedE6_of_one_le (hf : 1 ≤ f)
    (hk : Nat.card k = 2 ^ f) (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ f) (θ : MulAut (graphFixedRootGroup TwistTag.E6 K σ))
    (hθ : θ * θ = 1) (hθ1 : θ ≠ 1) : 2 ^ (24 * f) ∣ Nat.card (fixedSubgroup θ) := by
  have : CharP K 2 := charP_two_of_card hf hK
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
    exact two_pow_dvd_card_centralizer_of_sq_eq_one_of_one_le hf hK hσ hx2 hx1
  · exact two_pow_dvd_card_fixedSubgroup_of_outer hf hk hK hσ θ (by rw [sq]; exact hθ) hin

theorem swapPairExclusion_twistedE6_of_one_le (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    SeitzQ2.SwapPairExclusion (graphFixedRootGroup TwistTag.E6 K σ) := by
  have : CharP K 2 := charP_two_of_card hf hK
  have := finite_of_card hK
  intro θ θ' h1 h2 h3 h4 hsum _
  have hb : ∀ θ : MulAut (graphFixedRootGroup TwistTag.E6 K σ), θ * θ = 1 → θ ≠ 1 →
      24 * f ≤ (Nat.card (fixedSubgroup θ)).factorization 2 := fun θ hθ hθ1 =>
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').1
      (two_pow_dvd_card_fixedSubgroup_twistedE6_of_one_le hf hk hK hσ θ hθ hθ1)
  have hA := factorization_two_mul_card_mulAut_twistedE6_le hf hK hσ
  have hlt : f.factorization 2 < f := Nat.factorization_lt 2 (by omega)
  have := hb θ h1 h2
  have := hb θ' h3 h4
  omega

theorem swapPairExclusion_twistedE6_two (hk : Nat.card k = 2) (hK : Nat.card K = 4)
    {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2) :
    SeitzQ2.SwapPairExclusion (graphFixedRootGroup TwistTag.E6 K σ) :=
  swapPairExclusion_twistedE6_of_one_le (f := 1) le_rfl (by rw [hk, pow_one])
    (by rw [hK]; norm_num) (fun c => by rw [pow_one]; exact hσ c)

end Exclusion

end CFSG.SeitzReduction.TwistedE6Pilot
