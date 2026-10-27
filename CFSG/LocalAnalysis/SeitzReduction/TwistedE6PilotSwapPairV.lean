module

public import CFSG.Timmesfeld.Orders.ExceptionalTwistedUnipotent
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneTwistedE6ClassesReps
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotModel

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.TwistedE6Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

@[expose] def vCentRootList : List (Fin TwistTag.E6.tag.rank → ℤ) :=
  [![0, 0, 0, 1, 1, 0], ![0, 0, 0, 1, 1, 1], ![0, 0, 1, 1, 0, 0], ![0, 0, 1, 1, 1, 0],
    ![0, 1, 0, 0, 0, 0], ![0, 1, 0, 1, 1, 0], ![0, 1, 0, 1, 1, 1], ![0, 1, 1, 1, 0, 0],
    ![0, 1, 1, 1, 1, 0], ![0, 1, 1, 2, 1, 0], ![0, 1, 1, 2, 1, 1], ![0, 1, 1, 2, 2, 1],
    ![1, 0, 1, 1, 0, 0], ![1, 0, 1, 1, 1, 1], ![1, 1, 1, 1, 0, 0], ![1, 1, 1, 1, 1, 1],
    ![1, 1, 1, 2, 1, 0], ![1, 1, 1, 2, 1, 1], ![1, 1, 1, 2, 2, 1], ![1, 1, 2, 2, 1, 0],
    ![1, 1, 2, 2, 1, 1], ![1, 1, 2, 2, 2, 1], ![1, 1, 2, 3, 2, 1], ![1, 2, 2, 3, 2, 1]]

@[expose] def vCentRoots : Set (Fin TwistTag.E6.tag.rank → ℤ) := {α | α ∈ vCentRootList}

theorem vCentRoots_check :
    (∀ α ∈ vCentRootList, α ∈ rootFinset TwistTag.E6.tag ∧ 0 < height α) ∧
    (∀ α ∈ vCentRootList, permLattice TwistTag.E6.perm α ∈ vCentRootList) ∧
    (∀ α ∈ vCentRootList, ∀ β ∈ vCentRootList,
      α + β ∈ rootFinset TwistTag.E6.tag → α + β ∈ vCentRootList) ∧
    (∀ α ∈ vCentRootList, ∀ γ ∈ [twistedE6ClassRootA, twistedE6ClassRootA', twistedE6ClassRootB],
      α + γ ∉ rootFinset TwistTag.E6.tag ∧ α ≠ -γ) ∧
    vCentRootList.Nodup ∧ vCentRootList.length = 24 := by
  decide +kernel

theorem ncard_vCentRoots : vCentRoots.ncard = 24 := by
  have h : vCentRoots = ↑(vCentRootList.toFinset) := by
    ext α
    simp [vCentRoots]
  rw [h, Set.ncard_coe_finset, List.toFinset_card_of_nodup vCentRoots_check.2.2.2.2.1,
    vCentRoots_check.2.2.2.2.2]


theorem vCentRoots_facts :
    (∀ α ∈ vCentRoots, IsRoot TwistTag.E6.tag α ∧ 0 < height α) ∧
    (∀ α ∈ vCentRoots, permLattice TwistTag.E6.perm α ∈ vCentRoots) ∧
    (∀ α ∈ vCentRoots, ∀ β ∈ vCentRoots, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b →
      IsRoot TwistTag.E6.tag (a • α + b • β) → a • α + b • β ∈ vCentRoots) := by
  obtain ⟨h1, h2, h3, -⟩ := vCentRoots_check
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

theorem rootSubgroup_le_centralizer_pinnedX_classV {α γ : Fin TwistTag.E6.tag.rank → ℤ}
    (hα : α ∈ vCentRoots)
    (hγ : γ ∈ [twistedE6ClassRootA, twistedE6ClassRootA', twistedE6ClassRootB]) :
    rootSubgroup TwistTag.E6.tag K α ≤
      centralizer ({pinnedX TwistTag.E6.tag K γ 1} : Set (ModGL TwistTag.E6.tag K)) := by
  obtain ⟨h1, -, -, h4, -⟩ := vCentRoots_check
  have hαr := mem_rootFinset.1 (h1 α hα).1
  have hγr : IsRoot TwistTag.E6.tag γ := by
    obtain ⟨-, -, hA, hA', hB⟩ := isRoot_twistedE6ClassRoots
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hγ
    rcases hγ with rfl | rfl | rfl
    exacts [hA, hA', hB]
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

theorem rootSpan_vCentRoots_le_centralizer :
    rootSpan TwistTag.E6.tag K vCentRoots ≤
      centralizer ({twistedE6ClassV K} : Set (ModGL TwistTag.E6.tag K)) := by
  refine iSup₂_le fun α hα => ?_
  intro x hx
  rw [mem_centralizer_singleton_iff, twistedE6ClassV]
  have hA := mem_centralizer_singleton_iff.1 (rootSubgroup_le_centralizer_pinnedX_classV
    (K := K) hα (γ := twistedE6ClassRootA) (by simp) hx)
  have hA' := mem_centralizer_singleton_iff.1 (rootSubgroup_le_centralizer_pinnedX_classV
    (K := K) hα (γ := twistedE6ClassRootA') (by simp) hx)
  have hB := mem_centralizer_singleton_iff.1 (rootSubgroup_le_centralizer_pinnedX_classV
    (K := K) hα (γ := twistedE6ClassRootB) (by simp) hx)
  calc x * (pinnedX TwistTag.E6.tag K twistedE6ClassRootA 1 *
        pinnedX TwistTag.E6.tag K twistedE6ClassRootA' 1 *
        pinnedX TwistTag.E6.tag K twistedE6ClassRootB 1) =
      pinnedX TwistTag.E6.tag K twistedE6ClassRootA 1 * x *
        pinnedX TwistTag.E6.tag K twistedE6ClassRootA' 1 *
        pinnedX TwistTag.E6.tag K twistedE6ClassRootB 1 := by rw [← mul_assoc, ← mul_assoc, hA]
    _ = pinnedX TwistTag.E6.tag K twistedE6ClassRootA 1 *
        pinnedX TwistTag.E6.tag K twistedE6ClassRootA' 1 * x *
        pinnedX TwistTag.E6.tag K twistedE6ClassRootB 1 := by rw [mul_assoc _ x, hA', ← mul_assoc]
    _ = _ := by rw [mul_assoc _ x, hB, ← mul_assoc]

theorem two_pow_dvd_card_centralizer_classV [CharP K 2] {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    2 ^ (24 * f) ∣ Nat.card (centralizer ({⟨twistedE6ClassV K,
      twistedE6ClassV_mem_graphFixedRootGroup (apply_apply_eq hK hσ)⟩} :
        Set (graphFixedRootGroup TwistTag.E6 K σ))) := by
  have := finite_of_card hK
  have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  have hsurj : Function.Surjective σ := Finite.surjective_of_injective σ.injective
  have hq := CFSG.Timmesfeld.ExceptionalOrders.card_orbitField (t := TwistTag.E6)
    Nat.prime_two hf hK hσ
  obtain ⟨hS, hSρ, hScl⟩ := vCentRoots_facts
  have hc := CFSG.Timmesfeld.ExceptionalOrders.card_rootSpan_inf_twistedFixedGroup
    (t := TwistTag.E6) hsurj hq hS hSρ hScl
  rw [ncard_vCentRoots] at hc
  set Q : Subgroup (ModGL TwistTag.E6.tag K) :=
    rootSpan TwistTag.E6.tag K vCentRoots ⊓ twistedFixedGroup TwistTag.E6 K σ with hQ
  have hQC : Q ≤ graphFixedRootGroup TwistTag.E6 K σ := fun x hx =>
    graphFixedPosUnipotent_le_graphFixedRootGroup _ _ _
      ⟨rootSpan_le_posUnipotent hS hx.1, hx.2⟩
  have hle : Q.subgroupOf (graphFixedRootGroup TwistTag.E6 K σ) ≤
      centralizer ({⟨twistedE6ClassV K,
        twistedE6ClassV_mem_graphFixedRootGroup (apply_apply_eq hK hσ)⟩} :
          Set (graphFixedRootGroup TwistTag.E6 K σ)) := by
    intro x hx
    rw [mem_subgroupOf] at hx
    rw [mem_centralizer_singleton_iff]
    exact Subtype.ext (mem_centralizer_singleton_iff.1 (rootSpan_vCentRoots_le_centralizer hx.1))
  have h := Subgroup.card_dvd_of_le hle
  rw [Nat.card_congr (subgroupOfEquivOfLe hQC).toEquiv, hc, ← pow_mul, mul_comm f 24] at h
  exact h

end CFSG.SeitzReduction.TwistedE6Pilot
