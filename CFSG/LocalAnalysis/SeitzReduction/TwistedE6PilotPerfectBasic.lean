module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneTwistedE6ClassesBasic
public import CFSG.Quasithin.Background.A3ComponentsBasic

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.TwistedE6Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley RootOps
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.Quasithin (perfectCore perfectCore_le perfectCore_mono map_perfectCore
  le_perfectCore_of_perfect perfectCore_eq_self_of_perfect)
open scoped commutatorElement

section General

variable {G : Type*} [Group G]

theorem mul_conj_inv_mem_perfectCore {X : Subgroup G} {d v : G} (hd : d ∈ perfectCore X)
    (hv : v ∈ X) : d * v * d⁻¹ * v⁻¹ ∈ perfectCore X := by
  have hN : v ∈ normalizer (perfectCore X : Set G) :=
    CFSG.Quasithin.normalizer_le_normalizer_perfectCore X (le_normalizer hv)
  have h1 : v * d⁻¹ * v⁻¹ ∈ perfectCore X := (mem_normalizer_iff.1 hN _).1 (inv_mem hd)
  have e : d * v * d⁻¹ * v⁻¹ = d * (v * d⁻¹ * v⁻¹) := by group
  rw [e]
  exact mul_mem hd h1

theorem mul_conj_inv_mem_map_perfectCore {C : Subgroup G} {X : Subgroup C} {d v : G}
    (hdC : d ∈ C) (hvC : v ∈ C) (hd : (⟨d, hdC⟩ : C) ∈ perfectCore X) (hv : (⟨v, hvC⟩ : C) ∈ X) :
    d * v * d⁻¹ * v⁻¹ ∈ (perfectCore X).map C.subtype :=
  ⟨_, mul_conj_inv_mem_perfectCore hd hv, rfl⟩

end General


section Product

variable {t : TwistTag} {K : Type} [Field K]

theorem rootSpan_inf_twistedFixedGroup_le_of_forall {σ : K →+* K} (hσ : Function.Surjective σ)
    {S : Set (Fin t.tag.rank → ℤ)} (hS : ∀ α ∈ S, IsRoot t.tag α ∧ 0 < height α)
    (hSρ : ∀ α ∈ S, permLattice t.perm α ∈ S)
    (hclosed : ∀ α ∈ S, ∀ β ∈ S, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → IsRoot t.tag (a • α + b • β) →
      a • α + b • β ∈ S)
    {P : Subgroup (ModGL t.tag K)}
    (hP : ∀ α ∈ S, rootSpan t.tag K (t.diagramOrbit α : Set (Fin t.tag.rank → ℤ)) ⊓
      twistedFixedGroup t K σ ≤ P) :
    rootSpan t.tag K S ⊓ twistedFixedGroup t K σ ≤ P := by
  have hfin : {O' | O' ∈ t.diagramRootOrbits ∧ (O' : Set (Fin t.tag.rank → ℤ)) ⊆ S}.Finite :=
    ((finite_setOf_isRoot t.tag).image t.diagramOrbit).subset fun O' ⟨⟨α, hα, hαO⟩, _⟩ =>
      ⟨α, hα, hαO⟩
  obtain ⟨k, O, hO⟩ := hfin.fin_embedding
  have hbij := bijOn_prod_graphFixed (K := K) hσ hS hSρ hclosed O O.injective hO
  intro g hg
  obtain ⟨w, -, hw⟩ := hbij.surjOn hg
  rw [← hw]
  refine Subgroup.list_prod_mem _ fun x hx => ?_
  obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hx
  have hOj : O j ∈ {O' | O' ∈ t.diagramRootOrbits ∧ (O' : Set (Fin t.tag.rank → ℤ)) ⊆ S} := by
    rw [← hO]
    exact Set.mem_range_self j
  obtain ⟨⟨α, -, hαO⟩, hsub⟩ := hOj
  have hαS : α ∈ S := hsub (by rw [← hαO]; exact t.self_mem_diagramOrbit α)
  refine hP α hαS ?_
  rw [hαO]
  exact (w j).2

end Product

section Torus

variable {K : Type} [Field K]

theorem exists_eq_rootDiagUnit_conj_of_mem_orbitGroup [Finite K] (σ : K →+* K)
    {α : Fin TwistTag.E6.tag.rank → ℤ} (hα : IsRoot TwistTag.E6.tag α) (hαp : 0 < height α)
    {b : Fin TwistTag.E6.tag.rank → Kˣ}
    (hbΓ : rootDiagUnit TwistTag.E6.tag b ∈ twistedFixedGroup TwistTag.E6 K σ)
    (hb : ∀ β ∈ TwistTag.E6.diagramOrbit α, rootChar b β ≠ 1) {x : ModGL TwistTag.E6.tag K}
    (hx : x ∈ rootSpan TwistTag.E6.tag K (TwistTag.E6.diagramOrbit α : Set _) ⊓
      twistedFixedGroup TwistTag.E6 K σ) :
    ∃ v ∈ rootSpan TwistTag.E6.tag K (TwistTag.E6.diagramOrbit α : Set _) ⊓
        twistedFixedGroup TwistTag.E6 K σ,
      x = rootDiagUnit TwistTag.E6.tag b * v * (rootDiagUnit TwistTag.E6.tag b)⁻¹ * v⁻¹ := by
  have hOroot : ∀ β ∈ TwistTag.E6.diagramOrbit α, IsRoot TwistTag.E6.tag β ∧ 0 < height β := by
    intro β hβ
    rw [diagramOrbit_eq_pair_twistedE6Classes, Finset.mem_insert, Finset.mem_singleton] at hβ
    rcases hβ with rfl | rfl
    · exact ⟨hα, hαp⟩
    · exact ⟨hα.permLattice TwistTag.E6.cartan_perm, by rw [height_permLattice]; exact hαp⟩
  have hOcl : ∀ β ∈ (TwistTag.E6.diagramOrbit α : Set (Fin TwistTag.E6.tag.rank → ℤ)),
      ∀ γ ∈ (TwistTag.E6.diagramOrbit α : Set (Fin TwistTag.E6.tag.rank → ℤ)), ∀ a c : ℕ,
        1 ≤ a → 1 ≤ c → IsRoot TwistTag.E6.tag (a • β + c • γ) →
          a • β + c • γ ∈ (TwistTag.E6.diagramOrbit α : Set (Fin TwistTag.E6.tag.rank → ℤ)) :=
    fun β hβ γ hγ a c ha hc hr =>
      absurd hr (TwistTag.E6.not_isRoot_nsmul_add_nsmul_of_mem_diagramOrbit hα hβ hγ ha hc)
  set A := rootSpan TwistTag.E6.tag K (TwistTag.E6.diagramOrbit α : Set _) ⊓
    twistedFixedGroup TwistTag.E6 K σ with hA
  have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  have hnorm : ∀ v ∈ A, rootDiagUnit TwistTag.E6.tag b * v * (rootDiagUnit TwistTag.E6.tag b)⁻¹ ∈
      A := by
    intro v hv
    obtain ⟨hvO, hvΓ⟩ := Subgroup.mem_inf.1 hv
    refine Subgroup.mem_inf.2 ⟨?_, mul_mem (mul_mem hbΓ hvΓ) (inv_mem hbΓ)⟩
    have hmap := map_rootSpan_of_forall
      (f := (MulAut.conj (rootDiagUnit TwistTag.E6.tag b)).toMonoidHom)
      (S := (TwistTag.E6.diagramOrbit α : Set (Fin TwistTag.E6.tag.rank → ℤ)))
      fun β hβ => map_conj_rootDiagUnit_rootSubgroup b (hOroot β hβ).1
    rw [← hmap]
    exact ⟨v, hvO, rfl⟩
  have hfree : ∀ v ∈ A, rootDiagUnit TwistTag.E6.tag b * v * (rootDiagUnit TwistTag.E6.tag b)⁻¹ =
      v → v = 1 := by
    intro v hv hfix
    have h1 := mem_rootSpan_of_rootDiagUnit_conj_eq (B := {b}) hOroot hOcl
      (Subgroup.mem_inf.1 hv).1 fun b' hb' => by
        rw [Set.mem_singleton_iff.1 hb']
        exact hfix
    have hempty : {β | β ∈ (TwistTag.E6.diagramOrbit α : Set (Fin TwistTag.E6.tag.rank → ℤ)) ∧
        ∀ b' ∈ ({b} : Set (Fin TwistTag.E6.tag.rank → Kˣ)), rootChar b' β = 1} = ∅ :=
      Set.eq_empty_iff_forall_notMem.2 fun β hβ => hb β hβ.1 (hβ.2 b rfl)
    rw [hempty] at h1
    have hbot : rootSpan TwistTag.E6.tag K (∅ : Set (Fin TwistTag.E6.tag.rank → ℤ)) = ⊥ :=
      iSup₂_eq_bot.2 fun β hβ => absurd hβ (Set.notMem_empty β)
    rw [hbot] at h1
    exact Subgroup.mem_bot.1 h1
  exact exists_eq_mul_conj_inv_of_fixedPointFree hnorm hfree hx

theorem rootChar_cartanRow {τ : Tag} (i : Fin τ.rank) (u : Kˣ) (γ : Fin τ.rank → ℤ) :
    rootChar (fun j => u ^ τ.cartan i j) γ = u ^ coPair τ i γ := by
  simp only [rootChar, coPair, ← zpow_mul]
  exact prod_zpow_eq_zpow_sum Finset.univ _ u

theorem zpow_ne_one_of_abs_le_two_of_charTwo [CharP K 2] {u : Kˣ} (hu : u ≠ 1) {m : ℤ}
    (hm0 : m ≠ 0) (hm : |m| ≤ 2) : u ^ m ≠ 1 := by
  have h2 : u ^ (2 : ℤ) ≠ 1 := by
    intro h
    apply hu
    have h' : ((u : K)) ^ 2 = 1 := by
      have := congrArg Units.val h
      simpa using this
    have h3 : ((u : K) - 1) ^ 2 = 0 := by
      linear_combination h' + (1 - (u : K)) * (CharP.cast_eq_zero K 2)
    exact Units.ext (by simpa [sub_eq_zero] using h3)
  have h1 : u ^ (1 : ℤ) ≠ 1 := by rwa [zpow_one]
  rw [abs_le] at hm
  have : m = 1 ∨ m = -1 ∨ m = 2 ∨ m = -2 := by omega
  rcases this with rfl | rfl | rfl | rfl
  · exact h1
  · rw [zpow_neg, ne_eq, inv_eq_one]; exact h1
  · exact h2
  · rw [zpow_neg, ne_eq, inv_eq_one]; exact h2

theorem exists_units_ne_one_of_four_le {k : Type} [Field k] [Finite k]
    (hk : 4 ≤ Nat.card k) : ∃ a : kˣ, a ≠ 1 := by
  by_contra h
  push Not at h
  have hsurj : Function.Surjective (fun b : Bool => if b then (1 : k) else 0) := by
    intro x
    by_cases hx : x = 0
    · exact ⟨false, by simp [hx]⟩
    · refine ⟨true, ?_⟩
      have := h (Units.mk0 x hx)
      simpa using (congrArg Units.val this).symm
  have h1 := Nat.card_le_card_of_surjective _ hsurj
  have h2 : Nat.card Bool = 2 := by simp
  omega

theorem twistedE6PairX_permLattice {σ : K →+* K} (hσσ : ∀ x, σ (σ x) = x)
    {α : Fin TwistTag.E6.tag.rank → ℤ} (hα : IsRoot TwistTag.E6.tag α) (s : K) :
    twistedE6PairX σ (permLattice TwistTag.E6.perm α) s = twistedE6PairX σ α (σ s) := by
  unfold twistedE6PairX
  rw [permLattice_twistedE6_perm_perm, hσσ]
  exact (commute_pinnedX_permLattice_twistedE6 hα (σ s) s).eq.symm

theorem orbitGroup_le_rootSpan_inf_C0 {σ : K →+* K} {S : Set (Fin TwistTag.E6.tag.rank → ℤ)}
    (hS : ∀ α ∈ S, IsRoot TwistTag.E6.tag α ∧ 0 < height α)
    (hSρ : ∀ α ∈ S, permLattice TwistTag.E6.perm α ∈ S) {α : Fin TwistTag.E6.tag.rank → ℤ}
    (hα : α ∈ S) :
    rootSpan TwistTag.E6.tag K (TwistTag.E6.diagramOrbit α : Set _) ⊓
        twistedFixedGroup TwistTag.E6 K σ ≤
      rootSpan TwistTag.E6.tag K S ⊓ graphFixedRootGroup TwistTag.E6 K σ := by
  have hOS : (TwistTag.E6.diagramOrbit α : Set (Fin TwistTag.E6.tag.rank → ℤ)) ⊆ S := by
    intro β hβ
    rw [Finset.mem_coe, diagramOrbit_eq_pair_twistedE6Classes, Finset.mem_insert,
      Finset.mem_singleton] at hβ
    rcases hβ with rfl | rfl
    · exact hα
    · exact hSρ _ hα
  intro x hx
  obtain ⟨hxO, hxΓ⟩ := Subgroup.mem_inf.1 hx
  refine Subgroup.mem_inf.2 ⟨rootSpan_mono hOS hxO, graphFixedPosUnipotent_le_graphFixedRootGroup
    _ _ _ (Subgroup.mem_inf.2 ⟨rootSpan_mono (T := {β | IsRoot TwistTag.E6.tag β ∧ 0 < height β})
      (fun β hβ => hS β (hOS hβ)) hxO, hxΓ⟩)⟩

end Torus

end CFSG.SeitzReduction.TwistedE6Pilot
