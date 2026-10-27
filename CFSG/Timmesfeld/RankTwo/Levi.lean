module

public import CFSG.Timmesfeld.RankTwo.LeviSteinberg
public import CFSG.Timmesfeld.RankTwo.Presentation

public section

namespace CFSG.Timmesfeld

open CFSG.LieType CFSG.LieType.Universal

variable {K : Type*} [Group K]

@[expose] def pairRoots (D : UniversalRootDatum K) (i j : Fin D.rank) : Set (Fin D.rank → ℤ) :=
  {γ | γ ∈ D.roots ∧ ∀ k, k ≠ i → k ≠ j → γ k = 0}

@[expose] def LeviConePresented (D : UniversalRootDatum K) : Prop :=
  ∀ (i j : Fin D.rank) (H : Type) [Group H] (ψ : ∀ γ, D.rootGroup γ → H),
    (∀ α ∈ pairRoots D i j, ∀ β ∈ pairRoots D i j, ¬ Universal.IsNegMultiple α β →
      ExtendsToHom D.rootGroup (D.cone α β ∩ pairRoots D i j) ψ) →
    (∀ k, (k = i ∨ k = j) → ExtendsToHom D.rootGroup {Pi.single k 1, -Pi.single k 1} ψ) →
    CurtisTits.RelationsHold D.rootGroup (pairRoots D i j) ψ

variable {D : UniversalRootDatum K}

theorem mem_pairRoots_iff {i j : Fin D.rank} {γ : Fin D.rank → ℤ} :
    γ ∈ pairRoots D i j ↔ γ ∈ D.roots ∧ ∀ k ∉ ({i, j} : Finset (Fin D.rank)), γ k = 0 := by
  change (_ ∧ _) ↔ (_ ∧ _)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
  exact and_congr_right fun _ => ⟨fun h k hk => h k hk.1 hk.2, fun h k hi hj => h k ⟨hi, hj⟩⟩

theorem cone_subset_pairRoots {i j : Fin D.rank} {α β : Fin D.rank → ℤ}
    (hα : α ∈ pairRoots D i j) (hβ : β ∈ pairRoots D i j) : D.cone α β ⊆ pairRoots D i j := by
  rintro γ ⟨hγ, a, b, rfl⟩
  refine ⟨hγ, fun k hi hj => ?_⟩
  simp [hα.2 k hi hj, hβ.2 k hi hj]

variable {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K}

theorem leviConePresented_of
    (hct : CurtisTits.IsCTGroupDatum (RootSystem.coxeterMatrix D.isFiniteType).toCoxeterSystem
      (RootSystem.weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hext : Steinberg.SteinbergExtras D n H) : LeviConePresented D := by
  intro i j G _ ψ hcone hrank
  refine Levi.relationsHold_mono (Levi.relationsHold_supported hct hext {i, j} ψ
    (fun α hα hαs β hβ hβs hneg => ?_) (fun k hk => ?_)) fun γ hγ => mem_pairRoots_iff.mp hγ
  · have hα' : α ∈ pairRoots D i j := mem_pairRoots_iff.mpr ⟨hα, hαs⟩
    have hβ' : β ∈ pairRoots D i j := mem_pairRoots_iff.mpr ⟨hβ, hβs⟩
    exact Levi.relationsHold_mono (hcone α hα' β hβ' hneg).relationsHold
      fun γ hγ => ⟨hγ, cone_subset_pairRoots hα' hβ' hγ⟩
  · exact (hrank k (by simpa using hk)).relationsHold

end CFSG.Timmesfeld
