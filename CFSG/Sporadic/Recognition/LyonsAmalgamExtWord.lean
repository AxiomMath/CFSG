module

public import Mathlib.GroupTheory.FreeGroup.Basic
public import Mathlib.Data.Fin.VecNotation

public section

namespace CFSG.Sporadic.Recognition.LyonsSims

variable {ι : Type*} {X X₀ : Type*} [Group X] [Group X₀]

theorem map_lift_eq_lift_comp (φ : X →* X₀) (g : ι → X) (r : FreeGroup ι) :
    φ (FreeGroup.lift g r) = FreeGroup.lift (φ ∘ g) r := by
  have h : φ.comp (FreeGroup.lift g) = FreeGroup.lift (φ ∘ g) :=
    FreeGroup.ext_hom _ _ fun i => by simp
  exact congrArg (fun f : FreeGroup ι →* X₀ => f r) h

theorem lift_lift_eq_lift_comp {κ : Type*} (g : ι → X) (w : κ → FreeGroup ι) (r : FreeGroup κ) :
    FreeGroup.lift g (FreeGroup.lift w r) = FreeGroup.lift (fun j => FreeGroup.lift g (w j)) r :=
  map_lift_eq_lift_comp (FreeGroup.lift g) w r

theorem lift_eq_one_iff_lift_comp_eq_one_of_injective {φ : X →* X₀} (hφ : Function.Injective φ)
    (g : ι → X) (r : FreeGroup ι) :
    FreeGroup.lift g r = 1 ↔ FreeGroup.lift (φ ∘ g) r = 1 := by
  rw [← map_lift_eq_lift_comp, ← map_one φ, hφ.eq_iff]

theorem lift_eq_one_iff_lift_comp_eq_one (φ : X ≃* X₀) (g : ι → X) (r : FreeGroup ι) :
    FreeGroup.lift g r = 1 ↔ FreeGroup.lift (φ ∘ g) r = 1 :=
  lift_eq_one_iff_lift_comp_eq_one_of_injective (φ := φ.toMonoidHom) φ.injective g r

theorem lift_eq_one_iff_of_mulEquiv_apply (φ : X ≃* X₀) (g : ι → X) (g₀ : ι → X₀)
    (hg : ∀ i, φ (g i) = g₀ i) (r : FreeGroup ι) :
    FreeGroup.lift g r = 1 ↔ FreeGroup.lift g₀ r = 1 := by
  have h : ⇑φ ∘ g = g₀ := funext hg
  rw [lift_eq_one_iff_lift_comp_eq_one φ g r, h]

theorem lift_eq_one_of_lift_comp_eq_one (φ : X ≃* X₀) (g : ι → X) {r : FreeGroup ι}
    (h : FreeGroup.lift (φ ∘ g) r = 1) : FreeGroup.lift g r = 1 :=
  (lift_eq_one_iff_lift_comp_eq_one φ g r).mpr h

theorem forall_lift_eq_one_of_forall_lift_comp_eq_one (φ : X ≃* X₀) (g : ι → X)
    {R : Set (FreeGroup ι)} (h : ∀ r ∈ R, FreeGroup.lift (φ ∘ g) r = 1) :
    ∀ r ∈ R, FreeGroup.lift g r = 1 :=
  fun r hr => lift_eq_one_of_lift_comp_eq_one φ g (h r hr)

theorem lift_cdk_eq_one_iff (φ : X ≃* X₀) (c d k : X) (r : FreeGroup (Fin 3)) :
    FreeGroup.lift ![c, d, k] r = 1 ↔ FreeGroup.lift ![φ c, φ d, φ k] r = 1 := by
  have h : φ ∘ ![c, d, k] = ![φ c, φ d, φ k] := by
    funext i
    match i with
    | 0 => rfl
    | 1 => rfl
    | 2 => rfl
  rw [lift_eq_one_iff_lift_comp_eq_one φ, h]

section Subgroup

variable (H : Subgroup X)

theorem coe_lift_subgroup (g : ι → H) (r : FreeGroup ι) :
    ((FreeGroup.lift g r : H) : X) = FreeGroup.lift (fun i => (g i : X)) r := by
  have h : H.subtype.comp (FreeGroup.lift g) = FreeGroup.lift (fun i => (g i : X)) :=
    FreeGroup.ext_hom _ _ fun i => by simp
  exact congrArg (fun f : FreeGroup ι →* X => f r) h

theorem lift_subgroup_eq_one_iff (g : ι → H) (r : FreeGroup ι) :
    FreeGroup.lift g r = 1 ↔ FreeGroup.lift (fun i => (g i : X)) r = 1 := by
  rw [← coe_lift_subgroup, ← H.coe_one, Subtype.coe_inj]

theorem lift_eq_one_iff_of_mem (g : ι → X) (hg : ∀ i, g i ∈ H) (r : FreeGroup ι) :
    FreeGroup.lift g r = 1 ↔ FreeGroup.lift (fun i => (⟨g i, hg i⟩ : H)) r = 1 :=
  (lift_subgroup_eq_one_iff H (fun i => ⟨g i, hg i⟩) r).symm

variable {H} {Y : Type*} [Group Y]

theorem lift_eq_one_iff_of_mem_equiv (φ : H ≃* Y) (g : ι → X) (hg : ∀ i, g i ∈ H)
    (r : FreeGroup ι) :
    FreeGroup.lift g r = 1 ↔ FreeGroup.lift (fun i => φ ⟨g i, hg i⟩) r = 1 := by
  rw [lift_eq_one_iff_of_mem H g hg, lift_eq_one_iff_lift_comp_eq_one φ]
  rfl

theorem lift_eq_one_iff_of_mem_equiv_apply (φ : H ≃* Y) (g : ι → X) (hg : ∀ i, g i ∈ H)
    (g₀ : ι → Y) (hg₀ : ∀ i, φ ⟨g i, hg i⟩ = g₀ i) (r : FreeGroup ι) :
    FreeGroup.lift g r = 1 ↔ FreeGroup.lift g₀ r = 1 := by
  have h : (fun i => φ ⟨g i, hg i⟩) = g₀ := funext hg₀
  rw [lift_eq_one_iff_of_mem_equiv φ g hg r, h]

theorem lift_eq_one_of_mem_equiv (φ : H ≃* Y) (g : ι → X) (hg : ∀ i, g i ∈ H)
    {r : FreeGroup ι} (h : FreeGroup.lift (fun i => φ ⟨g i, hg i⟩) r = 1) :
    FreeGroup.lift g r = 1 :=
  (lift_eq_one_iff_of_mem_equiv φ g hg r).mpr h

end Subgroup

end CFSG.Sporadic.Recognition.LyonsSims
