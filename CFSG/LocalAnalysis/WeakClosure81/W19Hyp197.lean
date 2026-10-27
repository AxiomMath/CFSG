module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenUniqueMax

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] def centralizerQuot (H E F : Subgroup G) : Subgroup G where
  carrier := {h | h ∈ H ∧ h ∈ normalizer (F : Set G) ∧ ∀ e ∈ E, ⁅h, e⁆ ∈ F}
  one_mem' := ⟨H.one_mem, Subgroup.one_mem _, fun e _ => by
    rw [commutatorElement_one_left]; exact F.one_mem⟩
  mul_mem' := fun {h₁ h₂} h₁m h₂m => by
    refine ⟨H.mul_mem h₁m.1 h₂m.1, Subgroup.mul_mem _ h₁m.2.1 h₂m.2.1, fun e he => ?_⟩
    have eq : ⁅h₁ * h₂, e⁆ = (h₁ * ⁅h₂, e⁆ * h₁⁻¹) * ⁅h₁, e⁆ := by
      simp only [commutatorElement_def]
      group
    rw [eq]
    exact F.mul_mem ((Subgroup.mem_normalizer_iff.1 h₁m.2.1 _).1 (h₂m.2.2 e he)) (h₁m.2.2 e he)
  inv_mem' := fun {h} hm => by
    refine ⟨H.inv_mem hm.1, Subgroup.inv_mem _ hm.2.1, fun e he => ?_⟩
    have eq : ⁅h⁻¹, e⁆ = h⁻¹ * ⁅h, e⁆⁻¹ * h⁻¹⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [eq]
    exact (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hm.2.1) _).1 (F.inv_mem (hm.2.2 e he))

theorem mem_centralizerQuot {H E F : Subgroup G} {h : G} :
    h ∈ centralizerQuot H E F ↔
      h ∈ H ∧ h ∈ normalizer (F : Set G) ∧ ∀ e ∈ E, ⁅h, e⁆ ∈ F :=
  Iff.rfl

theorem centralizerQuot_le (H E F : Subgroup G) : centralizerQuot H E F ≤ H := fun _ h => h.1

@[expose] def eB (E F B : Subgroup G) : Subgroup G :=
  Subgroup.closure {e | e ∈ E ∧ ∀ b ∈ B, ⁅e, b⁆ ∈ F}

@[expose] def commEB (E F B : Subgroup G) : Subgroup G := ⁅eB E F B, B⁆

theorem eB_le (E F B : Subgroup G) : eB E F B ≤ E :=
  (Subgroup.closure_le E).2 fun _ h => h.1

theorem mem_eB_of {E F B : Subgroup G} {e : G} (he : e ∈ E) (h : ∀ b ∈ B, ⁅e, b⁆ ∈ F) :
    e ∈ eB E F B :=
  Subgroup.subset_closure ⟨he, h⟩

theorem mem_eB_iff {E F B : Subgroup G} (hFE : F ≤ E) (hE : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    {e : G} : e ∈ eB E F B ↔ e ∈ E ∧ ∀ b ∈ B, ⁅e, b⁆ ∈ F := by
  refine ⟨fun h => ?_, fun h => mem_eB_of h.1 h.2⟩
  let S : Subgroup G :=
    { carrier := {e | e ∈ E ∧ ∀ b ∈ B, ⁅e, b⁆ ∈ F}
      one_mem' := ⟨E.one_mem, fun b _ => by rw [commutatorElement_one_left]; exact F.one_mem⟩
      mul_mem' := fun {x y} hx hy => by
        refine ⟨E.mul_mem hx.1 hy.1, fun b hb => ?_⟩
        have eq : ⁅x * y, b⁆ = x * ⁅y, b⁆ * x⁻¹ * ⁅x, b⁆ := by
          simp only [commutatorElement_def]
          group
        have h1 : x * ⁅y, b⁆ * x⁻¹ = ⁅y, b⁆ := by
          have hc : x * ⁅y, b⁆ = ⁅y, b⁆ * x := hE x hx.1 _ (hFE (hy.2 b hb))
          rw [hc]
          group
        rw [eq, h1]
        exact F.mul_mem (hy.2 b hb) (hx.2 b hb)
      inv_mem' := fun {x} hx => by
        refine ⟨E.inv_mem hx.1, fun b hb => ?_⟩
        have eq : ⁅x⁻¹, b⁆ = x⁻¹ * ⁅x, b⁆⁻¹ * x := by
          simp only [commutatorElement_def]
          group
        have h1 : x⁻¹ * ⁅x, b⁆⁻¹ * x = ⁅x, b⁆⁻¹ := by
          have hc : x⁻¹ * ⁅x, b⁆⁻¹ = ⁅x, b⁆⁻¹ * x⁻¹ :=
            hE x⁻¹ (E.inv_mem hx.1) _ (E.inv_mem (hFE (hx.2 b hb)))
          rw [hc]
          group
        rw [eq, h1]
        exact F.inv_mem (hx.2 b hb) }
  exact (Subgroup.closure_le S).2 (fun _ h => h) h

theorem eB_eq_of_forall {E F B : Subgroup G} (h : ∀ e ∈ E, ∀ b ∈ B, ⁅e, b⁆ ∈ F) :
    eB E F B = E :=
  le_antisymm (eB_le E F B) fun _ he => mem_eB_of he (h _ he)

structure Hyp197 (D : Data G) (V X E F : Subgroup G) (g : G) : Prop where
  E_le : E ≤ X ⊔ D.T
  isElemAbelian : IsElemAbelian 2 E
  F_le : F ≤ E
  normalizer_E : X ⊔ D.T ≤ normalizer (E : Set G)
  normalizer_F : X ⊔ D.T ≤ normalizer (F : Set G)
  irreducible : ∀ U : Subgroup G, F ≤ U → U ≤ E → X ⊔ D.T ≤ normalizer (U : Set G) →
    U = F ∨ U = E
  comm_F : ⁅F, twoResidual (X ⊔ D.T)⁆ = ⊥
  le_T : conjSubgroup V g ≤ D.T
  comm_ne : ¬ ⁅twoResidual (X ⊔ D.T), conjSubgroup V g⁆ ≤ centralizerQuot (X ⊔ D.T) E F

end CFSG.LocalAnalysis.WeakClosure81

end
