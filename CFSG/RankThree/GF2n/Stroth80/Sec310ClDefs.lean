module

public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import Mathlib.LinearAlgebra.BilinearForm.Properties

public section

namespace CFSG.RankThree.GF2n.Stroth80.Classify

section Abstract

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]

@[expose] def IsIsom (F : LinearMap.BilinForm K V) (g : V ≃ₗ[K] V) : Prop :=
  ∀ x y, F (g x) (g y) = F x y

@[expose] def pointRadSubgroup (F : LinearMap.BilinForm K V) (e : V) :
    Subgroup (V ≃ₗ[K] V) where
  carrier := {g | IsIsom F g ∧ g e = e ∧ ∀ v, F v e = 0 → ∃ c : K, g v = v + c • e}
  mul_mem' := by
    rintro a b ⟨ha1, ha2, ha3⟩ ⟨hb1, hb2, hb3⟩
    refine ⟨fun x y => by simp only [LinearEquiv.mul_apply]; rw [ha1, hb1], ?_, ?_⟩
    · simp only [LinearEquiv.mul_apply]; rw [hb2, ha2]
    · intro v hv
      obtain ⟨c, hc⟩ := hb3 v hv
      obtain ⟨d, hd⟩ := ha3 v hv
      refine ⟨c + d, ?_⟩
      simp only [LinearEquiv.mul_apply]
      rw [hc, map_add, map_smul, ha2, hd, add_smul]
      abel
  one_mem' := ⟨fun x y => rfl, rfl, fun v _ => ⟨0, by simp⟩⟩
  inv_mem' := by
    rintro a ⟨ha1, ha2, ha3⟩
    refine ⟨fun x y => ?_, ?_, ?_⟩
    · have := ha1 (a⁻¹ x) (a⁻¹ y)
      simpa using this.symm
    · exact (LinearEquiv.symm_apply_eq a).mpr ha2.symm
    · intro v hv
      have hu : a (a⁻¹ v) = v := by simp
      have hFu : F (a⁻¹ v) e = 0 := by
        have := ha1 (a⁻¹ v) e
        rw [hu, ha2] at this
        rw [← this]
        exact hv
      obtain ⟨c, hc⟩ := ha3 (a⁻¹ v) hFu
      refine ⟨-c, ?_⟩
      rw [hu] at hc
      rw [neg_smul, ← sub_eq_add_neg]
      exact eq_sub_of_add_eq hc.symm

@[expose] def pointRad (F : LinearMap.BilinForm K V) (e : V) : Set (V ≃ₗ[K] V) :=
  (pointRadSubgroup F e : Set (V ≃ₗ[K] V))

@[expose] def ElationFull (F : LinearMap.BilinForm K V) (D : Set (V ≃ₗ[K] V)) (e : V) : Prop :=
  ∀ φ : Module.Dual K V, φ e = 0 → ∃ g ∈ D, ∀ v, F v e = 0 → g v = v + φ v • e

@[expose] def orthSubgroup (Qf : QuadraticForm K V) : Subgroup (V ≃ₗ[K] V) where
  carrier := {g | ∀ v, Qf (g v) = Qf v}
  mul_mem' := fun {a b} ha hb v => by
    simp only [LinearEquiv.mul_apply]
    rw [ha, hb]
  one_mem' := fun v => rfl
  inv_mem' := fun {g} hg v => by
    have := hg (g⁻¹ v)
    have hu : g (g⁻¹ v) = v := by simp
    rw [hu] at this
    exact this.symm

@[expose] def sympSubgroup (F : LinearMap.BilinForm K V) : Subgroup (V ≃ₗ[K] V) where
  carrier := {g | IsIsom F g}
  mul_mem' := fun {a b} ha hb x y => by
    simp only [LinearEquiv.mul_apply]
    rw [ha, hb]
  one_mem' := fun x y => rfl
  inv_mem' := fun {g} hg x y => by
    have := hg (g⁻¹ x) (g⁻¹ y)
    have hu : ∀ v, g (g⁻¹ v) = v := by simp
    rw [hu, hu] at this
    exact this.symm

@[expose] def TheoremXStatement : Prop :=
  ∀ (K V : Type) [Field K] [Finite K] [CharP K 2] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (F : LinearMap.BilinForm K V), 4 ≤ Nat.card K →
    F.Nondegenerate → F.IsAlt → 4 ≤ Module.finrank K V →
    ∀ (H : Subgroup (V ≃ₗ[K] V)), H ≤ sympSubgroup F →
    ∀ (P : Set V), (∀ e ∈ P, e ≠ 0) → Submodule.span K P = ⊤ →
    (∀ e ∈ P, ElationFull F ((H : Set _) ∩ pointRad F e) e) →
    H = Subgroup.closure (⋃ e ∈ P, (H : Set _) ∩ pointRad F e) →
      H = sympSubgroup F ∨
        ∃ Qf : QuadraticForm K V, Qf.polarBilin = F ∧
          H = ⁅orthSubgroup Qf, orthSubgroup Qf⁆

@[expose] def LemmaPStatement : Prop :=
  ∀ (K V : Type) [Field K] [Finite K] [CharP K 2] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (F : LinearMap.BilinForm K V), 4 ≤ Nat.card K →
    F.Nondegenerate → F.IsAlt → Module.finrank K V = 4 →
    ∀ (e f : V), F e f = 1 →
    ∀ (A A' : Subgroup (V ≃ₗ[K] V)), (A : Set _) ⊆ pointRad F e → (A' : Set _) ⊆ pointRad F f →
      ElationFull F A e → ElationFull F A' f →
        A ⊔ A' = sympSubgroup F ∨
          ∃ Qf : QuadraticForm K V, Qf.polarBilin = F ∧ Qf e = 0 ∧ Qf f = 0 ∧
            A ≤ orthSubgroup Qf ∧ A' ≤ orthSubgroup Qf

@[expose] def SiegelGenStatement : Prop :=
  ∀ (K V : Type) [Field K] [Finite K] [CharP K 2] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (Qf : QuadraticForm K V), 4 ≤ Nat.card K →
    Qf.polarBilin.Nondegenerate → 4 ≤ Module.finrank K V → (∃ e, e ≠ 0 ∧ Qf e = 0) →
      ⁅orthSubgroup Qf, orthSubgroup Qf⁆ =
        Subgroup.closure (⋃ e ∈ {e : V | e ≠ 0 ∧ Qf e = 0},
          (orthSubgroup Qf : Set _) ∩ pointRad Qf.polarBilin e)

end Abstract

end CFSG.RankThree.GF2n.Stroth80.Classify
