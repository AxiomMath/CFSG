module

public import CFSG.LocalAnalysis.StandardType.GGR4JMeetKGDefs
public import CFSG.LocalAnalysis.StandardType.GGPDDefs
public import CFSG.LocalAnalysis.StandardType.GGPDCoords
public import CFSG.LocalAnalysis.StandardType.GGPDComm
public import CFSG.LocalAnalysis.StandardType.GGPDLift
public import CFSG.LocalAnalysis.StandardType.GGPDInversion
public import CFSG.LocalAnalysis.StandardType.GGPDSection

public section

namespace CFSG.StandardType

open CFSG.Assembly

private theorem pds_M_eq {Γ : Type} {C : Matrix Γ Γ ℤ} (e : Fin 4 ≃ Γ)
    (he : (∀ i j, C (e i) (e j) = CartanMatrix.F₄ i j) ∨
      (∀ i j, C (e i) (e j) = CartanMatrix.F₄ j i)) :
    (Matrix.of fun j k => (C (e j) (e k) : ZMod 3)) = ggPDC3 ∨
      (Matrix.of fun j k => (C (e j) (e k) : ZMod 3)) = ggPDC3.transpose := by
  rcases he with h | h
  · left
    ext i j
    rw [Matrix.of_apply, h i j]
    rfl
  · right
    ext i j
    rw [Matrix.of_apply, h i j, Matrix.transpose_apply]
    rfl

private def pds_rhoA {M : Type*} [Group M] (κ : Additive M ≃+ (Fin 4 → ZMod 3)) :
    Multiplicative (Fin 4 → ZMod 3) →* M :=
  { toFun := fun v => Additive.toMul (κ.symm (Multiplicative.toAdd v))
    map_one' := by
      show Additive.toMul (κ.symm (Multiplicative.toAdd 1)) = 1
      rw [toAdd_one, map_zero, toMul_zero]
    map_mul' := fun v w => by
      show Additive.toMul (κ.symm (Multiplicative.toAdd (v * w))) =
        Additive.toMul (κ.symm (Multiplicative.toAdd v)) *
          Additive.toMul (κ.symm (Multiplicative.toAdd w))
      rw [toAdd_mul, map_add, toMul_add] }

private theorem pds_rhoA_injective {M : Type*} [Group M]
    (κ : Additive M ≃+ (Fin 4 → ZMod 3)) : Function.Injective (pds_rhoA κ) := by
  intro v w h
  change Additive.toMul (κ.symm (Multiplicative.toAdd v)) =
    Additive.toMul (κ.symm (Multiplicative.toAdd w)) at h
  have h2 : κ.symm (Multiplicative.toAdd v) = κ.symm (Multiplicative.toAdd w) :=
    Additive.toMul.injective h
  have h3 : Multiplicative.toAdd v = Multiplicative.toAdd w := κ.symm.injective h2
  exact Multiplicative.toAdd.injective h3

theorem ggPD_reduction {K : Type} [Field K] {d : ℕ}
    {A : Subgroup (Matrix.GeneralLinearGroup (Fin d) K ⧸
      Subgroup.center (Matrix.GeneralLinearGroup (Fin d) K))}
    (hA : IsElemAbelian 3 A) (hcard : Nat.card A = 3 ^ 4)
    [Fact (Nat.Prime 3)] {Γ : Type} [Fintype Γ] [DecidableEq Γ] {C : Matrix Γ Γ ℤ}
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {ι : Additive ↥A ≃+ V}
    {φ : Γ → MulAut ↥A} {h : Γ → V} {α : Γ → Module.Dual (ZMod 3) V}
    (hD : GGExtDatum ι C φ h α)
    (hF4 : ∃ e : Fin 4 ≃ Γ, (∀ i j, C (e i) (e j) = CartanMatrix.F₄ i j) ∨
      (∀ i j, C (e i) (e j) = CartanMatrix.F₄ j i)) :
    ∃ M : Matrix (Fin 4) (Fin 4) (ZMod 3), (M = ggPDC3 ∨ M = ggPDC3.transpose) ∧
      ∃ ρ : Multiplicative (Fin 4 → ZMod 3) →* Matrix.GeneralLinearGroup (Fin d) K,
        (∀ v, ρ v ∈ Subgroup.center (Matrix.GeneralLinearGroup (Fin d) K) → v = 1) ∧
        (∃ z : Matrix.GeneralLinearGroup (Fin d) K, ∀ v, z * ρ v * z⁻¹ = ρ v⁻¹) ∧
        ∀ i : Fin 4, ∃ g : Matrix.GeneralLinearGroup (Fin d) K, ∀ v, ∃ c : Kˣ,
          g * ρ v * g⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin d) c *
            ρ (Multiplicative.ofAdd ((ggPDRefl M i).mulVec (Multiplicative.toAdd v))) := by
  classical
  obtain ⟨e, he⟩ := hF4
  have hΓ : Fintype.card Γ = 4 := by
    rw [Fintype.card_congr e.symm, Fintype.card_fin]
  have hcomm := ggPD_comap_commute hA hcard hD hΓ
  obtain ⟨z, hz⟩ := ggPD_inversion_lift hcard hD e he
  have hexp : ∀ a : ↥A, a ^ 3 = 1 := by
    intro a
    apply Subtype.ext
    simpa using hA.2 a.1 a.2
  obtain ⟨τ, hτπ, hτz⟩ := ggPD_section hexp hcomm hz
  obtain ⟨κ, hκ⟩ := ggPD_coords hcard hD e
  let M : Matrix (Fin 4) (Fin 4) (ZMod 3) :=
    Matrix.of fun j k => (C (e j) (e k) : ZMod 3)
  have hM : M = ggPDC3 ∨ M = ggPDC3.transpose := by
    simpa [M] using pds_M_eq e he
  let π := QuotientGroup.mk' (Subgroup.center (Matrix.GeneralLinearGroup (Fin d) K))
  let ρA : Multiplicative (Fin 4 → ZMod 3) →* ↥A := pds_rhoA κ
  let ρ : Multiplicative (Fin 4 → ZMod 3) →* Matrix.GeneralLinearGroup (Fin d) K :=
    τ.comp ρA
  refine ⟨M, hM, ρ, ?_, ?_, ?_⟩
  · intro v hv
    have hρπ : π (ρ v) = (ρA v : Matrix.GeneralLinearGroup (Fin d) K ⧸
        Subgroup.center (Matrix.GeneralLinearGroup (Fin d) K)) := by
      simpa [ρ, π] using hτπ (ρA v)
    have h1 : π (ρ v) = 1 := (QuotientGroup.eq_one_iff (ρ v)).mpr hv
    have h2 : ρA v = 1 := Subtype.ext (hρπ.symm.trans h1)
    exact pds_rhoA_injective κ (h2.trans (map_one ρA).symm)
  · refine ⟨z, fun v => ?_⟩
    have h2 : ρ v⁻¹ = (ρ v)⁻¹ := map_inv ρ v
    rw [h2]
    simpa [ρ] using hτz (ρA v)
  · intro i
    obtain ⟨g, hg⟩ := ggPD_normalizer_lift hD (e i)
    refine ⟨g, fun v => ?_⟩
    let a : ↥A := ρA v
    have hπρ : π (ρ v) = a := by simpa [ρ, a, π] using hτπ a
    have hπg : π (g * ρ v * g⁻¹) = φ (e i) a := by
      have := hg (ρ v) a hπρ
      simpa [π] using this
    have hπτ : π (τ (φ (e i) a)) = φ (e i) a := by
      simpa [π] using hτπ (φ (e i) a)
    have hwπ : π ((τ (φ (e i) a))⁻¹ * (g * ρ v * g⁻¹)) = 1 := by
      rw [map_mul, map_inv, hπg, hπτ]
      simp
    have hw : (τ (φ (e i) a))⁻¹ * (g * ρ v * g⁻¹) ∈
        Subgroup.center (Matrix.GeneralLinearGroup (Fin d) K) :=
      (QuotientGroup.eq_one_iff _).mp hwπ
    have hwrange : (τ (φ (e i) a))⁻¹ * (g * ρ v * g⁻¹) ∈
        (Matrix.GeneralLinearGroup.scalar (Fin d)).range := by
      rw [← Matrix.GeneralLinearGroup.center_eq_range_scalar]
      exact hw
    obtain ⟨c, hc⟩ := MonoidHom.mem_range.mp hwrange
    refine ⟨c, ?_⟩
    have ha : Additive.ofMul a = κ.symm (Multiplicative.toAdd v) := by
      show Additive.ofMul (Additive.toMul (κ.symm (Multiplicative.toAdd v))) =
        κ.symm (Multiplicative.toAdd v)
      simp
    have hκa : κ (Additive.ofMul (φ (e i) a)) =
        (ggPDRefl M i).mulVec (Multiplicative.toAdd v) := by
      have hh := hκ i a
      rw [ha] at hh
      simpa using hh
    have hφ : φ (e i) a =
        ρA (Multiplicative.ofAdd ((ggPDRefl M i).mulVec (Multiplicative.toAdd v))) := by
      have h2 : Additive.ofMul (φ (e i) a) =
          κ.symm ((ggPDRefl M i).mulVec (Multiplicative.toAdd v)) := by
        apply κ.injective
        rw [hκa, κ.apply_symm_apply]
      have h3 := congrArg Additive.toMul h2
      simpa [ρA, pds_rhoA] using h3
    have hτφ : ρ (Multiplicative.ofAdd ((ggPDRefl M i).mulVec (Multiplicative.toAdd v))) =
        τ (φ (e i) a) := by
      change τ (ρA (Multiplicative.ofAdd ((ggPDRefl M i).mulVec (Multiplicative.toAdd v)))) =
        τ (φ (e i) a)
      rw [← hφ]
    rw [hτφ]
    have hscalar : g * ρ v * g⁻¹ =
        Matrix.GeneralLinearGroup.scalar (Fin d) c * τ (φ (e i) a) := by
      rw [Matrix.GeneralLinearGroup.scalar_commute, hc]
      group
    exact hscalar

end CFSG.StandardType

end
