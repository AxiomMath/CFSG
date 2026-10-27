module

public import CFSG.LocalAnalysis.LargeEvenClassification.FactorOrbitSylow
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherDescents
public import CFSG.Quasithin.Vol2.Ch1Xi
public import CFSG.Quasithin.Vol2.KGNatSL3Real

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS.C11P9A

open Matrix CFSG.Quasithin CFSG.Quasithin.Vol2.KGNat
  CFSG.ClassicalInvolution.ModelFacts.OddCover CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.Open (pCoreOf)
open CFSG.Assembly.LowTwoRank (StatedSL)

section Transport

variable {G G' : Type*} [Group G] [Group G'] (φ : G →* G') (hφ : Function.Injective φ)
include hφ

theorem map_mem_normalizer_iff {X : Subgroup G} {A : G} :
    φ A ∈ Subgroup.normalizer ((X.map φ : Subgroup G') : Set G') ↔
      A ∈ Subgroup.normalizer (X : Set G) := by
  simp only [Subgroup.mem_normalizer_iff]
  constructor
  · intro h x
    have := h (φ x)
    rwa [Subgroup.mem_map_iff_mem hφ, ← map_inv, ← map_mul, ← map_mul,
      Subgroup.mem_map_iff_mem hφ] at this
  · intro h y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨A * x * A⁻¹, (h x).mp hx, by rw [map_mul, map_mul, map_inv]⟩
    · rintro ⟨z, hz, hzy⟩
      refine ⟨A⁻¹ * z * A, (h _).mpr ?_, ?_⟩
      · rwa [show A * (A⁻¹ * z * A) * A⁻¹ = z by group]
      · rw [map_mul, map_mul, map_inv, hzy]
        group

theorem map_inf_sectionCentralizer (S X Y : Subgroup G) :
    S.map φ ⊓ sectionCentralizer (X.map φ) (Y.map φ) = (S ⊓ sectionCentralizer X Y).map φ := by
  ext z
  constructor
  · rintro ⟨⟨s, hs, rfl⟩, hnX, hnY, hc⟩
    refine ⟨s, ⟨hs, (map_mem_normalizer_iff φ hφ).mp hnX, (map_mem_normalizer_iff φ hφ).mp hnY,
      fun x hx => ?_⟩, rfl⟩
    have := hc (φ x) ⟨x, hx, rfl⟩
    rwa [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul,
      Subgroup.mem_map_iff_mem hφ] at this
  · rintro ⟨s, ⟨hs, hnX, hnY, hc⟩, rfl⟩
    refine ⟨⟨s, hs, rfl⟩, (map_mem_normalizer_iff φ hφ).mpr hnX,
      (map_mem_normalizer_iff φ hφ).mpr hnY, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
    exact ⟨_, hc x hx, rfl⟩

theorem pCoreOf_map_of_injective [Finite G] [Finite G'] (p : ℕ) (X : Subgroup G) :
    pCoreOf p (X.map φ) = (pCoreOf p X).map φ := by
  rw [CFSG.LargeEvenClassification.Helpers.pCoreOf_map_injective p X φ hφ, pCoreOf,
    Subgroup.map_map]

end Transport

section Realization

variable {K : Type} [Field K] {W : Type*} [CommGroup W] {H : Subgroup (MulAut W)}
  {Z : Subgroup W} {π : ↥(StatedSL 3 K) →* ↥H} {f : W → (Fin 3 → K)}

@[expose] noncomputable def psiW (π : ↥(StatedSL 3 K) →* ↥H) (g : SpecialLinearGroup (Fin 3) K) :
    SpecialLinearGroup (Fin 3) K →* MulAut W :=
  H.subtype.comp ((rho3 π).comp (MulAut.conj g).toMonoidHom)

theorem psiW_apply (π : ↥(StatedSL 3 K) →* ↥H) (g A : SpecialLinearGroup (Fin 3) K) :
    psiW π g A = ((rho3 π (g * A * g⁻¹) : ↥H) : MulAut W) := rfl

theorem psiW_injective (hf : IsCoord (linModelNat (StatedSL 3 K)) H Z π f)
    (g : SpecialLinearGroup (Fin 3) K) : Function.Injective (psiW π g) :=
  H.subtype_injective.comp ((rho3_bijective hf).1.comp (MulAut.conj g).injective)

theorem psiW_mul (π : ↥(StatedSL 3 K) →* ↥H) (g x : SpecialLinearGroup (Fin 3) K) :
    psiW π (g * x) = (psiW π g).comp (MulAut.conj x).toMonoidHom := by
  ext A
  rw [MonoidHom.comp_apply, psiW_apply, psiW_apply]
  congr 3
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  group

theorem exists_psiW_eq (hf : IsCoord (linModelNat (StatedSL 3 K)) H Z π f)
    (g : SpecialLinearGroup (Fin 3) K) {x : MulAut W} (hx : x ∈ H) :
    ∃ A, psiW π g A = x := by
  obtain ⟨B, hB⟩ := (rho3_bijective hf).2 ⟨x, hx⟩
  exact ⟨g⁻¹ * B * g, by rw [psiW_apply, show g * (g⁻¹ * B * g) * g⁻¹ = B by group, hB]⟩

theorem psiW_mem (π : ↥(StatedSL 3 K) →* ↥H) (g A : SpecialLinearGroup (Fin 3) K) :
    psiW π g A ∈ H :=
  (rho3 π (g * A * g⁻¹)).2

end Realization

end CFSG.Quasithin.Vol2.Ch11.SecS.C11P9A
