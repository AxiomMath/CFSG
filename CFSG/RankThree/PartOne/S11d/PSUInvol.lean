module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.RankThree.PartOne.S11d.PSUMatrix

public section

namespace CFSG.RankThree.PartOne

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.RankThree.PartOne.OddIso

variable {F : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 F K)

theorem exists_isotropic_eigenvector_of_involution {A τ : GL (Fin 3) K}
    (hτ : ∀ v w, idForm h 3 (linOf τ v) (linOf τ w) = idForm h 3 v w) (hτ2 : τ ^ 2 = 1)
    (hτ1 : τ ≠ 1) (hAτ : A * τ = τ * A) :
    ∃ (w : Fin 3 → K) (μ : K), w ≠ 0 ∧ idForm h 3 w w = 0 ∧ linOf A w = μ • w := by
  classical
  have hKc : CharP K 2 := h.charP
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  set N : Module.End K (Fin 3 → K) := linOf τ - 1 with hN
  have hττ : ∀ v, linOf τ (linOf τ v) = v := fun v => by
    have := congrArg (fun g : GL (Fin 3) K => linOf g v) hτ2
    simpa [pow_two, linOf_mul, Module.End.mul_apply, linOf_one] using this
  have hNN : ∀ v, N (N v) = 0 := by
    intro v
    have e : N (N v) = (2 : K) • (v - linOf τ v) := by
      simp only [hN, LinearMap.sub_apply, Module.End.one_apply, map_sub, hττ]
      module
    rw [e, h2, zero_smul]
  have hrk_le : LinearMap.range N ≤ LinearMap.ker N := by
    rintro _ ⟨v, rfl⟩
    exact LinearMap.mem_ker.mpr (hNN v)
  have hN0 : N ≠ 0 := by
    intro h0
    apply hτ1
    apply linOf_injective
    rw [linOf_one]
    refine LinearMap.ext fun v => ?_
    have := LinearMap.congr_fun h0 v
    simpa [hN, sub_eq_zero] using this
  have hRne : LinearMap.range N ≠ ⊥ := by
    intro hb
    apply hN0
    refine LinearMap.ext fun v => ?_
    have hv : N v ∈ LinearMap.range N := ⟨v, rfl⟩
    rw [hb, Submodule.mem_bot] at hv
    simpa using hv
  have hsum : Module.finrank K (LinearMap.range N) + Module.finrank K (LinearMap.ker N) = 3 := by
    have := LinearMap.finrank_range_add_finrank_ker N
    rwa [Module.finrank_fin_fun] at this
  have hle : Module.finrank K (LinearMap.range N) ≤ Module.finrank K (LinearMap.ker N) :=
    Submodule.finrank_mono hrk_le
  have hpos : 1 ≤ Module.finrank K (LinearMap.range N) := Submodule.one_le_finrank_iff.mpr hRne
  have hr1 : Module.finrank K (LinearMap.range N) = 1 := by omega
  obtain ⟨w, hwR, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hRne
  have hspan : LinearMap.range N = Submodule.span K {w} :=
    (Submodule.eq_of_le_of_finrank_eq ((Submodule.span_singleton_le_iff_mem w _).mpr hwR)
      ((finrank_span_singleton hw0).trans hr1.symm)).symm
  have hAN : ∀ v, linOf A (N v) = N (linOf A v) := by
    intro v
    have := congrArg (fun g : GL (Fin 3) K => linOf g v) hAτ
    simp only [linOf_mul, Module.End.mul_apply] at this
    simp only [hN, LinearMap.sub_apply, Module.End.one_apply, map_sub, this]
  have hAw : linOf A w ∈ Submodule.span K {w} := by
    obtain ⟨v₀, hv₀⟩ := hwR
    rw [← hspan, ← hv₀, hAN]
    exact ⟨_, rfl⟩
  obtain ⟨μ, hμ⟩ := Submodule.mem_span_singleton.mp hAw
  refine ⟨w, μ, hw0, ?_, hμ.symm⟩
  obtain ⟨v₀, hv₀⟩ := hwR
  have hNw : N w = 0 := by rw [← hv₀]; exact hNN v₀
  have h1 : linOf τ w = w := by
    have := hNw
    simp only [hN, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at this
    exact this
  have h3 : linOf τ v₀ = v₀ + w := by
    rw [← hv₀]
    simp [hN]
  have e1 := hτ v₀ w
  rw [h1, h3, map_add, LinearMap.add_apply] at e1
  simpa using e1

end CFSG.RankThree.PartOne
