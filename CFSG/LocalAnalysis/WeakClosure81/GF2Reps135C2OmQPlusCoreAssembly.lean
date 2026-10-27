module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQScaffold
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQPlusRankNode
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQPlusKappaOne
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQPlusNodeZero
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesTensor

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LieType.Universal.Spin CFSG.Quasithin.SmithCurtis
open scoped Matrix TensorProduct

theorem omq_omPlus_core_of_interfaces (h1 : OmqPlusWeightVector) (h2 : OmqRankFromWeights)
    (h3 : OmqPlusDescent) {F : Type} [Field F] [Finite F] [CharP F 2] {n f : ℕ} (hn : 5 ≤ n)
    (hF : Nat.card F = 2 ^ f) (hf : 2 ≤ f) {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    [Finite V] {ρ : Representation (ZMod 2) (spinGroup (quadPlus n F)) V} (hρ : IsSimpleRep ρ)
    {y : spinGroup (quadPlus n F)} (hy2 : y * y = 1) (hρy : ρ y ≠ 1)
    (hr : Module.finrank (ZMod 2) (LinearMap.range (ρ y - 1)) ≤ 6) :
    ∃ T : V ≃+ (Fin n ⊕ Fin n → F), ∀ (s : spinGroup (quadPlus n F)) (v : V),
      T (ρ s v) =
        (spinMatrix (quadPlus n F) s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *ᵥ T v := by
  have hn3 : 3 ≤ n := by omega
  haveI : NeZero n := ⟨by omega⟩
  have hF4 : 4 ≤ Nat.card F := by
    rw [hF]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  haveI : ρ.IsIrreducible :=
    (CFSG.QuasithinUnique.Setup.SL2Modules.isIrreducible_iff ρ).mpr hρ
  haveI : Finite (CFSG.LieType.RootSystem.coxeterMatrix (isFiniteType_cartanD n)).Group :=
    CFSG.LieType.RootSystem.finite_group (isFiniteType_cartanD n)
  let D := omPlusCurtisDatum n F hn3
  obtain ⟨k, _hk, _hkc, _hka, _halg, ι, s, y₀, χ, μ, hs, hE, hsimp, ht, hfrob, hrank, htriv⟩ :=
    omq_endfield_scaffold D (F := F) ρ
  let σ := CFSG.Theory.Representation.extendScalars k (CFSG.endFieldRep ρ)
  haveI : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  haveI : FiniteDimensional (Module.End (MonoidAlgebra (ZMod 2) (spinGroup (quadPlus n F)))
      ρ.asModule) ρ.asModule :=
    CFSG.HardMathSupport.GuralnickMalle.finiteDimensional_endField ρ
  haveI : Module.Finite k (k ⊗[Module.End (MonoidAlgebra (ZMod 2) (spinGroup (quadPlus n F)))
      ρ.asModule] ρ.asModule) := inferInstance
  have hy1 : y ≠ 1 := fun h => hρy (by rw [h, map_one])
  have hσy : σ y ≠ 1 := fun h => hρy ((htriv y).mp h)
  have hrle : s * Module.finrank k (LinearMap.range (σ y - 1)) ≤ 6 := by
    calc s * Module.finrank k (LinearMap.range (σ y - 1))
        = Module.finrank (ZMod 2) (LinearMap.range (ρ y - 1)) := (hrank y).symm
      _ ≤ 6 := hr
  have hrpos : 1 ≤ Module.finrank k (LinearMap.range (σ y - 1)) := by
    rw [Submodule.one_le_finrank_iff]
    intro hbot
    exact hσy (sub_eq_zero.mp (LinearMap.range_eq_bot.mp hbot))
  by_cases hs1 : s = 1
  · have hχ1 : ∀ h ∈ D.H, χ h = 1 := by
      intro h hh
      have hsq : χ h ^ 2 = χ h := by simpa [hs1] using hfrob h hh
      have hne : χ h ≠ 0 := by
        intro h0
        have h1 : χ h * χ h⁻¹ = 1 := by
          rw [← ht.chi_mul hh (D.H.inv_mem hh), mul_inv_cancel, ht.chi_one]
        rw [h0, zero_mul] at h1
        exact zero_ne_one h1
      have h2 : χ h * χ h = χ h * 1 := by rw [← pow_two, hsq, mul_one]
      exact mul_left_cancel₀ hne h2
    have h7 := omq_omPlus_kappa_one_rank h1 h2 hn3 (omqPlusSevenRoots_of_five hn) hF4 ι hsimp ht
      hχ1 hy2 hσy
    have hr6 : Module.finrank k (LinearMap.range (σ y - 1)) ≤ 6 := by
      have h := hrle
      rw [hs1, one_mul] at h
      exact h
    change Module.finrank k (LinearMap.range
      (CFSG.Theory.Representation.extendScalars k (CFSG.endFieldRep ρ) y - 1)) ≤ 6 at hr6
    omega
  · have hs2 : 2 ≤ s := by omega
    have hr3 : Module.finrank k (LinearMap.range (σ y - 1)) ≤ 3 := by
      have h2r : 2 * Module.finrank k (LinearMap.range (σ y - 1)) ≤
          s * Module.finrank k (LinearMap.range (σ y - 1)) := Nat.mul_le_mul_right _ hs2
      have h26 : 2 * Module.finrank k (LinearMap.range (σ y - 1)) ≤ 6 := le_trans h2r hrle
      omega
    change Module.finrank k (LinearMap.range
      (CFSG.Theory.Representation.extendScalars k (CFSG.endFieldRep ρ) y - 1)) ≤ 3 at hr3
    have hsep0 : ∀ j : Fin n, μ j = D.dScalar χ j → j.val = 0 := by
      intro j hj
      by_contra hj0
      have h4 := omq_omPlus_four_le_rank_of_node hn hsimp ht hj0 hj hy2 hy1
      omega
    obtain ⟨i0, hi0⟩ := omq_omPlus_exists_separating hn3 hsimp ht hσy
    have hJ : ∀ i : Fin n, μ i = D.dScalar χ i ↔ i.val = 0 := by
      intro i
      constructor
      · exact hsep0 i
      · intro hi
        have hi0val : i0.val = 0 := hsep0 i0 hi0
        have hii : i = 0 := Fin.ext (by simpa using hi)
        have hi0eq : i0 = 0 := Fin.ext (by simpa using hi0val)
        rw [hii, ← hi0eq]
        exact hi0
    rcases omq_omPlus_node_zero_dichotomy h1 h2 hn3 hF4 ι hsimp ht hJ hy2 hσy with
      ⟨a, β, hβ⟩ | h4
    · exact h3 (by omega) ρ ι a β hβ
    · omega

end CFSG.LocalAnalysis.WeakClosure81
