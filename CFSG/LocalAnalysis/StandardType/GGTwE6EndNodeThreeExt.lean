module

public import CFSG.LocalAnalysis.StandardType.GGTwE6RootKillDefs
import CFSG.LieType.Chevalley.OddDiagramFrobeniusFixedDerived
import Mathlib.FieldTheory.Finite.Extension

public section

namespace CFSG.StandardType.TwE6EndNode3

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.StandardType.TwE6RootKill

section Ext

theorem exists_cubic_ext {n : ℕ} {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ n) ^ 2)
    (h2 : ringChar K = 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n) :
    ∃ (K₃ : Type) (_ : Field K₃) (_ : Finite K₃) (ι : K →+* K₃) (σ₃ : K₃ ≃+* K₃),
      Nat.card K₃ = ((2 ^ n) ^ 3) ^ 2 ∧ (∀ c, σ₃ c = c ^ (2 ^ n) ^ 3) ∧
        ∀ c, σ₃ (ι c) = ι (σ c) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := ringChar.of_eq h2
  haveI : CharP (FiniteField.Extension K 2 3) 2 :=
    charP_of_injective_algebraMap (algebraMap K (FiniteField.Extension K 2 3)).injective 2
  have hinj : Function.Injective (iterateFrobenius (FiniteField.Extension K 2 3) 2 (n * 3)) :=
    (iterateFrobenius (FiniteField.Extension K 2 3) 2 (n * 3)).injective
  have hpow : ∀ c : K, c ^ (2 ^ n) ^ 2 = c := fun c => by
    haveI := Fintype.ofFinite K
    have h := FiniteField.pow_card c
    rwa [← Nat.card_eq_fintype_card, hK] at h
  refine ⟨FiniteField.Extension K 2 3, inferInstance, inferInstance,
    algebraMap K (FiniteField.Extension K 2 3),
    RingEquiv.ofBijective (iterateFrobenius (FiniteField.Extension K 2 3) 2 (n * 3))
      ⟨hinj, Finite.surjective_of_injective hinj⟩, ?_, fun c => ?_, fun c => ?_⟩
  · rw [FiniteField.natCard_extension, hK]
    ring
  · change iterateFrobenius (FiniteField.Extension K 2 3) 2 (n * 3) c = c ^ (2 ^ n) ^ 3
    rw [iterateFrobenius_def, pow_mul]
  · change iterateFrobenius (FiniteField.Extension K 2 3) 2 (n * 3)
      (algebraMap K (FiniteField.Extension K 2 3) c) = algebraMap K _ (σ c)
    have h3 : (2 : ℕ) ^ (n * 3) = (2 ^ n) ^ 2 * 2 ^ n := by ring
    rw [iterateFrobenius_def, ← map_pow, hσ c, h3, pow_mul, hpow]

end Ext

section Norm

variable {K K₃ : Type} [Field K] [Finite K] [Field K₃] [Finite K₃]

theorem twNormTwo_baseChange
    (ι : K →+* K₃) (σ : K ≃+* K) (σ₃ : K₃ ≃+* K₃) (h : ∀ c, σ₃ (ι c) = ι (σ c))
    {A : Subgroup (ModGL TwistTag.E6.tag K)} (hU : TwNormTwo K σ A) :
    TwNormTwo K₃ σ₃ (A.map (baseChangeGL ι)) := by
  obtain ⟨U, hUC, hU1, hU2, hAU⟩ := hU
  refine ⟨U.map (baseChangeGL ι), ?_, fun hbot => hU1 ?_, hU2.map _, ?_⟩
  · rintro _ ⟨u, hu, rfl⟩
    exact map_baseChangeGL_graphFixedRootGroup_le (σ := σ.toRingHom) (Fr := σ₃.toRingHom)
      σ.surjective h (Subgroup.mem_map_of_mem _ (hUC hu))
  · exact (Subgroup.map_eq_bot_iff_of_injective U (baseChangeGL_injective ι)).1 hbot
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨u, hu, rfl⟩
    exact ⟨a * u * a⁻¹, hAU a ha u hu, by simp⟩

end Norm

end CFSG.StandardType.TwE6EndNode3

end
