module

public import CFSG.Assembly.Defs
public import CFSG.Foundations.Basic

public section

namespace CFSG.LocalAnalysis

open Subgroup

namespace FaithfulPerfectInclusion

variable {G : Type*} [Group G]

theorem pCoreOf_eq_inSubgroup (p : ℕ) (H : Subgroup G) :
    CFSG.Assembly.pCoreOf p H = CFSG.inSubgroup (CFSG.pCore p) H :=
  rfl

theorem map_closure_omegaOne {M : Type*} [Group M] (f : M →* G) (hf : Function.Injective f)
    (H : Subgroup M) :
    (closure {a | a ∈ H ∧ (∀ b ∈ H, a * b = b * a) ∧ a ^ 2 = 1}).map f =
      closure {a | a ∈ H.map f ∧ (∀ b ∈ H.map f, a * b = b * a) ∧ a ^ 2 = 1} := by
  rw [MonoidHom.map_closure]
  congr 1
  ext a
  constructor
  · rintro ⟨a, ⟨ha, hc, hsq⟩, rfl⟩
    refine ⟨⟨a, ha, rfl⟩, ?_, by rw [← map_pow, hsq, map_one]⟩
    rintro _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hc b hb]
  · rintro ⟨⟨a, ha, rfl⟩, hc, hsq⟩
    refine ⟨a, ⟨ha, fun b hb => hf ?_, hf ?_⟩, rfl⟩
    · rw [map_mul, map_mul]
      exact hc (f b) ⟨b, hb, rfl⟩
    · rw [map_pow, map_one]
      exact hsq

end FaithfulPerfectInclusion

open FaithfulPerfectInclusion

end CFSG.LocalAnalysis
