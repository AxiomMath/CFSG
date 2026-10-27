module

public import CFSG.LocalAnalysis.WeakClosure81.W16PIrrOrbit
public import CFSG.LocalAnalysis.WeakClosure81.W16PIrrBar
public import CFSG.LocalAnalysis.WeakClosure81.SevenElevenW3
public import CFSG.Monster.B.Fischer.Fi22Order

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Quasithin CFSG.Open Subgroup
open CFSG.LocalAnalysis.WeakClosure81.SevenK

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
variable {G : Subgroup (LGL 2 V)} {Γ : Set (Subgroup (LGL 2 V))}
  {VA : Subgroup (LGL 2 V) → Submodule (ZMod 2) V} {i : ℕ}

section Certified


theorem eq_bot_or_eq_of_assumption131 (hTim : TimmesfeldTIRootInput)
    (h : Assumption131 G Γ VA i) (hrank : ∀ B ∈ Γ, mRank B ≤ i)
    (hVAle : ∀ B ∈ Γ, VA B ≤ fixSub B) {A B₀ : Subgroup (LGL 2 V)} (hA : A ∈ Γ) (hB₀ : B₀ ≤ A)
    (hN : G ⊓ Subgroup.normalizer (A : Set (LGL 2 V)) ≤
      Subgroup.normalizer (B₀ : Set (LGL 2 V))) :
    B₀ = ⊥ ∨ B₀ = A := by
  obtain ⟨G₁, hG₁G, -, hsub, hgen, h₁⟩ := exists_le_cjOrbit_assumption131 h hA
  have hrank₁ : ∀ B ∈ cjOrbit G₁ A, mRank B ≤ i := fun B hB => hrank B (hsub hB)
  have hVAle₁ : ∀ B ∈ cjOrbit G₁ A, VA B ≤ fixSub B := fun B hB => hVAle B (hsub hB)
  exact eq_bot_or_eq_of_hyp711 hTim h₁ hrank₁ (mem_cjOrbit_self G₁ A) hB₀
    ((inf_le_inf_right _ hG₁G).trans hN) (hyp711_UAOf_of_eq_iSup h₁ hrank₁ hVAle₁ hgen)
    (isBarMap_mk_pCore _)

end Certified

end CFSG.LocalAnalysis.WeakClosure81

end
