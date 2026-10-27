module

public import CFSG.LocalAnalysis.WeakClosure81.W183Abs5

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Open Subgroup

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

namespace Assumption131

variable {G : Subgroup (LGL 2 V)} {Γ : Set (Subgroup (LGL 2 V))}
  {VA : Subgroup (LGL 2 V) → Submodule (ZMod 2) V} {i : ℕ}

theorem kernel_dichotomy (h : Assumption131 G Γ VA i) {A L : Subgroup (LGL 2 V)}
    [IsSimpleGroup ↥L] (hA : A ∈ Γ) (hr : mRank A ≤ i)
    (hnab : ∃ a ∈ L, ∃ b ∈ L, a * b ≠ b * a) (hLG : L ≤ G)
    (hAn : ∀ a ∈ A, ∀ l ∈ L, a * l * a⁻¹ ∈ L) :
    A ⊓ Subgroup.centralizer (L : Set (LGL 2 V)) = ⊥ ∨
      A ≤ Subgroup.centralizer (L : Set (LGL 2 V)) := by
  by_cases hbot : A ⊓ Subgroup.centralizer (L : Set (LGL 2 V)) = ⊥
  · exact Or.inl hbot
  · right
    obtain ⟨⟨t, ht⟩, ht1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hbot
    have htA : t ∈ A := (Subgroup.mem_inf.1 ht).1
    have htC : t ∈ Subgroup.centralizer (L : Set (LGL 2 V)) := (Subgroup.mem_inf.1 ht).2
    have htL : ∀ l ∈ L, t * l = l * t := fun l hl =>
      ((Subgroup.mem_centralizer_iff.1 htC) l hl).symm
    have hall := h.centralizes_of_ne_one_centralizes hA hr hnab hLG hAn htA
      (fun hh => ht1 (Subtype.ext hh)) htL
    intro a ha
    exact Subgroup.mem_centralizer_iff.2 fun l hl => (hall a ha l hl).symm

end Assumption131

end CFSG.LocalAnalysis.WeakClosure81

end
