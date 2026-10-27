module

public import CFSG.LocalAnalysis.StandardType.GGTBJReflLemma

public section

namespace CFSG.StandardType

theorem exists_not_commute_reflection_fun {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] [Module.Finite (ZMod p) V]
    {ι : Type} [Nonempty ι] (f : ι → Module.Dual (ZMod p) V) (v : ι → V)
    (hfv : ∀ i, f i (v i) = 2)
    (hconn : ∀ S : Set ι, S.Nonempty →
      (∀ i j, (f i (v j) ≠ 0 ∨ f j (v i) ≠ 0) → (i ∈ S ↔ j ∈ S)) → S = Set.univ)
    (hcodim : Module.finrank (ZMod p) ↥(⨅ i, LinearMap.ker (f i) : Submodule (ZMod p) V) + 2 ≤
      Module.finrank (ZMod p) V) :
    ∃ (i j : ι) (w : V),
      (w - f j w • v j) - f i (w - f j w • v j) • v i ≠
        (w - f i w • v i) - f j (w - f i w • v i) • v j := by
  by_contra hcon
  push Not at hcon
  obtain ⟨i, j, hij⟩ := exists_not_commute_reflection_of_connected hp2 f v hfv hconn hcodim
  apply hij
  rw [commute_iff_eq]
  refine LinearEquiv.ext fun w => ?_
  simp only [LinearEquiv.mul_apply, Module.reflection_apply]
  exact hcon i j w

end CFSG.StandardType

end
