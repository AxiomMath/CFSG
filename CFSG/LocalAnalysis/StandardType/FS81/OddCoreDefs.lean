module

public import CFSG.LocalAnalysis.StandardType.FS81.Pieces

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Assembly

@[expose] def TransvAll {G : Type} [Group G] (b₀ : G) (K E : Subgroup G) : Prop :=
  (∀ g ∈ Subgroup.normalizer (E : Set G), ∀ a ∈ E ⊓ K, g * a * g⁻¹ ∈ E ⊓ K) ∧
    ∀ β ∈ E ⊓ K, ∃ g ∈ Subgroup.normalizer (E : Set G),
      (∀ a ∈ E ⊓ K, g * a * g⁻¹ = a) ∧ g * b₀ * g⁻¹ = b₀ * β

@[expose] def OddCoreTransvAt (r : Row) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (b₀ : G) (K E : Subgroup G),
    StdAssumptions b₀ K E r → ∀ B : Basis3 G (r.n + 1), Adapted B b₀ K E → LocalData r B b₀ →
      Fus42 B b₀ → ¬ OddCoreTrivial E → TransvAll b₀ K E

@[expose] def NoTransv : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (b₀ : G) (K E : Subgroup G) (r : Row),
    StdAssumptions b₀ K E r → ∀ B : Basis3 G (r.n + 1), Adapted B b₀ K E → LocalData r B b₀ →
      Fus42 B b₀ → ¬ TransvAll b₀ K E

theorem l1OddCore_of_split (h6 : OddCoreTransvAt Row.D6) (h7 : OddCoreTransvAt Row.twD7)
    (hE7 : OddCoreTransvAt Row.E7) (hno : NoTransv) : L1OddCore := by
  intro G _ _ b₀ K E r hstd B hB hloc hfus
  by_contra hodd
  have htr : TransvAll b₀ K E := by
    cases r with
    | D6 => exact h6 G b₀ K E hstd B hB hloc hfus hodd
    | twD7 => exact h7 G b₀ K E hstd B hB hloc hfus hodd
    | E7 => exact hE7 G b₀ K E hstd B hB hloc hfus hodd
  exact hno G b₀ K E r hstd B hB hloc hfus htr

end CFSG.StandardType.FrameRoute.FS81

end
