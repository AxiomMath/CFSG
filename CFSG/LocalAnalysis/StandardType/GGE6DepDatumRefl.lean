module

public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelResidualData
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelAut

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {G : Type} [Group G]

private theorem ggIsReflection_of_datum_node {Bs : Subgroup G} {Λ : Type} {V : Type*}
    [AddCommGroup V] [Module (ZMod 3) V]
    (ι : Additive ↥Bs ≃+ V) (φ : Option Λ → MulAut ↥Bs)
    (h : Option Λ → V) (α : Option Λ → Module.Dual (ZMod 3) V)
    (hαh : ∀ node, α node (h node) = 2)
    (hlin : ∀ node vector, ggLin (p := 3) ι (φ node) vector =
      vector - α node vector • h node) :
    ∀ node, GGIsReflection 3 (φ node) := fun node =>
  ggIsReflection_of_eq_reflection (p := 3) (by norm_num) ι (hαh node)
    (ggLin_eq_reflection (p := 3) ι (hαh node) (hlin node))

theorem ggDatum_reflections {Bs L K : Subgroup G} (hD : GGDependentReflectionDatum 3 Bs L K) :
    ∃ (Λ : Type) (_ : Fintype Λ) (_ : DecidableEq Λ) (b : Λ) (ρ : Λ → MulAut ↥Bs)
      (ρa : MulAut ↥Bs),
      (∀ l, GGIsReflection 3 (ρ l)) ∧ GGIsReflection 3 ρa ∧
      ggAutomizer L Bs = Subgroup.closure (Set.range ρ) ∧
      ggAutomizer K Bs = Subgroup.closure
        (Set.range (fun l : {l : Λ // l ≠ b} => ρ l) ∪ {ρa}) := by
  obtain ⟨Λ, hΛ, hdec, V, hV, hmod, ι, φ, h, α, b, hαh, -, hlin, -, hL, hK⟩ := hD
  have hnode : ∀ node : Option Λ, GGIsReflection 3 (φ node) :=
    ggIsReflection_of_datum_node ι φ h α hαh hlin
  exact ⟨Λ, hΛ, hdec, b, (fun l => φ (some l)), φ none,
    fun l => hnode (some l), hnode none, hL, hK⟩

end CFSG.StandardType

end
