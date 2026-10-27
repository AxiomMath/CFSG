module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.LocalAnalysis.WeakClosure81.SzExcl

structure SzBarTriple {X : Type} [Group X] (t c₂ c₃ g : X) : Prop where
  sq : t * t = 1
  ne_one : t ≠ 1
  comm₁₂ : t * (c₂⁻¹ * t * c₂) = c₂⁻¹ * t * c₂ * t
  ne₁₂ : c₂⁻¹ * t * c₂ ≠ t
  not_comm₁₃ : t * (c₃⁻¹ * t * c₃) ≠ c₃⁻¹ * t * c₃ * t
  not_comm₂₃ : c₂⁻¹ * t * c₂ * (c₃⁻¹ * t * c₃) ≠ c₃⁻¹ * t * c₃ * (c₂⁻¹ * t * c₂)
  not_isPGroup : ¬ IsPGroup 2 ↥(Subgroup.closure ({t, c₃⁻¹ * t * c₃} : Set X))
  mem : g ∈ Subgroup.closure ({t, c₂⁻¹ * t * c₂, c₃⁻¹ * t * c₃} : Set X)
  mul_self : g * g = t

end CFSG.LocalAnalysis.WeakClosure81.SzExcl
