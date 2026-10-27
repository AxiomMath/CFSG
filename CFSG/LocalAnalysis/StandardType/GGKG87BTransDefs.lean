module

public import CFSG.LieType.Chevalley.RootCharacterConjugation
public import CFSG.LieType.Chevalley.KernelComponentRoots
public import CFSG.LieType.Chevalley.Canonical
public import CFSG.Blueprint.ChevalleyPinned

public section

namespace CFSG.StandardType.KG87B

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

@[expose] def blockRoots : Set (Fin Tag.E6.rank → ℤ) :=
  {γ | IsRoot Tag.E6 γ ∧ γ ⟨1, by decide⟩ = 0 ∧ γ ⟨3, by decide⟩ = 0}

@[expose] noncomputable def blockGroup
    (Ω : Type) [Field Ω] : Subgroup (ModGL Tag.E6 Ω) :=
  rootSpan Tag.E6 Ω blockRoots

@[expose] def thirdTorus (Ω : Type) [Field Ω] : Subgroup (ModGL Tag.E6 Ω) where
  carrier := {g | ∃ a : Fin Tag.E6.rank → Ωˣ,
    a ⟨0, by decide⟩ = 1 ∧ a ⟨2, by decide⟩ = 1 ∧ a ⟨4, by decide⟩ = 1 ∧ a ⟨5, by decide⟩ = 1 ∧
      g = rootDiagUnit Tag.E6 a}
  mul_mem' := by
    rintro _ _ ⟨a, h0, h2, h4, h5, rfl⟩ ⟨b, h0', h2', h4', h5', rfl⟩
    exact ⟨a * b, by simp [h0, h0'], by simp [h2, h2'], by simp [h4, h4'], by simp [h5, h5'],
      (rootDiagUnit_mul a b).symm⟩
  one_mem' := ⟨1, rfl, rfl, rfl, rfl, rootDiagUnit_one.symm⟩
  inv_mem' := by
    rintro _ ⟨a, h0, h2, h4, h5, rfl⟩
    exact ⟨a⁻¹, by simp [h0], by simp [h2], by simp [h4], by simp [h5], rootDiagUnit_inv a⟩

@[expose] noncomputable def thirdCox : WeylGroup Tag.E6 :=
  rootReflection ![0, 1, 0, 0, 0, 0] * rootReflection ![1, 1, 2, 3, 2, 1]

@[expose] noncomputable def thirdWeyl
    (Ω : Type) [Field Ω] : ModGL Tag.E6 Ω :=
  canonicalRep (coxeterSystem Tag.E6) Ω thirdCox

end CFSG.StandardType.KG87B

end
