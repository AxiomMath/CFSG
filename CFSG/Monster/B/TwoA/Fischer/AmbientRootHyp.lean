module

public import CFSG.Monster.B.TwoA.Fischer.AmbientRootClasses
public import CFSG.Monster.B.TwoA.Fischer.ChoiceExists

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent AddSubgroupClass.instZModModule

namespace CFSG.Monster.B.TwoA.Fischer

open CFSG.Monster.B.Fischer CFSG.Monster.B.TwoA CFSG.Monster.B.Classical.Mog22
open CFSG.Monster.B.E6.FixedE6 CFSG.Monster.B.E6.FixedE6Root CFSG.Monster.B.E6.StdF4
  CFSG.LieType.Chevalley.C2E6Std CFSG.LieType.Chevalley.C2E6Std.FieldExtension
open scoped IsMulCommutative

variable {S V : Type*} [Group S] {act : S →* Equiv.Perm V} {lab : V → S} {Y : Set V}

namespace IsFischerSlice

theorem ambient_root_orbits_hyp
    (hS : IsFischerSlice act lab Y)
    {ρ : sliceGroup lab Y →* stdGroup} (hρ : Function.Injective ρ)
    (hroot : ∀ y : Y, ρ ⟨lab y, lab_mem_sliceGroup y.2⟩ ∈ rootClass)
    (Q : Subgroup S) (hHQ : sliceGroup lab Y ≤ Q) (hQY : ∀ q ∈ Q, ∀ y ∈ Y, act q y ∈ Y)
    (ρQ : Q →* GStar)
    (hρQ : ∀ (h : S) (hh : h ∈ sliceGroup lab Y),
      ρQ ⟨h, hHQ hh⟩ = SemidirectProduct.inl (ρ ⟨h, hh⟩)) :
    ∃ r : Fin 4 → rootClass,
      (∀ x : rootClass, ∃! k, x ∈ qRootOrbit Q ρQ (r k)) ∧
      qRootOrbit Q ρQ (r 0) =
        {x : rootClass | ∃ y : Y, ρ ⟨lab y, lab_mem_sliceGroup y.2⟩ = (x : stdGroup)} ∧
      (∀ k, (qRootOrbit Q ρQ (r k)).ncard = (![3510, 142155, 694980, 3127410] : Fin 4 → ℕ) k) ∧
      ∀ k, ∀ x ∈ qRootOrbit Q ρQ (r k),
        {x' : rootClass | x' ∈ {x : rootClass |
            ∃ y : Y, ρ ⟨lab y, lab_mem_sliceGroup y.2⟩ = (x : stdGroup)} ∧
          x' ≠ x ∧ Commute (x' : stdGroup) x}.ncard = (![693, 22, 126, 22] : Fin 4 → ℕ) k := by
  obtain ⟨C, hC, _, x, hx, η, θ, hη, hθ, φ, hφ, α, hα, Φ, hΦ⟩ := hS.exists_cliqueData
  exact hS.root_classes_of_choices hC hx hη hθ hφ hα hΦ hρ hroot Q hHQ hQY ρQ hρQ

end IsFischerSlice

end CFSG.Monster.B.TwoA.Fischer
