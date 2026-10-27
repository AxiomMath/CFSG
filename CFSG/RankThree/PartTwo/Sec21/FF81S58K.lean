module

public import CFSG.RankThree.PartTwo.Sec21.RudvalisFF81Sp6RefS
import CFSG.RankThree.PartTwo.Sec21.HeringFFLSp6Facts

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81.S58

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF79
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two (H6)
open CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII (zH)

theorem exists_conj_of_monomial_bases
    {X : Type} [Group X]
    [Finite X] {M : Subgroup X} (hM : StatedClassicalModel M .PSp 3 2 1) {a₁ a₂ a₃ c₁ c₂ c₃ : X}
    (ha₁ : a₁ ∈ M) (ha₂ : a₂ ∈ M) (ha₃ : a₃ ∈ M) (hc₁ : c₁ ∈ M) (hc₂ : c₂ ∈ M) (hc₃ : c₃ ∈ M)
    (hEa : IsElemAb 3 3 (Subgroup.closure {a₁, a₂, a₃}))
    (hEc : IsElemAb 3 3 (Subgroup.closure {c₁, c₂, c₃}))
    (hma : ∀ n ∈ M, n ∈ Nor (Subgroup.closure {a₁, a₂, a₃}) → ∀ x ∈ ({a₁, a₂, a₃} : Set X),
      n * x * n⁻¹ ∈ ({a₁, a₁⁻¹, a₂, a₂⁻¹, a₃, a₃⁻¹} : Set X))
    (hmc : ∀ n ∈ M, n ∈ Nor (Subgroup.closure {c₁, c₂, c₃}) → ∀ x ∈ ({c₁, c₂, c₃} : Set X),
      n * x * n⁻¹ ∈ ({c₁, c₁⁻¹, c₂, c₂⁻¹, c₃, c₃⁻¹} : Set X)) :
    ∃ x ∈ M, x * a₁ * x⁻¹ = c₁ ∧ x * a₂ * x⁻¹ = c₂ ∧ x * a₃ * x⁻¹ = c₃ := by
  obtain ⟨f, hf, hfM, hf0, hf1, hf2⟩ := Sp6RefS.exists_hom_std hM ha₁ ha₂ ha₃ hEa hma
  obtain ⟨g, hg, hgM, hg0, hg1, hg2⟩ := Sp6RefS.exists_hom_std hM hc₁ hc₂ hc₃ hEc hmc
  have hfmem : ∀ x, f x ∈ M := fun x => hfM ▸ Subgroup.mem_map_of_mem f (Subgroup.mem_top x)
  have hgmem : ∀ x, g x ∈ M := fun x => hgM ▸ Subgroup.mem_map_of_mem g (Subgroup.mem_top x)
  have hsf : ∀ y : M, ∃ x, f x = y := fun y => by
    have hy : (y : X) ∈ Subgroup.map f ⊤ := by rw [hfM]; exact y.2
    obtain ⟨x, -, hx⟩ := Subgroup.mem_map.mp hy
    exact ⟨x, hx⟩
  have hsg : ∀ y : M, ∃ x, g x = y := fun y => by
    have hy : (y : X) ∈ Subgroup.map g ⊤ := by rw [hgM]; exact y.2
    obtain ⟨x, -, hx⟩ := Subgroup.mem_map.mp hy
    exact ⟨x, hx⟩
  let ef : H6 ≃* M := MulEquiv.ofBijective (f.codRestrict M hfmem)
    ⟨fun x y h => hf (congrArg Subtype.val h), fun y => by
      obtain ⟨x, hx⟩ := hsf y
      exact ⟨x, Subtype.ext hx⟩⟩
  let eg : H6 ≃* M := MulEquiv.ofBijective (g.codRestrict M hgmem)
    ⟨fun x y h => hg (congrArg Subtype.val h), fun y => by
      obtain ⟨x, hx⟩ := hsg y
      exact ⟨x, Subtype.ext hx⟩⟩
  have hef : ∀ x, ((ef x : M) : X) = f x := fun x => rfl
  have heg : ∀ x, ((eg x : M) : X) = g x := fun x => rfl
  let α : MulAut M := ef.symm.trans eg
  have hα : ∀ (i : Fin 3) (a c : X) (ha : a ∈ M) (hc : c ∈ M), f (zH i) = a → g (zH i) = c →
      ((α ⟨a, ha⟩ : M) : X) = c := by
    intro i a c ha hc hfa hgc
    have h1 : ef.symm ⟨a, ha⟩ = zH i := by
      rw [MulEquiv.symm_apply_eq]
      exact Subtype.ext (by rw [hef, hfa])
    show ((eg (ef.symm ⟨a, ha⟩) : M) : X) = c
    rw [h1, heg, hgc]
  obtain ⟨y, hy⟩ := exists_eq_conj_of_sp6Model hM α
  have hconj : ∀ (a c : X) (ha : a ∈ M), ((α ⟨a, ha⟩ : M) : X) = c →
      (y : X) * a * (y : X)⁻¹ = c := by
    intro a c ha h
    rw [← h, hy]
    rfl
  exact ⟨y, y.2, hconj _ _ ha₁ (hα 0 a₁ c₁ ha₁ hc₁ hf0 hg0),
    hconj _ _ ha₂ (hα 1 a₂ c₂ ha₂ hc₂ hf1 hg1), hconj _ _ ha₃ (hα 2 a₃ c₃ ha₃ hc₃ hf2 hg2)⟩

end CFSG.RankThree.PartTwo.Sec21.FF81.S58
