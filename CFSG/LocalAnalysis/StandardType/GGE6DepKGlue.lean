module

public import CFSG.LocalAnalysis.StandardType.GGE6DepKGlueMain
public import CFSG.LocalAnalysis.StandardType.GGE6DepKClass

public section

namespace CFSG.StandardType

namespace E6Dep

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {G : Type} [Group G]

theorem ggE6Dep_glueK {Bs K : Subgroup G} {y : G} (hyBs : y ∈ Bs) (hy1 : y ≠ 1)
    (hy3 : y ^ 3 = 1) (hcardBs : Nat.card Bs = 3 ^ 6)
    (hKy : K ≤ Subgroup.centralizer ({y} : Set G))
    {ι : Additive ↥Bs ≃+ Vec6} {c : ZMod 3}
    (hyι : ι (Additive.ofMul ⟨y, hyBs⟩) = xs + c • xx)
    {κ : Additive ↥Bs →+ Vec6} (hκ : GGE6DepKFrame Bs K y κ)
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] {b : Λ} {ρ : Λ → MulAut ↥Bs} {ρa : MulAut ↥Bs}
    (hρrefl : ∀ l, GGIsReflection 3 (ρ l)) (hρa : GGIsReflection 3 ρa)
    (hKgen : ggAutomizer K Bs =
      Subgroup.closure (Set.range (fun l : {l : Λ // l ≠ b} => ρ l) ∪ {ρa}))
    {g : Λ → Mat6} (hg : ∀ l, g l ∈ refl36 ∧ ActsAs ι (ρ l) (g l))
    (hgfix : ∀ l, l ≠ b → g l ∈ reflFix xs)
    (hS : ∀ i : Fin 5, ∃ φ ∈ Subgroup.closure (Set.range fun l : {l : Λ // l ≠ b} => ρ l),
      ActsAs ι φ (gS i)) :
    ∃ s t u w : ZMod 3, s * u + t * w = 2 ∧ w ≠ 0 ∧ u + w * c = 0 ∧
      ∃ φ ∈ ggAutomizer K Bs, ActsAs ι φ (gensAll s t u w 6) := by
  obtain ⟨Ma, h, hMa, hMah, hn, hgen⟩ :=
    ggE6Dep_glueK_gen hyBs hy1 hy3 hcardBs hKy hyι hκ hρrefl hρa hKgen hg hgfix hS
  obtain ⟨sw, s, t, u, w, h1, h2, h3, h4⟩ := kclass hn hgen
  have hSK : ∀ i : Fin 5, ∃ φ ∈ ggAutomizer K Bs, ActsAs ι φ (gS i) := by
    intro i
    obtain ⟨φ, hφ, hact⟩ := hS i
    refine ⟨φ, ?_, hact⟩
    rw [hKgen]
    exact Subgroup.closure_mono Set.subset_union_left hφ
  obtain ⟨φ₁, hφ₁, hact₁⟩ := realize_word hSK sw
  obtain ⟨φ₂, hφ₂, hact₂⟩ := realize_word hSK sw.reverse
  have hρaK : ρa ∈ ggAutomizer K Bs := by
    rw [hKgen]
    exact Subgroup.subset_closure (Or.inr rfl)
  refine ⟨s, t, u, w, h1, h2, h3, φ₁ * ρa * φ₂, ?_, ?_⟩
  · exact (ggAutomizer K Bs).mul_mem ((ggAutomizer K Bs).mul_mem hφ₁ hρaK) hφ₂
  · have hact := (hact₁.mul hMa).mul hact₂
    rw [hMah, h4] at hact
    exact hact

end E6Dep

end CFSG.StandardType

end
