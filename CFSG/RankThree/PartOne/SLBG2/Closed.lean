module

public import CFSG.LieType.Steinberg.CentralExt.G2Multiplier

public section

namespace CFSG.RankThree.PartOne.SLBG2

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.CentralExt.AdjointClosed


theorem g2_ker_eq_bot {K : Type} [Field K] [Finite K] (hK : 5 ≤ Nat.card K) {Y : Type} [Group Y]
    (φ : Y →* adjointGroup .G2 K) (hφ : Function.Surjective φ) (hcen : φ.ker ≤ Subgroup.center Y)
    (hmin : ∀ M : Subgroup Y, M.map φ = ⊤ → M = ⊤) : φ.ker = ⊥ := by
  obtain ⟨σ, hσ⟩ := g2_exists_section_of_central hK hφ hcen
  have hrange : σ.range = ⊤ := by
    apply hmin
    rw [eq_top_iff]
    intro g _
    exact ⟨σ g, ⟨g, rfl⟩, hσ g⟩
  rw [eq_bot_iff]
  intro y hy
  have hy' : y ∈ σ.range := hrange ▸ Subgroup.mem_top y
  obtain ⟨g, rfl⟩ := hy'
  have hg : g = 1 := by
    have h1 : φ (σ g) = 1 := MonoidHom.mem_ker.mp hy
    rw [hσ g] at h1
    exact h1
  rw [hg, map_one]
  exact Subgroup.one_mem _

end CFSG.RankThree.PartOne.SLBG2
