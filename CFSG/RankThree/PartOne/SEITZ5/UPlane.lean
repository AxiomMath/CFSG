module

public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.RankThree.PartOne.SEITZ2.SUnPlane
public import CFSG.RankThree.PartOne.SEITZ5.UDickson

public section

namespace CFSG.RankThree.PartOne.SEITZ5

open Matrix CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary
  CFSG.RankThree.PartOne.SEITZ2
open CFSG.RankThree.PartOne.CTP (u2 l2)

variable {K : Type} [Field K] [Finite K] [CharP K 2]
  {k : Subfield K} {σ : K ≃+* K} {N : ℕ}

theorem hfull_of_plane (hσi : ∀ c, σ (σ c) = c) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card (fixSub σ) = Nat.card (ratFix σ k) ^ p) (hr2 : Nat.card (ratFix σ k) = 2)
    {a₀ b₀ : Fin N → K} (ha : herm σ a₀ a₀ = 0) (hb : herm σ b₀ b₀ = 0)
    (hab : herm σ a₀ b₀ = 1) {M : Subgroup (SUid σ N)} {ν : fixSub σ} (hν : ν ∉ ratFix σ k)
    (h1 : ∃ t ∈ M, IsTv σ t a₀ 1) (hνt : ∃ t ∈ M, IsTv σ t a₀ (ν : K))
    (hl : ∃ t ∈ M, IsTv σ t b₀ 1) : ∀ b : fixSub σ, ∃ t ∈ M, IsTv σ t a₀ (b : K) := by
  set Θ := planeSUN hσi ha hb hab with hΘ
  obtain ⟨t1, ht1M, ht1⟩ := h1
  obtain ⟨tν, htνM, htν⟩ := hνt
  obtain ⟨tl, htlM, htl⟩ := hl
  have hu1 : u2 (1 : fixSub σ) ∈ M.comap Θ := by
    have : Θ (u2 1) = t1 := (isTv_planeSUN_u2 hσi ha hb hab 1).unique ht1
    show Θ (u2 1) ∈ M
    rw [this]
    exact ht1M
  have huν : u2 ν ∈ M.comap Θ := by
    have : Θ (u2 ν) = tν := (isTv_planeSUN_u2 hσi ha hb hab ν).unique htν
    show Θ (u2 ν) ∈ M
    rw [this]
    exact htνM
  have hl1 : l2 (1 : fixSub σ) ∈ M.comap Θ := by
    have : Θ (l2 1) = tl := (isTv_planeSUN_l2 hσi ha hb hab 1).unique htl
    show Θ (l2 1) ∈ M
    rw [this]
    exact htlM
  have htop : M.comap Θ = ⊤ := sl2_top_of_roots hp hp2 hK hr2 hν one_ne_zero hu1 huν hl1
  intro b
  have hb' : u2 b ∈ M.comap Θ := htop ▸ Subgroup.mem_top _
  exact ⟨Θ (u2 b), hb', isTv_planeSUN_u2 hσi ha hb hab b⟩

end CFSG.RankThree.PartOne.SEITZ5
