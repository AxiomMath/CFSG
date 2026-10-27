module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenTwentyThree

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem sixteen_nine_of_bounds (D : Data G) {V₀ V : Subgroup G} (h : Hyp125 D V₀ V)
    (hr : ((D.k + mSub V₀ : ℕ) : ℕ∞) < rMV D.M V)
    (hγ : ((D.k + mSub V₀ : ℕ) : ℕ∞) < gammaN D.k D.M V) :
    (V₀ ≤ centralizer (E3.wClos V D.k D.T : Set G) ∧
      ∀ v ∈ V, (∀ w ∈ E3.wClos V D.k D.T, ⁅v, w⁆ ∈ V₀) →
        v ∈ centralizer (E3.wClos V D.k D.T : Set G)) ∧
    ∀ B ∈ E3.gammaSet V D.k D.T, V₀ ≤ centralizer (B : Set G) ∧
      ∀ v ∈ V, (∀ b ∈ B, ⁅v, b⁆ ∈ V₀) → v ∈ centralizer (B : Set G) := by
  have h62 : Hyp62 D.M V₀ V := h.hyp62
  refine ⟨six_three h62 D.sylowM.le hr hγ, fun B hB => ?_⟩
  obtain ⟨hBT, g, hBg, hBm⟩ := hB
  have hD : B ≤ conjSubgroup V g ⊓ D.M := le_inf hBg (hBT.trans D.sylowM.le)
  have hcomm : ⁅preCTilde V₀ V B h62.isElemAbelian, B⁆ = ⊥ :=
    six_two_two h62 hD (by rwa [hBm]) (Or.inr (by rwa [hBm]))
  have hmem : ∀ {u : G}, u ∈ V →
      (u ∈ preCTilde V₀ V B h62.isElemAbelian ↔ ∀ b ∈ B, ⁅u, b⁆ ∈ V₀) := fun hu =>
    mem_preCTilde_iff h62.isElemAbelian (h62.le_stabTil hD) hu
  have hUC : preCTilde V₀ V B h62.isElemAbelian ≤ centralizer (B : Set G) := fun u hu =>
    Subgroup.mem_centralizer_iff.2 fun b hb => by
      have h1 : ⁅u, b⁆ = 1 := by
        have := Subgroup.commutator_le.1 hcomm.le u hu b hb
        simpa using this
      exact (commutatorElement_eq_one_iff_mul_comm.1 h1).symm
  exact ⟨fun v hv => hUC (le_preCTilde h62.isElemAbelian h62.le hv),
    fun v hvV hv => hUC ((hmem hvV).2 hv)⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
