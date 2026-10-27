module

public import CFSG.RankThree.PartTwo.Sec21.CarterFF81aNoInvert
public import CFSG.GroupTheory.OddCoreCentralizerDecomposition

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81

open CFSG.RankThree.PartTwo.Sec21.FF79
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {b : G} {L : Subgroup G}

theorem FF81Hyp.X_eq_oddCore_mul_centralizer_tau_of_no_conj (h : FF81Hyp b L)
    (hnoL : ∀ g : G, g * b * g⁻¹ ∉ L)
    {τ b₁ b₂ b₃ : G} (hτL : τ ∈ L) (hb₁ : b₁ ∈ L) (hb₂ : b₂ ∈ L) (hb₃ : b₃ ∈ L)
    (hE : IsElemAb 3 3 (Subgroup.closure ({b₁, b₂, b₃} : Set G)))
    (hb₁ne : b₁ ≠ 1)
    (hτ2o : orderOf τ = 2) (hb : τ * b * τ⁻¹ = b)
    (hinv : τ * b₁ * τ⁻¹ = b₁⁻¹ ∧ τ * b₂ * τ⁻¹ = b₂⁻¹ ∧ τ * b₃ * τ⁻¹ = b₃⁻¹)
    (hbB : b ∈ Subgroup.closure ({b, b₁, b₂, b₃} : Set G))
    (hb₁B : b₁ ∈ Subgroup.closure ({b, b₁, b₂, b₃} : Set G))
    (hb₂B : b₂ ∈ Subgroup.closure ({b, b₁, b₂, b₃} : Set G))
    (hb₃B : b₃ ∈ Subgroup.closure ({b, b₁, b₂, b₃} : Set G))
    {τX : MulAut ↥(Subgroup.closure ({b, b₁, b₂, b₃} : Set G))}
    (hτXmem : τX ∈ FF81X (Subgroup.closure ({b, b₁, b₂, b₃} : Set G)))
    (hτX2 : τX * τX = 1)
    (hτXeq : τX = FF81X.tau (FF81Hyp.tau_mem_normalizer h hτL hb₁ hb₂ hb₃ hE hb hinv)) :
    (⊤ : Set ↥(FF81X (Subgroup.closure ({b, b₁, b₂, b₃} : Set G)))) =
      (oddCore ↥(FF81X (Subgroup.closure ({b, b₁, b₂, b₃} : Set G))) : Set _) *
        (Subgroup.centralizer ({⟨τX, hτXmem⟩} :
          Set ↥(FF81X (Subgroup.closure ({b, b₁, b₂, b₃} : Set G)))) : Set _) := by
  let B : Subgroup G := Subgroup.closure ({b, b₁, b₂, b₃} : Set G)
  let X : Subgroup (MulAut ↥B) := FF81X B
  let τX' : ↥X := ⟨τX, hτXmem⟩
  have hτX2' : τX' * τX' = 1 := by
    apply Subtype.ext
    simpa [τX'] using hτX2
  have hτXne : τX ≠ 1 := by
    rw [hτXeq]
    exact FF81Hyp.tauX_ne_one h hτL hb₁ hb₂ hb₃ hE hb₁ne hτ2o hb hinv hbB hb₁B
  have hτX'1 : τX' ≠ 1 := by
    intro h1
    apply hτXne
    have := congrArg (fun x : ↥X => (x : MulAut ↥B)) h1
    simpa [τX'] using this
  have hiso : ∀ g : ↥X, (g * τX' * g⁻¹) * τX' = τX' * (g * τX' * g⁻¹) →
      g * τX' * g⁻¹ = τX' := by
    intro g hg
    let σ : MulAut ↥B := (g : MulAut ↥B)
    have hσX : σ ∈ X := by
      simpa [X, σ] using g.2
    have hcommX : (σ * τX * σ⁻¹) * τX = τX * (σ * τX * σ⁻¹) := by
      have hg' := congrArg (fun x : ↥X => (x : MulAut ↥B)) hg
      simpa [σ, τX'] using hg'
    have hcomm : (σ * FF81X.tau (FF81Hyp.tau_mem_normalizer h hτL hb₁ hb₂ hb₃ hE hb hinv) *
        σ⁻¹) * FF81X.tau (FF81Hyp.tau_mem_normalizer h hτL hb₁ hb₂ hb₃ hE hb hinv) =
        FF81X.tau (FF81Hyp.tau_mem_normalizer h hτL hb₁ hb₂ hb₃ hE hb hinv) *
        (σ * FF81X.tau (FF81Hyp.tau_mem_normalizer h hτL hb₁ hb₂ hb₃ hE hb hinv) * σ⁻¹) := by
      rw [← hτXeq]
      exact hcommX
    have h := FF81Hyp.tau_isolated_of_no_conj_into_L h hnoL hτL hb₁ hb₂ hb₃ hE hb hinv
      hbB hb₁B hb₂B hb₃B (FF81Hyp.tau_mem_normalizer h hτL hb₁ hb₂ hb₃ hE hb hinv)
      (σ := σ) hσX hcomm
    have h' : σ * τX * σ⁻¹ = τX := by
      rw [hτXeq]
      exact h
    apply Subtype.ext
    simpa [σ, τX'] using h'
  exact CFSG.eq_oddCore_mul_centralizer_of_isolated (X := ↥X) (τ := τX')
    hτX'1 hτX2' hiso

end CFSG.RankThree.PartTwo.Sec21.FF81
