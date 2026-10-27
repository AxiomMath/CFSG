module

public import CFSG.RankThree.GF2n.Smith81.S81VGeomE3
public import CFSG.RankThree.GF2n.Smith81.S81VGeomE4

public section

namespace CFSG.RankThree.GF2n.Smith81.S81V

open CFSG.ClassicalGroups.Unitary CFSG.RankThree.GF2n.Smith81.U6Cube Module

variable {F : Type} [Field F] {σ : F ≃+* F}

theorem lemmaE [Finite F] [CharP F 2] (hσ : IsUnitaryInvolution σ) (hq : 3 ≤ Nat.card (Fσ σ))
    {S : Set (Fin 6 → F)} (hS : ClosedPts σ S) {P4 P3 P2 : Submodule F (Fin 6 → F)}
    (h4 : finrank F P4 = 4) (h3 : finrank F P3 = 3) (h2 : finrank F P2 = 2) (h32 : P3 ≤ P4)
    (hn4 : NonDeg σ P4) (hn3 : NonDeg σ P3) (hn2 : NonDeg σ P2) {p₄ : Fin 6 → F} (hp4S : p₄ ∈ S)
    (hp4P : p₄ ∈ P4) (hp4P3 : p₄ ∉ P3) (hperp : P3 ⊓ orth σ (Submodule.span F {p₄}) = P2)
    (hE0 : ∀ z ∈ P3, z ≠ 0 → herm σ z z = 0 → z ∈ S) :
    ∀ z ∈ P4, z ≠ 0 → herm σ z z = 0 → z ∈ S := by
  have hp40 : p₄ ≠ 0 := (hS.iso p₄ hp4S).1
  have hp4i : herm σ p₄ p₄ = 0 := (hS.iso p₄ hp4S).2
  have hI : ∀ p'' ∈ P4, p'' ≠ 0 → herm σ p'' p'' = 0 → herm σ p'' p₄ ≠ 0 → p'' ∈ S := by
    intro p'' hp''P4 hp''0 hp''i hp''j
    by_cases hp''P3 : p'' ∈ P3
    · exact hE0 p'' hp''P3 hp''0 hp''i
    · exact lemmaE_caseI hσ hq hS h4 h3 h2 h32 hn3 hn2 hp4S hp4P hp4P3 hperp hE0
        hp''P4 hp''0 hp''i hp''P3 hp''j
  intro z hzP4 hz0 hzi
  by_cases hzP3 : z ∈ P3
  · exact hE0 z hzP3 hz0 hzi
  by_cases hzj : herm σ z p₄ = 0
  · exact lemmaE_caseII hσ hS h4 hn4 hp4P hp40 hp4i hI hzP4 hz0 hzi
      (herm_eq_zero_comm σ hσ.invol hzj)
  · exact hI z hzP4 hz0 hzi hzj

end CFSG.RankThree.GF2n.Smith81.S81V
