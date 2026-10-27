module

public import CFSG.RankThree.PartOne.N1322.Pure
public import CFSG.RankThree.PartOne.N1322.CaseGL32

public section

namespace CFSG.RankThree.PartOne.N1322

open scoped Matrix
open CFSG.RepresentationTheory
open CFSG.RankThree.SubgroupLists (omegaGL)

theorem case2_false (hΩ : KF1322OmegaList) {p : ℕ} [Fact p.Prime] {d : CoreData (ZMod p)}
    (h : CoreHyp d) {H : Subgroup (GL (Fin 3) (ZMod p))} (hHX : H ≤ d.X)
    (hnorm : ∀ g ∈ d.X, ∀ x ∈ H, g * x * g⁻¹ ∈ H) (hirr : IsIrreducibleMatrixRep H.subtype)
    (M : Matrix (Fin 3) (Fin 3) (ZMod p)) (hM : Mᵀ = M) (hdet : M.det ≠ 0) (hH : H = omegaGL M) :
    False := by
  rcases hΩ p h.p5 d.X d.D h.refl h.gen h.Dconj h.kO H hHX hnorm hirr M hM hdet hH with
    hord | hne
  · obtain ⟨ρ, t₀, hg, ht₀D, hs₀D⟩ := exists_refl_pair h
    have h1 := hord _ ht₀D _ hs₀D
    have hprod : (t₀ : GL (Fin 3) (ZMod p)) * ((t₀ * ρ : d.Lm) : GL (Fin 3) (ZMod p)) =
        (ρ : GL (Fin 3) (ZMod p)) := by
      have := congrArg Subtype.val (show t₀ * (t₀ * ρ) = ρ by rw [← mul_assoc, hg.sq, one_mul])
      simpa using this
    rw [hprod, Subgroup.orderOf_coe, hg.ord] at h1
    have h4 := hg.four
    omega
  · obtain ⟨e⟩ := hne
    exact case4_false h hHX hnorm hirr e

end CFSG.RankThree.PartOne.N1322
