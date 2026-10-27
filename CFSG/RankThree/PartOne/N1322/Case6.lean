module

public import CFSG.RankThree.PartOne.N1322.CaseCyclic
public import CFSG.RankThree.PartOne.N1322.CasePair

public section

namespace CFSG.RankThree.PartOne.N1322

open CFSG.RepresentationTheory

theorem case6_false {p : ℕ} [Fact p.Prime] {d : CoreData (ZMod p)} (h : CoreHyp d)
    {H : Subgroup (GL (Fin 3) (ZMod p))} (hnorm : ∀ g ∈ d.X, ∀ x ∈ H, g * x * g⁻¹ ∈ H)
    (hirr : IsIrreducibleMatrixRep H.subtype) (hcyc : IsCyclic H) : False := by
  obtain ⟨ρ, t₀, hg, ht₀D, -⟩ := exists_refl_pair h
  exact no_refl_normalizing_cyclic (four_ne_zero_of_five_le h.p5) hirr hcyc (h.refl _ ht₀D)
    (fun x hx => hnorm _ (mem_X_of_mem_D h ht₀D) x hx)

end CFSG.RankThree.PartOne.N1322
