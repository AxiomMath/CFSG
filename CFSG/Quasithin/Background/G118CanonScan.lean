module

public import CFSG.Quasithin.Background.G9StmtsDimensionOnly

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank

namespace G11

namespace Canon

variable {U : Type} [AddCommGroup U] [Module (ZMod 2) U]

theorem g118_scan_nat [Finite U] {Γ' H' : Subgroup (GLV U)} {m : ℕ}
    (h : G93ConclDimensionOnly Γ' H' m)
    (hsd : SelfDual H' ⊤) (hle : Module.finrank (ZMod 2) U ≤ m + 2)
    (h3 : 2 < Module.finrank (ZMod 2) U) :
    (Module.finrank (ZMod 2) U = 4 ∧ m = 2 ∧
        IsNaturalMatrixModule H' (StatedSL 2 (GaloisField 2 2)) ∧ EndIsField H' 2) ∨
    (Module.finrank (ZMod 2) U = 4 ∧ m = 2 ∧
        (∃ (b c : GaloisField 2 1), (∀ s : GaloisField 2 1, s ^ 2 + b * s + c ≠ 0) ∧
          IsNaturalMatrixModule H' (StatedOmega (StatedQuadMinus 2 (GaloisField 2 1) b c))) ∧
        Nonempty (↥H' ≃* ↥(StatedSL 2 (GaloisField 2 2))) ∧ EndIsField H' 1) ∨
    (Module.finrank (ZMod 2) U = 4 ∧ IsPermCoreModule H' (alternatingGroup (Fin 6)) ∧
        EndIsField H' 1) ∨
    (Module.finrank (ZMod 2) U = 8 ∧ m = 6 ∧
        IsNaturalMatrixModule H' ⁅StatedSp 2 (GaloisField 2 2), StatedSp 2 (GaloisField 2 2)⁆ ∧
        EndIsField H' 2) ∨
    (Module.finrank (ZMod 2) U = 6 ∧ m = 4 ∧ IsPermCoreModule H' (alternatingGroup (Fin 8)) ∧
        EndIsField H' 1) := by
  have h' := G93ConclDimensionOnly.of_selfDual h hsd
  rcases h' with h0 | h2 | h4 | h6 | h7 | h9 | h10 | h12 | h15 | h16
  · obtain ⟨⟨hm, hd, -⟩, -, -⟩ := h0
    omega
  · obtain ⟨⟨hm, hd, -, -⟩, -, -⟩ := h2
    omega
  · obtain ⟨⟨hm, hd, hm3, -⟩, -, -⟩ := h4
    omega
  · obtain ⟨n, ⟨hn, hd, hnm, hmn, hnat⟩, hend, -⟩ := h6
    have hn2 : n = 2 := by omega
    subst hn2
    exact Or.inl ⟨by omega, by omega, hnat, hend⟩
  · obtain ⟨a, ⟨ha, hd, ha1, ha2, hiso, b, c, hbc, hmod⟩, hend, -⟩ := h7
    have ha1' : a = 1 := by omega
    subst ha1'
    exact Or.inr (Or.inl ⟨by omega, by omega, ⟨b, c, hbc, hmod⟩, hiso, hend⟩)
  · obtain ⟨n, ⟨hn, hd, hnm, hmn, hnat, hcore⟩, hend, -⟩ := h9
    have hn2 : n = 1 ∨ n = 2 := by omega
    rcases hn2 with rfl | rfl
    · exact Or.inr (Or.inr (Or.inl ⟨by omega, hcore rfl, hend⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega, hnat, hend⟩)))
  · obtain ⟨n, ⟨hn, hd, hnm, hmn, -⟩, -, -⟩ := h10
    omega
  · obtain ⟨⟨hm, hd, hm4, hperm⟩, hend, -⟩ := h12
    exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hd, by omega, hperm, hend⟩)))
  · obtain ⟨n, ⟨hn, hd, hnm, hmn, -⟩, -, -⟩ := h15
    omega
  · obtain ⟨⟨hm, hd, -⟩, -, -⟩ := h16
    omega

end Canon

end G11

end CFSG.Quasithin
