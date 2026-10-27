module

public import CFSG.Quasithin.Background.G9StmtsDimensionOnly
public import CFSG.Quasithin.Background.G93ApplyRestrict

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank

namespace G11

namespace G118

variable {U : Type} [AddCommGroup U] [Module (ZMod 2) U]

theorem g118_scan [Finite U] {Γ' H' : Subgroup (GLV U)} {m : ℕ}
    (h : G93ConclDimensionOnly Γ' H' m)
    (hsd : SelfDual H' ⊤) (hle : Module.finrank (ZMod 2) U ≤ m + 2)
    (h3 : 2 < Module.finrank (ZMod 2) U) :
    (Module.finrank (ZMod 2) U = 4 ∧ m = 2 ∧
        IsNaturalMatrixModule H' (StatedSL 2 (GaloisField 2 2)) ∧ EndIsField H' 2) ∨
    (Module.finrank (ZMod 2) U = 4 ∧ m = 2 ∧
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
  · obtain ⟨a, ⟨ha, hd, ha1, ha2, hiso, -⟩, hend, -⟩ := h7
    have ha1' : a = 1 := by omega
    subst ha1'
    exact Or.inr (Or.inl ⟨by omega, by omega, hiso, hend⟩)
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

theorem selfDual_restrictRange_top {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    {H : Subgroup (GLV V)} {I : Submodule (ZMod 2) V} (hHI : Invariant H I)
    (h : SelfDual H I) : SelfDual (restrictRange H I hHI) ⊤ := by
  obtain ⟨f, hnd, hinv⟩ := h
  let e : ↥(⊤ : Submodule (ZMod 2) ↥I) ≃ₗ[ZMod 2] ↥I := Submodule.topEquiv
  refine ⟨LinearMap.BilinForm.congr e.symm f, LinearMap.BilinForm.Nondegenerate.congr e.symm hnd,
    fun g hg i j i' j' hgi hgj => ?_⟩
  obtain ⟨k, hk, hkg⟩ := (mem_restrictRange_iff hHI).1 hg
  rw [LinearMap.BilinForm.congr_apply, LinearMap.BilinForm.congr_apply]
  refine hinv k hk (e i) (e j) (e i') (e j') ?_ ?_
  · have := hkg (e i)
    rw [← this]
    exact congrArg Subtype.val hgi
  · have := hkg (e j)
    rw [← this]
    exact congrArg Subtype.val hgj

end G118

end G11

end CFSG.Quasithin
