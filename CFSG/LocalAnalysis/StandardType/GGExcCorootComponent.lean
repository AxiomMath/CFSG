module

public import CFSG.LocalAnalysis.StandardType.GGExcStdFormLemmas
public import CFSG.LocalAnalysis.StandardType.GGLatCoroot

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank

section Component

theorem exists_component_of_coroot (hcoroot : GGLatCorootExc) {G : Type} [Group G]
    (τ : StatedLieTag) (f : ℕ) (hτ : GGExcFive τ) (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (Bs G₀ : Subgroup G)
    (S : Matrix (Fin (ggU (absTag τ) 6 f).D.rank) (Fin (ggU (absTag τ) 6 f).D.rank) ℤ)
    (π : Equiv.Perm (Fin (ggU (absTag τ) 6 f).D.rank))
    (hS : IsRootGram (ggU (absTag τ) 6 f).D S) (hπ : IsDiagAut (ggU (absTag τ) 6 f).D π)
    (F : GGStdForm p Bs G₀ (ggU (absTag τ) 6 f).D S π f)
    (α : Fin (ggU (absTag τ) 6 f).D.rank → ℤ) (hα : α ∈ (ggU (absTag τ) 6 f).D.roots)
    (hαπ : latPerm π α = α) (k : ZMod p) (hk : k ≠ 0) (b : Bs)
    (hb : Multiplicative.toAdd (F.coord b) = k • corootCoord p S α) :
    b ≠ 1 ∧ ∃ L₂ : Subgroup G, IsComponentOf L₂ (G₀ ⊓ Subgroup.centralizer {(b : G)}) ∧
      Nat.card (Bs ⊓ Subgroup.centralizer (L₂ : Set G) : Subgroup G) ≤ p ^ 2 := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨hspan, hfix, hne, hO⟩ := hcoroot τ f hτ S π hS hπ p hp hp2 α hα hαπ
  have hb1 : b ≠ 1 := by
    intro hb_eq
    have hzero : k • corootCoord p S α = 0 := by
      rw [← hb, hb_eq, map_one]
      simp
    rcases smul_eq_zero.mp hzero with hk0 | hv0
    · exact hk hk0
    · exact hne hv0
  obtain ⟨O, hOrb, hnsolv, hcard⟩ := hO (f = 1)
  have hOrb' : IsCompOrbit S π (latPhi (ggU (absTag τ) 6 f).D.roots p
      (Multiplicative.toAdd (F.coord b))) O := by
    rw [hb, latPhi_smul (ggU (absTag τ) 6 f).D.roots p k hk]
    exact hOrb
  obtain ⟨L₂, hL₂, hL⟩ := F.comp_ex b hb1 O hOrb' hnsolv
  exact ⟨hb1, ⟨L₂, hL₂, F.card_inf_centralizer_le hp L₂ O hL hcard⟩⟩

end Component

end CFSG.StandardType
