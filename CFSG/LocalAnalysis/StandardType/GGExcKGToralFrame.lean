module

public import CFSG.LocalAnalysis.StandardType.GGExcKnownGroups
public import CFSG.LocalAnalysis.StandardType.GGPresentation

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank

section Lat

variable {N : ℕ}

@[expose] def latCorootZ (S : Matrix (Fin N) (Fin N) ℤ) (α : Fin N → ℤ) : Fin N → ℤ :=
  fun i => 2 * latGram S (Pi.single i 1) α / latGram S α α

@[expose] def latEigenCoroot (p : ℕ) (S : Matrix (Fin N) (Fin N) ℤ) (π : Equiv.Perm (Fin N))
    (O : Set (Fin N → ℤ)) : Set (Fin N → ZMod p) :=
  {g | ∃ x ∈ Submodule.span ℤ (latCorootZ S '' O), (∀ i, (x i : ZMod p) = g i) ∧
    ∃ z ∈ Submodule.span ℤ (latCorootZ S '' O), (fun i => x (π.symm i)) - x = (p : ℤ) • z}

end Lat

section Frame

@[expose] def GGExcKGToralFrame : Prop :=
  ∀ (t : StatedLieTag) (n f : ℕ), GGExcFive t → ∀ (G : Type) [Group G] [Finite G]
    (ψ : (ggU t n f).K →* G), GGKnownSetting t n f ψ →
    ∀ p : ℕ, p.Prime → p ≠ 2 → GGExcRegime p f →
    ∀ Bs : Subgroup G, IsElemAbelian p Bs → p ^ 4 ≤ Nat.card Bs →
      Bs ≤ Subgroup.normalizer (ψ.range : Set G) →
      (∀ b ∈ Bs, GGPsiInnerDiag (ggU t n f).D ψ b) →
      (∃ P : Sylow p (Subgroup.normalizer (ψ.range : Set G)),
        Bs ≤ (P : Subgroup (Subgroup.normalizer (ψ.range : Set G))).map
          (Subgroup.normalizer (ψ.range : Set G)).subtype ∧
        ∀ E : Subgroup G, E ≤ (P : Subgroup (Subgroup.normalizer (ψ.range : Set G))).map
          (Subgroup.normalizer (ψ.range : Set G)).subtype →
          IsElemAbelian p E → Nat.card E = Nat.card Bs → E = Bs) →
      ∃ (S : Matrix (Fin (ggU (absTag t) 6 f).D.rank) (Fin (ggU (absTag t) 6 f).D.rank) ℤ)
        (π : Equiv.Perm (Fin (ggU (absTag t) 6 f).D.rank))
        (F : GGStdForm p Bs ψ.range (ggU (absTag t) 6 f).D S π f),
        (IsRootGram (ggU (absTag t) 6 f).D S ∧ IsDiagAut (ggU (absTag t) 6 f).D π ∧
         (t = .F4 ∨ t = .E7 ∨ t = .E8 → π = 1) ∧
         (t = .E6 → (π = 1 ↔ p ∣ 2 ^ f - 1)) ∧
         (t = .twistedE6 → (π = 1 ↔ p ∣ 2 ^ f + 1)) ∧
         (∀ α ∈ (ggU (absTag t) 6 f).D.roots, latPerm π α = α →
           ∃ (γ : Fin (ggU t n f).D.rank → ℤ) (u : (ggU t n f).K),
             GGRootClass (ggU t n f).D t γ ∧
             (∀ b : Bs, latChar p (Multiplicative.toAdd (F.coord b)) α = 0 →
               (b : G) ∈ Subgroup.centralizer (ggRootSub (ggU t n f).D ψ γ u : Set G)) ∧
             ∃ r ∈ ggRootSub (ggU t n f).D ψ γ u, orderOf r = 2) ∧
         (∀ α ∈ (ggU t n f).D.roots, GGRootClass (ggU t n f).D t α →
           (∃ x' ∈ ggRankOneSub (ggU t n f).D ψ α, orderOf x' = p) ∧
           ∀ x' ∈ ggRankOneSub (ggU t n f).D ψ α, orderOf x' = p →
             ∃ h ∈ ψ.range, ∃ αB ∈ (ggU (absTag t) 6 f).D.roots, latPerm π αB = αB ∧
               ∃ k : ZMod p, k ≠ 0 ∧ ∃ b : Bs, (b : G) = h * x' * h⁻¹ ∧
                 Multiplicative.toAdd (F.coord b) = k • corootCoord p S αB)) ∧
        (∀ u : GGWeyl (ggU (absTag t) 6 f).D,
          (∀ α, weylAction (ggU (absTag t) 6 f).D.isFiniteType u (latPerm π α) =
            latPerm π (weylAction (ggU (absTag t) 6 f).D.isFiniteType u α)) →
          ∃ m ∈ ψ.range ⊓ Subgroup.normalizer (Bs : Set G), ∀ b b' : Bs, (b' : G) = m * b * m⁻¹ →
            ∀ i, Multiplicative.toAdd (F.coord b') i = latChar p (Multiplicative.toAdd (F.coord b))
              (weylAction (ggU (absTag t) 6 f).D.isFiniteType u⁻¹ (Pi.single i 1))) ∧
        (∀ b : Bs, b ≠ 1 → ∀ L : Subgroup G,
          IsComponentOf L (ψ.range ⊓ Subgroup.centralizer {(b : G)}) →
          ∃ O, IsCompOrbit S π (latPhi (ggU (absTag t) 6 f).D.roots p
              (Multiplicative.toAdd (F.coord b))) O ∧
            (∀ b' : Bs, (b' : G) ∈ Subgroup.centralizer (L : Set G) ↔
              ∀ α ∈ O, latChar p (Multiplicative.toAdd (F.coord b')) α = 0) ∧
            ∀ b' : Bs, Multiplicative.toAdd (F.coord b') ∈ latEigenCoroot p S π O →
              (b' : G) ∈ L) ∧
        (∀ U : Subgroup G, U ≤ Bs → U ≠ ⊥ → ∀ K : Subgroup G,
          IsComponentOf K (ψ.range ⊓ Subgroup.centralizer (U : Set G)) →
          ∃ O, IsCompOrbit S π {α | α ∈ (ggU (absTag t) 6 f).D.roots ∧
              ∀ u : Bs, (u : G) ∈ U → latChar p (Multiplicative.toAdd (F.coord u)) α = 0} O ∧
            ∀ b' : Bs, (∀ α ∈ O, latChar p (Multiplicative.toAdd (F.coord b')) α = 0) →
              (b' : G) ∈ Subgroup.centralizer (K : Set G))

theorem ggExcKGStdForm_of_toralFrame (h : GGExcKGToralFrame) : GGExcKGStdForm := by
  intro t n f ht G _ _ ψ hset p hp hp2 hreg Bs hBs hcard hN hdiag hP
  obtain ⟨S, π, F, hF, -⟩ := h t n f ht G ψ hset p hp hp2 hreg Bs hBs hcard hN hdiag hP
  exact ⟨S, π, F, hF⟩

end Frame

end CFSG.StandardType
