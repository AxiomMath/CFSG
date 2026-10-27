module

public import CFSG.LocalAnalysis.StandardType.GGExcKGToralFrame

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank

section Count

@[expose] noncomputable def GGFixCard (p : ℕ) {R : ℕ} (π : Equiv.Perm (Fin R)) : ℕ :=
  Nat.card {z : Fin R → ZMod p // ∀ i, z (π i) = z i}

end Count

abbrev GGAutU
    (t : StatedLieTag) (n f : ℕ) : Type :=
  MulAut ((ggU t n f).K ⧸ Subgroup.center (ggU t n f).K)

@[expose] noncomputable def ggPsiU
    (t : StatedLieTag) (n f : ℕ) : (ggU t n f).K →* GGAutU t n f :=
  (MulAut.conj : ((ggU t n f).K ⧸ Subgroup.center (ggU t n f).K) →* _).comp
    (QuotientGroup.mk' _)

@[expose] def GGKnownAdm
    (t : StatedLieTag) (n f : ℕ) : Prop :=
  StatedLieAdmissible t n 2 f ∧ 2 ≤ (ggU t n f).D.rank

@[expose] def GGInnDiagU
    (t : StatedLieTag) (n f : ℕ) (κ : GGAutU t n f) : Prop :=
  GGPsiInnerDiag (ggU t n f).D (ggPsiU t n f) κ

@[expose] def GGPiCond
    (t : StatedLieTag) (p f : ℕ)
    (π : Equiv.Perm (Fin (ggU (absTag t) 6 f).D.rank)) : Prop :=
  IsDiagAut (ggU (absTag t) 6 f).D π ∧ (t = .F4 ∨ t = .E7 ∨ t = .E8 → π = 1) ∧
    (t = .E6 → (π = 1 ↔ p ∣ 2 ^ f - 1)) ∧ (t = .twistedE6 → (π = 1 ↔ p ∣ 2 ^ f + 1))

@[expose] def GGKGInndiagCI
    : Prop :=
  ∀ (t : StatedLieTag) (n f : ℕ), GGExcFive t → GGKnownAdm t n f → ∀ p : ℕ, p.Prime → p ≠ 2 →
    GGExcRegime p f → ∀ π : Equiv.Perm (Fin (ggU (absTag t) 6 f).D.rank), GGPiCond t p f π →
    (∀ E : Subgroup (GGAutU t n f), IsElemAbelian p E → (∀ b ∈ E, GGInnDiagU t n f b) →
        Nat.card E ≤ GGFixCard p π) ∧
    ((t = .E6 ∨ t = .twistedE6) → p = 3 → π = 1 →
      ∀ E E' : Subgroup (GGAutU t n f), IsElemAbelian p E → IsElemAbelian p E' →
        (∀ b ∈ E, GGInnDiagU t n f b) → (∀ b ∈ E', GGInnDiagU t n f b) →
        Nat.card E = GGFixCard p π → Nat.card E' = GGFixCard p π →
        ∃ κ : GGAutU t n f, GGInnDiagU t n f κ ∧ E.map (MulAut.conj κ).toMonoidHom = E')

section Clauses

variable {G : Type} [Group G]

@[expose] def GGClauseRF
    (t : StatedLieTag) (n f p : ℕ) (ψ : (ggU t n f).K →* G) (Bs : Subgroup G)
    (π : Equiv.Perm (Fin (ggU (absTag t) 6 f).D.rank))
    (coord : Bs →* Multiplicative (Fin (ggU (absTag t) 6 f).D.rank → ZMod p)) : Prop :=
  ∀ α ∈ (ggU (absTag t) 6 f).D.roots, latPerm π α = α →
    ∃ (δ : Fin (ggU t n f).D.rank → ℤ) (u : (ggU t n f).K), GGRootClass (ggU t n f).D t δ ∧
      Bs ≤ Subgroup.normalizer
        (((ggRankOneSub (ggU t n f).D ψ δ).map (MulAut.conj (ψ u)).toMonoidHom : Subgroup G) :
          Set G) ∧
      ∀ b : Bs, (b : G) ∈ Subgroup.centralizer
          (((ggRankOneSub (ggU t n f).D ψ δ).map (MulAut.conj (ψ u)).toMonoidHom : Subgroup G) :
            Set G) ↔
        latChar p (Multiplicative.toAdd (coord b)) α = 0

@[expose] def GGClauseF5
    (t : StatedLieTag) (n f p : ℕ) (ψ : (ggU t n f).K →* G) (Bs : Subgroup G)
    (S : Matrix (Fin (ggU (absTag t) 6 f).D.rank) (Fin (ggU (absTag t) 6 f).D.rank) ℤ)
    (π : Equiv.Perm (Fin (ggU (absTag t) 6 f).D.rank))
    (coord : Bs →* Multiplicative (Fin (ggU (absTag t) 6 f).D.rank → ZMod p)) : Prop :=
  ∀ α ∈ (ggU t n f).D.roots, GGRootClass (ggU t n f).D t α →
    (∃ x' ∈ ggRankOneSub (ggU t n f).D ψ α, orderOf x' = p) ∧
    ∀ x' ∈ ggRankOneSub (ggU t n f).D ψ α, orderOf x' = p →
      ∃ h ∈ ψ.range, ∃ αB ∈ (ggU (absTag t) 6 f).D.roots, latPerm π αB = αB ∧
        ∃ k : ZMod p, k ≠ 0 ∧ ∃ b : Bs, (b : G) = h * x' * h⁻¹ ∧
          Multiplicative.toAdd (coord b) = k • corootCoord p S αB

@[expose] def GGClauseW
    (t : StatedLieTag) (n f p : ℕ) (ψ : (ggU t n f).K →* G) (Bs : Subgroup G)
    (π : Equiv.Perm (Fin (ggU (absTag t) 6 f).D.rank))
    (coord : Bs →* Multiplicative (Fin (ggU (absTag t) 6 f).D.rank → ZMod p)) : Prop :=
  ∀ u : GGWeyl (ggU (absTag t) 6 f).D,
    (∀ α, weylAction (ggU (absTag t) 6 f).D.isFiniteType u (latPerm π α) =
      latPerm π (weylAction (ggU (absTag t) 6 f).D.isFiniteType u α)) →
    ∃ m ∈ ψ.range ⊓ Subgroup.normalizer (Bs : Set G), ∀ b b' : Bs, (b' : G) = m * b * m⁻¹ →
      ∀ i, Multiplicative.toAdd (coord b') i = latChar p (Multiplicative.toAdd (coord b))
        (weylAction (ggU (absTag t) 6 f).D.isFiniteType u⁻¹ (Pi.single i 1))

@[expose] def GGClauseComp
    (t : StatedLieTag) (n f p : ℕ) (ψ : (ggU t n f).K →* G)
    (Bs : Subgroup G)
    (S : Matrix (Fin (ggU (absTag t) 6 f).D.rank) (Fin (ggU (absTag t) 6 f).D.rank) ℤ)
    (π : Equiv.Perm (Fin (ggU (absTag t) 6 f).D.rank))
    (coord : Bs →* Multiplicative (Fin (ggU (absTag t) 6 f).D.rank → ZMod p)) : Prop :=
  (∀ b : Bs, b ≠ 1 → ∀ O,
    IsCompOrbit S π (latPhi (ggU (absTag t) 6 f).D.roots p (Multiplicative.toAdd (coord b))) O →
    ¬ LatSolv (f = 1) π O → ∃ L : Subgroup G,
      IsComponentOf L (ψ.range ⊓ Subgroup.centralizer {(b : G)}) ∧
      ∀ b' : Bs, (b' : G) ∈ Subgroup.centralizer (L : Set G) ↔
        ∀ α ∈ O, latChar p (Multiplicative.toAdd (coord b')) α = 0) ∧
  (∀ b : Bs, b ≠ 1 → ∀ L : Subgroup G,
    IsComponentOf L (ψ.range ⊓ Subgroup.centralizer {(b : G)}) →
      ∃ O, IsCompOrbit S π
          (latPhi (ggU (absTag t) 6 f).D.roots p (Multiplicative.toAdd (coord b))) O ∧
        ¬ LatSolv (f = 1) π O ∧
        (∀ b' : Bs, (b' : G) ∈ Subgroup.centralizer (L : Set G) ↔
          ∀ α ∈ O, latChar p (Multiplicative.toAdd (coord b')) α = 0) ∧
        Bs ≤ Subgroup.normalizer (L : Set G) ∧
        (∀ α ∈ O, latPerm π α = α → ∀ b' : Bs,
          Multiplicative.toAdd (coord b') = corootCoord p S α → (b' : G) ∈ L) ∧
        (IsSingleComp S (latPhi (ggU (absTag t) 6 f).D.roots p (Multiplicative.toAdd (coord b))) O ∨
          ∃ k : ℕ, LieModel (↥L ⧸ Subgroup.center ↥L) .PSL k 2 (2 * f)))

@[expose] def GGClauseA
    (t : StatedLieTag) (n f p : ℕ) (ψ : (ggU t n f).K →* G) (Bs : Subgroup G)
    (S : Matrix (Fin (ggU (absTag t) 6 f).D.rank) (Fin (ggU (absTag t) 6 f).D.rank) ℤ)
    (π : Equiv.Perm (Fin (ggU (absTag t) 6 f).D.rank))
    (coord : Bs →* Multiplicative (Fin (ggU (absTag t) 6 f).D.rank → ZMod p)) : Prop :=
  ∀ b : Bs, b ≠ 1 → ∀ L : Subgroup G,
    IsComponentOf L (ψ.range ⊓ Subgroup.centralizer {(b : G)}) →
    ∃ O, IsCompOrbit S π
        (latPhi (ggU (absTag t) 6 f).D.roots p (Multiplicative.toAdd (coord b))) O ∧
      (∀ b' : Bs, (b' : G) ∈ Subgroup.centralizer (L : Set G) ↔
        ∀ α ∈ O, latChar p (Multiplicative.toAdd (coord b')) α = 0) ∧
      ∀ b' : Bs, Multiplicative.toAdd (coord b') ∈ latEigenCoroot p S π O → (b' : G) ∈ L

@[expose] def GGClauseAU
    (t : StatedLieTag) (n f p : ℕ) (ψ : (ggU t n f).K →* G) (Bs : Subgroup G)
    (S : Matrix (Fin (ggU (absTag t) 6 f).D.rank) (Fin (ggU (absTag t) 6 f).D.rank) ℤ)
    (π : Equiv.Perm (Fin (ggU (absTag t) 6 f).D.rank))
    (coord : Bs →* Multiplicative (Fin (ggU (absTag t) 6 f).D.rank → ZMod p)) : Prop :=
  ∀ U : Subgroup G, U ≤ Bs → U ≠ ⊥ → ∀ K : Subgroup G,
    IsComponentOf K (ψ.range ⊓ Subgroup.centralizer (U : Set G)) →
    ∃ O, IsCompOrbit S π {α | α ∈ (ggU (absTag t) 6 f).D.roots ∧
        ∀ u : Bs, (u : G) ∈ U → latChar p (Multiplicative.toAdd (coord u)) α = 0} O ∧
      ∀ b' : Bs, (∀ α ∈ O, latChar p (Multiplicative.toAdd (coord b')) α = 0) →
        (b' : G) ∈ Subgroup.centralizer (K : Set G)

end Clauses

structure GGKGModel
    (t : StatedLieTag) (n f p : ℕ) where
  S : Matrix (Fin (ggU (absTag t) 6 f).D.rank) (Fin (ggU (absTag t) 6 f).D.rank) ℤ
  π : Equiv.Perm (Fin (ggU (absTag t) 6 f).D.rank)
  hS : IsRootGram (ggU (absTag t) 6 f).D S
  hπ : GGPiCond t p f π
  Bfull : Subgroup (GGAutU t n f)
  isElemAbelian : IsElemAbelian p Bfull
  diag : ∀ b ∈ Bfull, GGInnDiagU t n f b
  card_full : Nat.card Bfull = GGFixCard p π
  index_inner : Nat.card Bfull ≤ p * Nat.card ↥(Bfull ⊓ (ggPsiU t n f).range)
  coord : Bfull →* Multiplicative (Fin (ggU (absTag t) 6 f).D.rank → ZMod p)
  coord_inj : Function.Injective coord
  coord_fixed : ∀ b i, Multiplicative.toAdd (coord b) (π i) = Multiplicative.toAdd (coord b) i
  coord_surj_inner : ∀ g ∈ LatCorootSpan (ggU (absTag t) 6 f).D p, (∀ i, g (π i) = g i) →
    ∃ b : Bfull, (b : GGAutU t n f) ∈ (ggPsiU t n f).range ∧ Multiplicative.toAdd (coord b) = g
  rf : GGClauseRF t n f p (ggPsiU t n f) Bfull π coord
  f5 : ∀ κ : GGAutU t n f, GGInnDiagU t n f κ →
    ∀ α ∈ (ggU t n f).D.roots, GGRootClass (ggU t n f).D t α →
      (∃ x' ∈ ggRankOneSub (ggU t n f).D (ggPsiU t n f) α, orderOf x' = p) ∧
      ∀ x' ∈ ggRankOneSub (ggU t n f).D (ggPsiU t n f) α, orderOf x' = p →
        ∃ h ∈ (ggPsiU t n f).range, ∃ αB ∈ (ggU (absTag t) 6 f).D.roots, latPerm π αB = αB ∧
          ∃ k : ZMod p, k ≠ 0 ∧ ∃ b : Bfull, (b : GGAutU t n f) ∈ (ggPsiU t n f).range ∧
            κ⁻¹ * (b : GGAutU t n f) * κ = h * x' * h⁻¹ ∧
            Multiplicative.toAdd (coord b) = k • corootCoord p S αB
  w : GGClauseW t n f p (ggPsiU t n f) Bfull π coord

@[expose] def GGModelFamily
    : Type :=
  ∀ (t : StatedLieTag) (n f : ℕ), GGExcFive t → GGKnownAdm t n f → ∀ p : ℕ, p.Prime → p ≠ 2 →
    GGExcRegime p f → GGKGModel t n f p

@[expose] def GGModelComp
    (Mod : GGModelFamily) : Prop :=
  ∀ (t : StatedLieTag) (n f : ℕ) (ht : GGExcFive t) (hadm : GGKnownAdm t n f) (p : ℕ)
    (hp : p.Prime) (hp2 : p ≠ 2) (hreg : GGExcRegime p f),
    GGClauseComp t n f p (ggPsiU t n f) (Mod t n f ht hadm p hp hp2 hreg).Bfull
      (Mod t n f ht hadm p hp hp2 hreg).S (Mod t n f ht hadm p hp hp2 hreg).π
      (Mod t n f ht hadm p hp hp2 hreg).coord ∧
    GGClauseA t n f p (ggPsiU t n f) (Mod t n f ht hadm p hp hp2 hreg).Bfull
      (Mod t n f ht hadm p hp hp2 hreg).S (Mod t n f ht hadm p hp hp2 hreg).π
      (Mod t n f ht hadm p hp hp2 hreg).coord ∧
    GGClauseAU t n f p (ggPsiU t n f) (Mod t n f ht hadm p hp hp2 hreg).Bfull
      (Mod t n f ht hadm p hp hp2 hreg).S (Mod t n f ht hadm p hp hp2 hreg).π
      (Mod t n f ht hadm p hp hp2 hreg).coord

@[expose] def GGModelCompInput
    : Prop := ∃ Mod : GGModelFamily, GGModelComp Mod

end CFSG.StandardType
