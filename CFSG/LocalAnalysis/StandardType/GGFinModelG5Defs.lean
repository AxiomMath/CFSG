module

public import CFSG.LocalAnalysis.StandardType.GGFinModelRootCompat
public import CFSG.LocalAnalysis.StandardType.GGFinModelExists

public section

namespace CFSG.StandardType.GGFinModel.G5

open CFSG.StandardType CFSG.StandardType.GGFinModel CFSG.Open CFSG.Assembly CFSG.Blueprint
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.Assembly.LowTwoRank

section Defs

@[expose] def GGModelF5
    (t : StatedLieTag) (n f p : ℕ) (Bfull : Subgroup (GGAutU t n f))
    (S : Matrix (Fin (ggU (absTag t) 6 f).D.rank) (Fin (ggU (absTag t) 6 f).D.rank) ℤ)
    (π : Equiv.Perm (Fin (ggU (absTag t) 6 f).D.rank))
    (coord : Bfull →* Multiplicative (Fin (ggU (absTag t) 6 f).D.rank → ZMod p)) : Prop :=
  ∀ κ : GGAutU t n f, GGInnDiagU t n f κ →
    ∀ α ∈ (ggU t n f).D.roots, GGRootClass (ggU t n f).D t α →
      (∃ x' ∈ ggRankOneSub (ggU t n f).D (ggPsiU t n f) α, orderOf x' = p) ∧
      ∀ x' ∈ ggRankOneSub (ggU t n f).D (ggPsiU t n f) α, orderOf x' = p →
        ∃ h ∈ (ggPsiU t n f).range, ∃ αB ∈ (ggU (absTag t) 6 f).D.roots, latPerm π αB = αB ∧
          ∃ k : ZMod p, k ≠ 0 ∧ ∃ b : Bfull, (b : GGAutU t n f) ∈ (ggPsiU t n f).range ∧
            κ⁻¹ * (b : GGAutU t n f) * κ = h * x' * h⁻¹ ∧
            Multiplicative.toAdd (coord b) = k • corootCoord p S αB

@[expose] noncomputable def ratSL2 (f : ℕ) : Subgroup (SL2 GGL) :=
  (Matrix.SpecialLinearGroup.map (ggFrobT f)).eqLocus (MonoidHom.id _)

@[expose] noncomputable def ratRankOne
    (t : StatedLieTag) (f : ℕ) (β : Fin (langTag t).rank → ℤ) :
    Subgroup (ModGL (langTag t) GGL) :=
  (ggFixGp t f ⊓ rootSubgroup (langTag t) GGL β) ⊔
    (ggFixGp t f ⊓ rootSubgroup (langTag t) GGL (-β))

@[expose] def GGCommPi
    (t : StatedLieTag) (p f : ℕ) (ht : GGExcFive t)
    (u : WeylGroup (langTag t)) : Prop :=
  ∀ v : Fin (langTag t).rank → ℤ,
    u • permLattice ((finCongr (rank_eq_langTag f ht)).permCongr (piB t p f)) v =
      permLattice ((finCongr (rank_eq_langTag f ht)).permCongr (piB t p f)) (u • v)

structure GGLangFrame
    (t : StatedLieTag) (p f : ℕ) (ht : GGExcFive t) where
  M : GGDatumModel t f p ht
  frame : Set (Fin (ggU (absTag t) 6 f).D.rank → ℤ)
  frame_root : ∀ β ∈ frame, β ∈ (ggU (absTag t) 6 f).D.roots
  frame_fixed : ∀ β ∈ frame, latPerm (piB t p f) β = β
  frame_graph : ∀ β ∈ frame,
    ggGraphLat t (ggLangReidx (rank_eq_langTag f ht) β) = ggLangReidx (rank_eq_langTag f ht) β
  z : SL2 GGL
  act : ∀ β ∈ frame, ∀ A : SL2 GGL,
    M.D.g0 * rootSL2 (langTag t) GGL (ggLangReidx (rank_eq_langTag f ht) β) A * M.D.g0⁻¹ =
      rootSL2 (langTag t) GGL (ggLangReidx (rank_eq_langTag f ht) β) (z * A * z⁻¹)
  cover_rf : ∀ α ∈ (ggU (absTag t) 6 f).D.roots, latPerm (piB t p f) α = α →
    ∃ β ∈ frame, ∃ u : WeylGroup (langTag t), GGCommPi t p f ht u ∧
      u • ggLangReidx (rank_eq_langTag f ht) β = ggLangReidx (rank_eq_langTag f ht) α
  cover_f5 : ∀ β : Fin (langTag t).rank → ℤ, IsRoot (langTag t) β → ggGraphLat t β = β →
    ∃ β₀ ∈ frame, ∃ u : WeylGroup (langTag t),
      ggPhi t f (canonicalRep (coxeterSystem (langTag t)) GGL u) =
        canonicalRep (coxeterSystem (langTag t)) GGL u ∧
      u • ggLangReidx (rank_eq_langTag f ht) β₀ = β

end Defs

end CFSG.StandardType.GGFinModel.G5
