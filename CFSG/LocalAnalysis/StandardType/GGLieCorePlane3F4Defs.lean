module

public import CFSG.LocalAnalysis.StandardType.GGLieCorePlane3Defs
public import CFSG.LocalAnalysis.StandardType.GGLieCoreStruct
public import CFSG.Blueprint.Catalog

public section

namespace CFSG.StandardType.LieCore

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.RankThree.PartOne.KE
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.Open (StatedLieTag)

structure GGLieF4PlaneHyp
    {L : Type} [Field L] (D : LangDatum Tag.F4 L)
    (ρ : Equiv.Perm (Fin Tag.F4.rank → ℤ)) (a₁ a₂ : Fin Tag.F4.rank → Lˣ) : Prop where
  frob : FrobRootMap D ρ
  finite : Finite D.model
  hq : ∃ f : ℕ, 1 ≤ f ∧ D.q = 2 ^ f
  mem₁ : rootDiagUnit Tag.F4 a₁ ∈ D.torus
  mem₂ : rootDiagUnit Tag.F4 a₂ ∈ D.torus
  pow₁ : rootDiagUnit Tag.F4 a₁ ^ 3 = 1
  pow₂ : rootDiagUnit Tag.F4 a₂ ^ 3 = 1
  card : Nat.card ↥(Subgroup.closure {rootDiagUnit Tag.F4 a₁, rootDiagUnit Tag.F4 a₂}) = 3 ^ 2

@[expose] def GGLieF4PlaneShape (Ψ : Set (Fin Tag.F4.rank → ℤ)) : Prop :=
  (compRank Ψ = 1 ∧ Ψ.ncard = 2) ∨ (compRank Ψ = 2 ∧ Ψ.ncard = 6) ∨ (compRank Ψ = 2 ∧ Ψ.ncard = 8)

@[expose] noncomputable def GGLieF4PlaneRat
    {L : Type} [Field L] (D : LangDatum Tag.F4 L) (ρ : Equiv.Perm (Fin Tag.F4.rank → ℤ))
    (a₁ a₂ : Fin Tag.F4.rank → Lˣ) (i : KernelComponent (jointChar a₁ a₂)) :
    Subgroup (ModGL Tag.F4 L) :=
  ratComp ρ D.Γ (componentRoots (jointChar a₁ a₂) i)

@[expose] def GGLieSp4Model (G : Type) [Group G] (f : ℕ) : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ f ∧
    Nonempty (G ≃* ↥(CFSG.Open.StatedSp 2 K))

@[expose] def GGLieSL2Model (G : Type) [Group G] (f : ℕ) : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ f ∧
    Nonempty (G ≃* ↥(CFSG.Open.StatedSL 2 K))

@[expose] def GGLieSL3Model (G : Type) [Group G] (f : ℕ) : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ f ∧
    Nonempty (G ≃* ↥(CFSG.Open.StatedSL 3 K))

@[expose] def GGLieSU3Model (G : Type) [Group G] (f : ℕ) : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = (2 ^ f) ^ 2 ∧
    Nonempty (G ≃* ↥(CFSG.Open.StatedSU 3 (2 ^ f) K))

theorem GGLieSp4Model.congr {G H : Type} [Group G] [Group H] (e : G ≃* H) {f : ℕ}
    (hG : GGLieSp4Model G f) : GGLieSp4Model H f := by
  obtain ⟨K, hK, hfin, hc, ⟨e'⟩⟩ := hG
  exact ⟨K, hK, hfin, hc, ⟨e.symm.trans e'⟩⟩

theorem GGLieSL2Model.congr {G H : Type} [Group G] [Group H] (e : G ≃* H) {f : ℕ}
    (hG : GGLieSL2Model G f) : GGLieSL2Model H f := by
  obtain ⟨K, hK, hfin, hc, ⟨e'⟩⟩ := hG
  exact ⟨K, hK, hfin, hc, ⟨e.symm.trans e'⟩⟩

theorem GGLieSL3Model.congr {G H : Type} [Group G] [Group H] (e : G ≃* H) {f : ℕ}
    (hG : GGLieSL3Model G f) : GGLieSL3Model H f := by
  obtain ⟨K, hK, hfin, hc, ⟨e'⟩⟩ := hG
  exact ⟨K, hK, hfin, hc, ⟨e.symm.trans e'⟩⟩

theorem GGLieSU3Model.congr {G H : Type} [Group G] [Group H] (e : G ≃* H) {f : ℕ}
    (hG : GGLieSU3Model G f) : GGLieSU3Model H f := by
  obtain ⟨K, hK, hfin, hc, ⟨e'⟩⟩ := hG
  exact ⟨K, hK, hfin, hc, ⟨e.symm.trans e'⟩⟩

end CFSG.StandardType.LieCore
