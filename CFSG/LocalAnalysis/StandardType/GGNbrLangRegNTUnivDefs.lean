module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangRegNT
public import CFSG.LocalAnalysis.StandardType.GGNbrLangTorARank
public import CFSG.RankThree.PerfectCover.HopfCover

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.RankThree.PerfectCover

@[expose] def KGLangTorusNTUnivCont (p : ℕ) : LargeEvenRawCont := fun R _ I F =>
  ∀ [Finite (HopfCover R)] (θ : HopfCover R ⧸ Subgroup.center (HopfCover R) ≃* R),
    commutator (HopfCover R) = ⊤ →
    ∀ A : Subgroup (MulAut (HopfCover R)), IsElemAbelian p A →
      (∀ α ∈ A, ∃ u ∈ I, ∃ f ∈ Subgroup.closure F, kgInducedAut θ α = u * f) →
      (∃ α ∈ A, α ≠ 1 ∧ kgInducedAut θ α ∈ I) →
      ∀ α₀ ∈ A, kgInducedAut θ α₀ ∉ I → KGLangTorusConcl p θ I A α₀

@[expose] def KGLangTorusNTUnivOn (S : ℕ → LargeEvenLabel → Prop) : Prop :=
  ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → p ≠ 2 → LargeEvenInLambda2 lab → S p lab →
    LargeEvenLabelAll lab (KGLangTorusNTUnivCont p)

end CFSG.StandardType
