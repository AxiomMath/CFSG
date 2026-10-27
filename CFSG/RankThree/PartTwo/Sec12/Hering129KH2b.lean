module

public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.RankThree.PartTwo.Sec4.Statements

public section

namespace CFSG.RankThree.PartTwo.Sec12

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU projImage)

namespace Hering129KH2b

@[expose] noncomputable def galoisFieldZeroAlgEquiv (p : ℕ) [Fact p.Prime] :
    GaloisField p 0 ≃ₐ[ZMod p] ZMod p := by
  have hf : (Polynomial.X ^ p ^ 0 - Polynomial.X : Polynomial (ZMod p)) = 0 := by simp
  have hsplit : Polynomial.IsSplittingField (ZMod p) (GaloisField p 0)
      (Polynomial.X ^ p ^ 0 - Polynomial.X : Polynomial (ZMod p)) :=
    inferInstanceAs (Polynomial.IsSplittingField (ZMod p)
      (Polynomial.SplittingField (Polynomial.X ^ p ^ 0 - Polynomial.X : Polynomial (ZMod p))) _)
  have hS := hsplit.adjoin_rootSet
  rw [hf, Polynomial.rootSet_zero, Algebra.adjoin_empty] at hS
  exact (AlgEquiv.ofBijective (Algebra.ofId (ZMod p) (GaloisField p 0))
    (Algebra.bijective_algebraMap_iff.2 hS.symm)).symm

@[expose] noncomputable def galoisFieldZeroRingEquiv (p : ℕ) [Fact p.Prime] :
    GaloisField p 0 ≃+* GaloisField p 1 :=
  ((galoisFieldZeroAlgEquiv p).trans (GaloisField.equivZmodP p).symm).toRingEquiv

@[expose] noncomputable def projSLFieldEquiv {K L : Type} [Field K] [Field L] (e : K ≃+* L) :
    projSL 3 K ≃* projSL 3 L :=
  (CFSG.PGLModel.projSLEquivStatedProj 3 K).trans
    ((CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 K).symm.trans
      ((CFSG.Adapters.RankTwoModelTransports.projectiveSpecialLinearGroupCongr (Fin 3) e).trans
        ((CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 L).trans
          (CFSG.PGLModel.projSLEquivStatedProj 3 L).symm)))

theorem isoLThreePi_zero {X : Type} [Group X] {p : ℕ} [Fact p.Prime]
    (h : Sec4.IsoLThreePi X p 0) (hp : p % 3 = 1) : Sec4.IsoLThreePi X p 1 := by
  unfold Sec4.IsoLThreePi at h ⊢
  rcases h with ⟨-, ⟨φ⟩⟩ | ⟨h2, -⟩
  · exact Or.inl ⟨by simpa using hp, ⟨φ.trans (projSLFieldEquiv (galoisFieldZeroRingEquiv p))⟩⟩
  · norm_num at h2

end Hering129KH2b

end CFSG.RankThree.PartTwo.Sec12
