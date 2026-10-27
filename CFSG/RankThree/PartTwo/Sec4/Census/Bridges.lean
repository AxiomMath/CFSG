module

public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeB2Carrier
import CFSG.Adapters.LinearFieldTransport
import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census

open CFSG.Assembly.LowTwoRank TauCeti
open CFSG.Assembly.RankThreeEven (projSp localRank)
open CFSG.Adapters.RankTwoModelTransports (glCongr glCongr_statedScalars statedProjCongr
  statedProjEquivMapMk)

noncomputable def typeB2GroupEquivProjSp (q : PrimePower) (hv : (LieTypeIndex.B 2 q).Valid)
    [Fact q.p.Prime] :
    ValidLieTypeIndex.Group ⟨.B 2 q, hv⟩ ≃* projSp 2 (GaloisField q.p q.exponent) :=
  haveI := CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField ⟨.B 2 q, hv⟩
  let φ : ↥(ValidLieTypeIndex.fixedField ⟨.B 2 q, hv⟩) ≃+* GaloisField q.p q.exponent :=
    CFSG.ClassicalModels.finiteFieldEquivGaloisField _ q.p q.exponent q.exponent_pos (by
      rw [ValidLieTypeIndex.card_fixedField, ValidLieTypeIndex.fieldOrder_eq_characteristic_pow,
        show ValidLieTypeIndex.characteristic ⟨.B 2 q, hv⟩ = q.p from
          LieTypeIndex.characteristic_B 2 q,
        show ValidLieTypeIndex.fieldExponent ⟨.B 2 q, hv⟩ = q.exponent from
          LieTypeIndex.fieldExponent_B 2 q])
  (CFSG.QuasithinUnique.SQTK.typeB2GroupEquivStatedProj q hv).trans
    ((statedProjCongr (glCongr φ) (CFSG.ClassicalInvolution.Upgrade.glCongr_statedSp φ 2)
      (glCongr_statedScalars φ)).trans (statedProjEquivMapMk (StatedSp 2 _)))


@[expose] def BridgeSp6Two : Prop :=
  ∀ (q : PrimePower) (hv : (LieTypeIndex.B 3 q).Valid), q.p = 2 → q.exponent = 1 →
    Nonempty (ValidLieTypeIndex.Group ⟨.B 3 q, hv⟩ ≃* projSp 3 (GaloisField 2 1))

structure SpinLargePrimeRankThree : Prop where
  typeB3 : ∀ (q : PrimePower) (hv : (LieTypeIndex.B 3 q).Valid), q.p = 2 → 3 ≤ q.exponent →
    ∀ [Finite (CFSGIndex.lie ⟨.B 3 q, hv⟩).Group], ∃ r : ℕ, r.Prime ∧ 3 < r ∧
      3 ≤ localRank r (CFSGIndex.lie ⟨.B 3 q, hv⟩).Group
  twistedD4 : ∀ (q : PrimePower) (hv : (LieTypeIndex.twistedD 4 q).Valid), q.p = 2 →
    2 ≤ q.exponent → ∀ [Finite (CFSGIndex.lie ⟨.twistedD 4 q, hv⟩).Group], ∃ r : ℕ, r.Prime ∧
      3 < r ∧ 3 ≤ localRank r (CFSGIndex.lie ⟨.twistedD 4 q, hv⟩).Group

end CFSG.RankThree.PartTwo.Sec4.Census
