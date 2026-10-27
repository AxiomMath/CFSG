module

public import CFSG.LocalAnalysis.StandardType.GGKGForkExcFrame
public import CFSG.LocalAnalysis.StandardType.GGTwE6CorootCoreFrame
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.TorusAtDatum
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.TorusAtCore

public section

namespace CFSG.StandardType

namespace ExcE6Split

open CFSG CFSG.Assembly CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.StandardType.TwE6CorootCore CFSG.StandardType.TableBExcTwoFusion CFSG.RankThree.Chevalley
  CFSG.RankThree.PartOne.KE

theorem exists_splitFrame
    {K : Type} [Field K] [Finite K] {p : ℕ}
    (Fr : AlgebraicClosure K →+* AlgebraicClosure K) (hFr : ∀ c, Fr c = c ^ Nat.card K)
    {ET : Subgroup (adjointGroup .E6 K)}
    (hET : ∀ x : adjointGroup .E6 K, x ∈ ET ↔ x ^ p = 1 ∧
      baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL .E6 K) ∈
          twistedTorusOf (1 : ModGL .E6 (AlgebraicClosure K)) (Units.map (entrywiseHom Fr))) :
    ∃ F : ExcFrame .E6 K p ET, F.w = 1 ∧ F.D.g0 = 1 ∧ F.D.n = 1 := by
  let L := AlgebraicClosure K
  let D : LangDatum .E6 L :=
    LangDatum.ofFrobenius Fr (Nat.card K) hFr 1 (Subgroup.one_mem _) (by
      simp [canonicalRep_one])
  refine ⟨{ D := D
            w := 1
            q_eq := rfl
            frob := ⟨Fr, hFr, fun g => rfl⟩
            n_eq := rfl
            mem_iff := ?_ }, rfl, ?_, ?_⟩
  · intro x
    rw [hET x]
    constructor
    · rintro ⟨hp, hmem⟩
      exact ⟨hp, by simpa [D, LangDatum.ofFrobenius, LangDatum.torus, canonicalRep_one] using hmem⟩
    · rintro ⟨hp, hmem⟩
      exact ⟨hp, by simpa [D, LangDatum.ofFrobenius, LangDatum.torus, canonicalRep_one] using hmem⟩
  · simp [D, LangDatum.ofFrobenius]
  · simp [D, LangDatum.ofFrobenius, canonicalRep_one]

end ExcE6Split

end CFSG.StandardType

end
