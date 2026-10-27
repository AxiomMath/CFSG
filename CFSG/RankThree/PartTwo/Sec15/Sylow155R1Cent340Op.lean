module

public import CFSG.Open.LocalVocabulary
import CFSG.RankThree.PartTwo.Sec11.TwoStarProofLFTools
import CFSG.RankThree.PartTwo.Sec15.Sylow155R1CentSL2
import CFSG.LocalAnalysis.SectionRank.AmbientRank
import CFSG.RankThree.PartTwo.Sec11.Item116EiiCoprime

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155R1

open CFSG.RankThree.PartTwo.Sec11
open CFSG.RankThree.PartOne.FixedRank36 (fixedSub frattiniRep)
open scoped IsMulCommutative

theorem res1340_mulAut_eq_one_of_pRank_le_two {L : Type*} [Group L] [Finite L]
    [Group.IsPerfect L] {N : Subgroup L} [N.Normal] (hN : Group.IsSolvable N)
    (hN3 : ¬ 3 ∣ Nat.card N) (hsimple : IsSimpleGroup (L ⧸ N)) {E : Subgroup L}
    (hE : CFSG.Open.IsElemAbelian 3 E) (hE9 : Nat.card E = 9)
    {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) {T : Type} [Group T] [Finite T] (hT : IsPGroup p T)
    (hrank : CFSG.Open.pRank p (⊤ : Subgroup T) ≤ 2) (φ : L →* MulAut T) : φ = 1 := by
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := by omega
  by_contra hne
  have hφ : ∃ x, φ x ≠ 1 := by
    by_contra h
    push Not at h
    exact hne (MonoidHom.ext h)
  obtain ⟨D, hDchar, hDp, hexp, hclass, hel, l, hl⟩ :=
    TwoStarProof.exists_critical_rep_ne_one hp2 hT φ hφ
  set ρD : L →* MulAut ↥D := (Sec3.restrictCharacteristic D).comp φ
  have hdim : Module.finrank (ZMod p) (Additive (↥D ⧸ frattini ↥D)) ≤ 2 := by
    by_contra hlt
    push Not at hlt
    have hker : Module.finrank (ZMod p) (LinearMap.ker (frattiniRep p ρD 1 - 1)) =
        Module.finrank (ZMod p) (Additive (↥D ⧸ frattini ↥D)) := by
      rw [map_one, sub_self, LinearMap.ker_zero, finrank_top]
    have h3 := TwoStarProof.three_le_pRank_fixed hp2 hDp hexp hclass ρD (t := 1) (k := 0)
      (one_pow _) (by rw [hker]; omega)
    have h4 : CFSG.pRank p ↥(fixedSub (ρD 1)) ≤ CFSG.Open.pRank p (⊤ : Subgroup T) :=
      calc CFSG.pRank p ↥(fixedSub (ρD 1)) = CFSG.Open.pRank p (fixedSub (ρD 1)) :=
            CFSG.SectionRank.pRank_coe_eq_openPRank p _
        _ ≤ CFSG.Open.pRank p ((fixedSub (ρD 1)).map D.subtype) :=
            CFSG.SectionRank.pRank_le_map hp.one_lt D.subtype D.subtype_injective _
        _ ≤ CFSG.Open.pRank p (⊤ : Subgroup T) := CFSG.SectionRank.pRank_mono hp.one_lt le_top
    omega
  have h3 : (3 : ZMod p) ≠ 0 := by
    intro h
    have h' : ((3 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h'
    have := Nat.le_of_dvd (by norm_num) h'
    omega
  have : Module.Finite (ZMod p) (Additive (↥D ⧸ frattini ↥D)) := Module.Finite.of_finite
  exact hl (res1Cent_rho_eq_one_of_finrank_le_two hN hN3 hsimple hE hE9 h3 hdim
    (frattiniRep p ρD) l)

end CFSG.RankThree.PartTwo.Sec15.Sylow155R1
