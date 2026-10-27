module

public import CFSG.LocalAnalysis.StandardType.GGLieCoreToral
public import CFSG.LocalAnalysis.StandardType.GGLieCoreToralHolds
public import CFSG.LocalAnalysis.StandardType.GGLieBridgeHolds
import CFSG.LocalAnalysis.StandardType.GGLieCoreA3DictPhi
import CFSG.LocalAnalysis.StandardType.GGLieCoreRatFinite
public import Certificates.Certificate1952
public import Certificates.Certificate2264
public import Certificates.Certificate2267
public import Certificates.Certificate3951
public import Certificates.Certificate8033
public import Certificates.Certificate8064
public import Certificates.Certificate13659
public import Certificates.Certificate13660
public import Certificates.Certificate13604
public import Certificates.Certificate13605
public import Certificates.Certificate13691
public import Certificates.Certificate13720
public import Certificates.Certificate13721
public import Certificates.Certificate13722
public import Certificates.Certificate13723
public import Certificates.Certificate13724

public section

namespace CFSG.StandardType.A6Red

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.StandardType CFSG.StandardType.GGFinModel CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.RankThree.PartOne.KE
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.Open (StatedLieTag)
open scoped commutatorElement
open CFSG.StandardType.LieCore
open CFSG.StandardType.ExcFramesHalf (IsToralSubgroup)

theorem a6glue_toral_or_nontoral
    {t : StatedLieTag} (ht : GGExcFive t) {f : ℕ} (hf : 1 ≤ f) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {A : Subgroup (ModGL (langTag t) GGL)} (hA : A ≤ ggFixGp t f)
    (hel : IsElemAbelian p A) (hcard : Nat.card A ≤ p ^ 2) :
    IsToralSubgroup (langTag t) GGL A ∨ (langTag t = .E6 ∧ p = 3 ∧ Nat.card A = 3 ^ 2) := by
  by_cases hE6 : langTag t = .E6 → p = 3 → Nat.card A ≤ p
  · left
    have hZ : IsSteinbergEndZ (langTag t) GGL (2 ^ f) (ggPhi t f) :=
      isSteinbergEndZ_of_isSteinbergEnd (isSteinbergEnd_ggPhi ht f)
    have hfinΦ : Finite ↥(ratPoints (ggPhi t f)) :=
      finite_ratPoints (q := 2 ^ f)
        (Nat.one_lt_pow (n := f) (by omega) (by norm_num : (1 : ℕ) < 2)) hZ
    have hfinG : Finite ↥(ggFixGp t f) := hfinΦ
    have hfinA : Finite A := by
      have : Finite ↥(ggFixGp t f) := hfinG
      exact Finite.of_injective (Subgroup.inclusion hA) (Subgroup.inclusion_injective hA)
    exact isToralSubgroup_of_card_le_sq (τ := langTag t) (L := GGL)
      (CFSG.HardMathSupport.Timmesfeld.CrossChar.isAlgebraic_zmod_algebraicClosure_of_finite
        (ZMod 2) 2) hp hp2 (hA.trans inf_le_left) hfinA hel hcard hE6
  · right
    push Not at hE6
    obtain ⟨hτ, hp3, hlt⟩ := hE6
    refine ⟨hτ, hp3, ?_⟩
    have hfinA : Finite A :=
      Nat.finite_of_card_ne_zero (lt_of_le_of_lt (Nat.zero_le p) hlt).ne'
    have : Fact p.Prime := ⟨hp⟩
    have : Finite A := hfinA
    have hisP : IsPGroup p A := fun x =>
      ⟨1, Subtype.ext (by rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one]; exact hel.2 x x.2)⟩
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hisP
    have hk2 : k ≤ 2 := by
      have h := hcard
      rw [hk] at h
      exact (Nat.pow_le_pow_iff_right hp.one_lt).mp h
    have hk1 : 1 < k := by
      rw [hk, hp3] at hlt
      exact (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 3)).mp (by simpa using hlt)
    have hk2' : k = 2 := by omega
    rw [hk, hp3, hk2']

end CFSG.StandardType.A6Red
