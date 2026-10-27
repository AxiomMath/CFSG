module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S20
public import CFSG.LocalAnalysis.UniquenessCase.UCFront08
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
import CFSG.LocalAnalysis.UniquenessCase.UC22P20c
import CFSG.LocalAnalysis.UniquenessCase.UC22P20e
import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.Cat.OutNoOdd
import CFSG.GroupTheory.PRankQuotientLift

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

variable {G : Type} [Group G] [Finite G]

theorem uc22s216_not_thin8_of_isSpor
    (hrank : ∀ (X : Type) [Group X] [Finite X] [Nontrivial X] (s : TauCeti.SporadicName),
      s ≠ .J1 → IsSpor X s → 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X))
    {M L : Subgroup G} (hL : L ∈ calC M) {s : TauCeti.SporadicName} (hs : s ≠ .J1)
    (hX : IsSpor (BarInf L) s) : ¬ F08.Thin8 L := by
  intro hthin
  haveI := (uc22p20c_barInf_simple (uc22p20e_cComp_of_calC hL)).1
  have h3 := CFSG.GroupTheory.two_le_pRank_of_quotient (CFSG.solvableRadical ↥L)
    Nat.prime_three (by norm_num) (hrank (BarInf L) s hs hX)
  rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup] at h3
  have h1 := hthin 3 Nat.prime_three (by norm_num)
  omega

theorem uc22s216_mem_range_conj_of_isSpor
    (hout : ∀ (X : Type) [Group X] [Finite X], IsSimpleGroup X → (∃ a b : X, a * b ≠ b * a) →
      ∀ s : TauCeti.SporadicName, IsSpor X s → Nat.card (Outer X) ≤ 2)
    {M L : Subgroup G} (hL : L ∈ calC M) {s : TauCeti.SporadicName}
    (hX : IsSpor (BarInf L) s) {σ : MulAut (BarInf L)} (hσ : Odd (orderOf σ)) :
    σ ∈ (MulAut.conj : BarInf L →* MulAut (BarInf L)).range := by
  obtain ⟨hsimp, hnc⟩ := uc22p20c_barInf_simple (uc22p20e_cComp_of_calC hL)
  have h2 := hout (BarInf L) hsimp hnc s hX
  haveI : Finite (MulAut (BarInf L)) :=
    Finite.of_injective (fun (g : MulAut (BarInf L)) (w : BarInf L) => g w)
      (fun g h hgh => MulEquiv.ext (congrFun hgh))
  have hpos : 0 < Nat.card (Outer (BarInf L)) := Nat.card_pos
  have hdvd : Nat.card (Outer (BarInf L)) ∣ 2 ^ 1 := by
    interval_cases h : Nat.card (Outer (BarInf L)) <;> norm_num
  exact CFSG.EvenSporadicStandard.HSStd.InvCent.mem_range_conj_of_odd_orderOf_of_card_outer_dvd
    hdvd hσ

end CFSG.LocalAnalysis.UniquenessCase.UC22
