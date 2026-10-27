module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesWeylPTorsion
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesFixE6
public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6Basic
public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoToralExcAdj

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

namespace ExcFrames

section SplitE6


theorem exists_weylFrame_E6 {K : Type} [Field K] [Finite K] {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hpq : p ∣ Nat.card K - 1) {G : Type} [Group G]
    (χ : adjointGroup .E6 K →* G) (hχ : Function.Injective χ) {Bs : Subgroup G}
    (hBsR : Bs ≤ χ.range) (hBs : IsElemAbelian p Bs) (hr : p ^ Tag.E6.rank ≤ Nat.card Bs) :
    ∃ ι : Multiplicative (Fin Tag.E6.rank → ZMod p) →* G, Function.Injective ι ∧ ι.range = Bs ∧
      ∀ g ∈ Subgroup.normalizer (χ.range : Set G), g ∈ Subgroup.normalizer (Bs : Set G) →
        g ^ p = 1 → ∃ w : WeylGroup .E6, ∀ s : Fin Tag.E6.rank → ZMod p,
          g * ι (Multiplicative.ofAdd s) * g⁻¹ =
            ι (Multiplicative.ofAdd (TableBExc.torusAct .E6 p w s)) := by
  have hp : p.Prime := Fact.out
  have hp3' : Nat.Coprime 3 p := (Nat.coprime_primes Nat.prime_three hp).2 (Ne.symm hp3)
  obtain ⟨c, hc⟩ := TableBExc.ggExcToralRankInput_E6_of_ne_three hp hp2 hp3 hpq (Bs.comap χ)
    (isElemAbelian_comap_frame χ hχ hBs) (by rw [card_comap_of_le_range χ hχ hBsR]; exact hr)
  exact exists_weylFrame_of_toral_fullp (StepTwoToralExc.isUnit_det_symmetrizedCartan_E6 hp3) hpq
    (fun a ha => TableBExc.fullp_E6 hp.one_lt hp3' a ha)
    (fun α hα => exists_inner_on_torusPow_E6 hp2 α hα) χ hχ hBsR ⟨c, hc⟩

end SplitE6

end ExcFrames

end CFSG.StandardType
