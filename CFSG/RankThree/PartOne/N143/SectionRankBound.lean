module

import CFSG.RankThree.OddKernel.ThreeComplementQuotient
import CFSG.LieType.CurtisTits.Conclusion
public import CFSG.RankThree.PartOne.S11.SecTenEight
public import CFSG.RankThree.PartOne.S8.Statements

public section

namespace CFSG.RankThree.PartOne.N143

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank Subgroup
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open CFSG.RankThree.PartOne (Sec6EightMultipliers TauCetiCatalogBridge)

theorem isKGroup_of_section {L M : Type} [Group L] [Group M] (hL : CFSG.IsKGroup L)
    (H : Subgroup L) (π : H →* M) (hπ : Function.Surjective π) : CFSG.IsKGroup M :=
  (hL.subgroup H).of_surjective π hπ

theorem sec68_full {Y : Type} [Group Y] [Finite Y] (h68 : Sec6EightMultipliers)
    (hbridge : TauCetiCatalogBridge) (hYK : CFSG.IsKGroup Y) (hq : CFSG.IsQuasisimple Y)
    (he : CFSG.Assembly.evenRank Y ≤ 3) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ3 : 3 < ℓ)
    (hdvd : ℓ ∣ Nat.card (center Y)) :
    ℓ = 5 ∧ Nat.card (center Y) = 5 ∧
      ∃ n : ℕ, 1 ≤ n ∧ StatedClassicalModel (Y ⧸ center Y) .PSU 5 2 n := by
  have hqt : CFSG.IsQuasisimple (⊤ : Subgroup Y) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.topEquiv : (⊤ : Subgroup Y) ≃* Y).symm hq
  have hsimple : IsSimpleGroup ((⊤ : Subgroup Y) ⧸ center (⊤ : Subgroup Y)) := hqt.2.1
  have hcat : CFSG.Blueprint.Catalog ((⊤ : Subgroup Y) ⧸ center (⊤ : Subgroup Y)) :=
    hbridge _ hqt.2.2 (hYK ⊤ (center (⊤ : Subgroup Y)) hsimple)
  have hcard : Nat.card (center (⊤ : Subgroup Y)) = Nat.card (center Y) :=
    Nat.card_congr (Subgroup.centerCongr (Subgroup.topEquiv : (⊤ : Subgroup Y) ≃* Y)).toEquiv
  have hpZ : ℓ ∣ Nat.card (center (⊤ : Subgroup Y)) := hcard ▸ hdvd
  have he' : CFSG.twoLocalOddRank Y ≤ 3 := by
    rw [← CFSG.RankThree.OddKernel.evenRank_eq_twoLocalOddRank]
    exact he
  obtain ⟨h5, hc5, n, hn, hmodel⟩ := h68 Y he' ⊤ ℓ hℓ hℓ3 hqt hcat hpZ
  refine ⟨h5, hcard ▸ hc5, n, hn, ?_⟩
  exact CFSG.LieType.CurtisTits.statedClassicalModel_of_mulEquiv
    (QuotientGroup.congr _ _ (Subgroup.topEquiv : (⊤ : Subgroup Y) ≃* Y)
      (Subgroup.map_center_eq (Subgroup.topEquiv : (⊤ : Subgroup Y) ≃* Y))) hmodel

theorem prime_dvd_center_eq_five {Y : Type} [Group Y] [Finite Y] (h68 : Sec6EightMultipliers)
    (hbridge : TauCetiCatalogBridge) (hYK : CFSG.IsKGroup Y) (hq : CFSG.IsQuasisimple Y)
    (he : CFSG.Assembly.evenRank Y ≤ 3) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ3 : 3 < ℓ)
    (hdvd : ℓ ∣ Nat.card (center Y)) : ℓ = 5 :=
  (sec68_full h68 hbridge hYK hq he hℓ hℓ3 hdvd).1

end CFSG.RankThree.PartOne.N143
