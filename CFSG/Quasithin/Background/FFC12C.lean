module

public import CFSG.Quasithin.Background.FFC12B

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank

namespace B69

theorem asB69RankOneSylow_proved : AsB69RankOneSylow := by
  intro V _ _ hV X T M A L hH W hW hex
  obtain ⟨e, he, hnat⟩ := hex
  obtain ⟨-, -, hO2, -, -, hA, hL, hLA⟩ := hH
  have hAnL : A ≤ Subgroup.normalizer (L : Set (MulAut V)) := le_normalizer_of_commutator_eq hLA
  have hAn : ∀ a ∈ A, ∀ l ∈ L, a * l * a⁻¹ ∈ L := fun a ha l hl =>
    B19Aux.conj_mem_of_le_normalizer hAnL ha hl
  have hAW := a_stab_irr hV hA hL.2.2 hLA hW
  have hAst : A ≤ stabSub W := B1.le_stabSub_of_invariant hAW
  have hAU : A ≤ stabSub (W ⊓ fixV L) :=
    B1.le_stabSub_of_invariant (isInv_inf hAW (B1Red.fixV_inv_of_normalizes hAn))
  have hact := exists_act_natural hL.2.2 hW he hnat hA.1 hAn hAW
  obtain ⟨hS, hge⟩ := natural_counts hV hA hL.2.2 hLA hW he hnat hact
  have hsup := (eq_sup_fixV_of_sec hV hA hL.2.2 hLA hW hS).1
  have hAL : A ≤ L := le_of_act hV hO2 hA hL hLA hW hsup hact
  have hcard : Nat.card (autSec A W (W ⊓ fixV L)) ≤ Nat.card A := by
    have := card_autSec_mul hAst hAU
    exact Nat.le_of_dvd Nat.card_pos ⟨_, this.symm⟩
  obtain ⟨K, hKf, hKfin, hK, π₀, hπ₀⟩ := hnat
  let π : ↥(StatedSL 2 K) →* ↥L := π₀
  have hπ : (FFModel.nat (StatedSL 2 K)).RealizesVia L W (W ⊓ fixV L) π := hπ₀
  exact isSylowTwoOf_of_natural hAL hA.1.2.2.1.2 he hK π hπ.1 (hge.trans hcard)

end B69

end CFSG.Quasithin
