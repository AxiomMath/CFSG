module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.FourTenDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_16FactsA6Model
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.FourTenBasic
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.FourTenNineModels
public import CFSG.Adapters.StatedPSLTwoNine

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Quasithin CFSG.Open Subgroup CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts
open CFSG.QuasithinUnique.Unc25K1.A6Model

theorem eq_psl29_or_nonempty_mulEquiv_perm_of_le_s6 {B : Subgroup P10}
    (hpsl : A6Models.psl29 ≤ B) (hB : B ≤ s6) :
    B = A6Models.psl29 ∨ Nonempty (↥B ≃* Equiv.Perm (Fin 6)) := by
  obtain ⟨θ, -, hθinj, -⟩ := exists_pslEquiv
  let j : ↥B →* Equiv.Perm (Fin 6) := θ.comp (Subgroup.inclusion hB)
  have hj : Function.Injective j := hθinj.comp (Subgroup.inclusion_injective hB)
  have h720 : Nat.card (Equiv.Perm (Fin 6)) = 720 := by
    rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
    rfl
  have hle : Nat.card B ≤ 720 := h720 ▸ Nat.card_le_card_of_injective j hj
  obtain ⟨m, hm⟩ : 360 ∣ Nat.card B := card_psl29 ▸ Subgroup.card_dvd_of_le hpsl
  have hpos : 0 < Nat.card B := Nat.card_pos
  have hm2 : m = 1 ∨ m = 2 := by
    rcases m with _ | _ | _ | m
    · omega
    · exact Or.inl rfl
    · exact Or.inr rfl
    · omega
  rcases hm2 with rfl | rfl
  · have hBc : Nat.card B = 360 := by omega
    exact Or.inl (Subgroup.eq_of_le_of_card_ge hpsl (le_of_eq (hBc.trans card_psl29.symm))).symm
  · have hBc : Nat.card B = 720 := by omega
    exact Or.inr ⟨MulEquiv.ofBijective j
      (hj.bijective_of_nat_card_le (le_of_eq (h720.trans hBc.symm)))⟩

theorem fourTenNine_holds : FourTenNine := by
  intro Q _ _ L p e h hpe T hT Ω hΩ h4
  obtain ⟨rfl, rfl⟩ := hpe
  have := h.normal
  obtain ⟨e₀⟩ := CFSG.Open.StatedAPI.nonempty_mulEquiv_alternating_six_of_psl_two_nine h.isL2
  obtain ⟨ι, hι, hpsl⟩ := exists_autA6_embedding L e₀ h.centralizer_eq_bot
  set B : Subgroup P10 := ι.range.map A6Models.autA6.subtype
  have hBle : B ≤ A6Models.autA6 := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hQB : Q ≃* ↥B := (MonoidHom.ofInjective hι).trans
    (ι.range.equivMapOfInjective _ A6Models.autA6.subtype_injective)
  by_cases hs : B ≤ s6
  · exfalso
    rcases eq_psl29_or_nonempty_mulEquiv_perm_of_le_s6 hpsl hs with hB9 | ⟨⟨eB⟩⟩
    · have hQ : Nat.card Q = 360 := by
        rw [Nat.card_congr hQB.toEquiv, hB9, card_psl29]
      have hL : L = ⊤ := Subgroup.eq_top_of_card_eq L (by
        rw [Nat.card_congr e₀.toEquiv, card_alt6, hQ])
      exact h.not_small (Or.inr (Or.inl
        (CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv
          ((MulEquiv.subgroupCongr hL).trans Subgroup.topEquiv) h.isL2)))
    · exact h.not_small (Or.inr (Or.inr ⟨hQB.trans eB⟩))
  · obtain ⟨σ, hσB, hσs⟩ := SetLike.not_le_iff_exists.mp hs
    have hrange : (A6Models.autA6.subtype.comp ι).range = B :=
      MonoidHom.range_comp A6Models.autA6.subtype ι
    have hinj : Function.Injective (A6Models.autA6.subtype.comp ι) :=
      A6Models.autA6.subtype_injective.comp hι
    rcases classify B hBle hpsl ⟨σ, hσB, hσs⟩ with hBM | hBM | hBM
    · exact genEi_sup_eq_top_of_fourTenModel FourTenQ9.fourTenModel_pgl29 _ hinj
        (hrange.trans hBM) hT (h.tA_eq T) hΩ h4
    · exact genEi_sup_eq_top_of_fourTenModel FourTenQ9.fourTenModel_m10 _ hinj
        (hrange.trans hBM) hT (h.tA_eq T) hΩ h4
    · exact genEi_sup_eq_top_of_fourTenModel FourTenQ9.fourTenModel_autA6 _ hinj
        (hrange.trans hBM) hT (h.tA_eq T) hΩ h4

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
