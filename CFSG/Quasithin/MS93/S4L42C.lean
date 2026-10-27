module

import CFSG.Quasithin.MS93.S34FPar
import CFSG.Quasithin.MS93.S33F2
public import CFSG.Quasithin.MS93.S34FFlat
public import CFSG.Quasithin.MS93.S4AH1

public section

namespace CFSG.Quasithin.MS93.S4L

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open CFSG.Quasithin.MS93.S4A
open scoped Matrix commutatorElement

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}

theorem exists_natural_flat_of_nonfull (h : PUHyp M T L) (hU : IsSL3U M T L)
    (hF : ¬ IsSL3Full M T L) :
    ∃ (F : Type) (_ : Field F) (_ : Fintype F) (φ : ↥(L ⊔ pCoreOf 2 M) →* ↥(StatedSL 3 F)),
      CharP F 2 ∧ 4 ≤ Nat.card F ∧ Function.Surjective φ ∧
        IsSumOfNaturalModulesVia (L ⊔ pCoreOf 2 M) (Uq M T L) ⊥ φ false 1 := by
  obtain ⟨-, -, m, F, _, _, a, hcard, ha, hLV, hZV, β, hβ, hβker, hβα⟩ :=
    S34F.isSL3UEven_of_nonfull h hU hF
  have hQV : pCoreOf 2 M ≤ Subgroup.normalizer (Uq M T L : Set G) :=
    (pCoreOf_le' M).trans (le_normalizer_Uq h.le_normalizer)
  obtain ⟨φ, hφ, hnat⟩ := exists_natural_of_coordAct (Γ := StatedSL 3 F) (A := L)
    (M := L ⊔ pCoreOf 2 M) (T := pCoreOf 2 M) rfl ha hLV hZV hβ hβker hβα hQV fun t ht =>
      ⟨1, (S33.isCoordAct_id_of_le_centralizer (S34F.pCoreOf_le_centralizer_Uq h ht)).congr
        fun x => by simp⟩
  have hFn : Nat.card F = 2 ^ (2 * m) := by
    rw [Nat.card_eq_fintype_card, hcard, S34F.four_pow_eq]
  have hm : m ≠ 0 := by
    rintro rfl
    have h1 := Fintype.one_lt_card (α := F)
    rw [hcard, pow_zero] at h1
    exact lt_irrefl _ h1
  refine ⟨F, inferInstance, inferInstance, φ, FFC.charP_two_of_card_pow hFn, ?_, hφ, hnat⟩
  rw [Nat.card_eq_fintype_card, hcard]
  calc 4 = 4 ^ 1 := by norm_num
    _ ≤ 4 ^ m := Nat.pow_le_pow_right (by norm_num) (Nat.one_le_iff_ne_zero.mpr hm)

end CFSG.Quasithin.MS93.S4L
