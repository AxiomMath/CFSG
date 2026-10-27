module

public import CFSG.Quasithin.Background.SmithA36Lift
public import CFSG.Quasithin.Background.B5NonInputs

public section

namespace CFSG.Quasithin

open Matrix

namespace SmithA36

theorem ringChar_eq_two_of_card {K : Type} [Field K] [Finite K] {n : ℕ}
    (h : Nat.card K = 2 ^ n) : ringChar K = 2 := by
  have : Fintype K := Fintype.ofFinite K
  have h1 : 1 < Nat.card K := Finite.one_lt_card
  rw [FiniteField.even_card_iff_char_two, Fintype.card_eq_nat_card, h]
  rcases n with _ | n
  · rw [h, pow_zero] at h1
    exact absurd h1 (lt_irrefl 1)
  · rw [pow_succ, Nat.mul_mod_left]

theorem injective_of_isQuasisimple_statedSL {L H : Type*} [Group L] [Group H]
    (hL : CFSG.IsQuasisimple L) {m : ℕ} (hm : 2 ≤ m) {K : Type} [Field K] [Finite K]
    (hK : ringChar K = 2) (e : H ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL (m + 1) K)) {f : L →* H}
    (hf : Function.Surjective f) (hodd : ∀ z ∈ f.ker, Odd (orderOf z)) :
    Function.Injective f := by
  have : CharP K 2 := ringChar.eq_iff.mp hK
  have : Group.IsPerfect L := hL.1
  let ψ : H ≃* SpecialLinearGroup (Fin (m + 1)) K :=
    e.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL (m + 1) K).symm
  let π : L →* SpecialLinearGroup (Fin (m + 1)) K := ψ.toMonoidHom.comp f
  have hπ : Function.Surjective π := ψ.surjective.comp hf
  have hker : ∀ z ∈ π.ker, z ∈ f.ker := fun z hz =>
    f.mem_ker.mpr ((map_eq_one_iff ψ ψ.injective).mp (π.mem_ker.mp hz))
  have hne : ∃ k, π k ≠ 1 := by
    have h01 : (⟨0, by omega⟩ : Fin (m + 1)) ≠ ⟨1, by omega⟩ := fun h =>
      absurd (congrArg Fin.val h) zero_ne_one
    obtain ⟨k, hk⟩ := hπ (SpecialLinearGroup.transvection h01 1)
    refine ⟨k, fun h => ?_⟩
    have h' := congrArg (fun A : SpecialLinearGroup (Fin (m + 1)) K =>
      (A : Matrix (Fin (m + 1)) (Fin (m + 1)) K) ⟨0, by omega⟩ ⟨1, by omega⟩) (hk.symm.trans h)
    simp [SpecialLinearGroup.transvection_coe] at h'
  have hcen : π.ker ≤ Subgroup.center L :=
    CFSG.LieType.CurtisTits.ker_le_center_of_isQuasisimple hL hne
  have hinj : Function.Injective π :=
    injective_of_perfect_sl_charTwo hm hπ hcen fun z hz => hodd z (hker z hz)
  intro x y hxy
  exact hinj (show ψ (f x) = ψ (f y) by rw [hxy])

end SmithA36

theorem asA36NoOddCover_holds : AsA36NoOddCover := by
  intro L H _ _ _ hL _ f hf hodd hH
  rcases hH with ⟨n, K, _, _, hcard, ⟨e⟩⟩ | ⟨K, _, _, hcard, ⟨e⟩⟩ | ⟨K, _, _, hcard, ⟨e⟩⟩
  · exact SmithA36.injective_of_isQuasisimple_statedSL hL (m := 2) le_rfl
      (SmithA36.ringChar_eq_two_of_card hcard) e hf hodd
  · exact SmithA36.injective_of_isQuasisimple_statedSL hL (m := 3) (by norm_num)
      (SmithA36.ringChar_eq_two_of_card (n := 1) hcard) e hf hodd
  · exact SmithA36.injective_of_isQuasisimple_statedSL hL (m := 4) (by norm_num)
      (SmithA36.ringChar_eq_two_of_card (n := 1) hcard) e hf hodd

end CFSG.Quasithin
