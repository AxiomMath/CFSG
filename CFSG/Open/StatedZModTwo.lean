module

public import CFSG.Open.StatedAPI

public section

namespace CFSG.Open.StatedAPI

theorem statedSL_eq_top_of_card_two {K : Type} [Field K] (hK : Nat.card K = 2) (n : ℕ) :
    StatedSL n K = ⊤ := by
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  have : Subsingleton Kˣ :=
    (Nat.card_eq_one_iff_unique.mp (by rw [Nat.card_units, hK])).1
  refine eq_top_iff.mpr fun A _ => mem_statedSL_iff.mpr ?_
  have h : Matrix.GeneralLinearGroup.det A = 1 := Subsingleton.elim _ _
  simpa [Units.ext_iff] using h

theorem statedScalars_eq_bot_of_card_two {K : Type} [Field K] (hK : Nat.card K = 2)
    (ι : Type) [Fintype ι] [DecidableEq ι] : StatedScalars ι K = ⊥ := by
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  have : Subsingleton Kˣ :=
    (Nat.card_eq_one_iff_unique.mp (by rw [Nat.card_units, hK])).1
  rw [eq_bot_iff]
  rintro _ ⟨c, rfl⟩
  rw [Subsingleton.elim c 1, map_one]
  exact Subgroup.one_mem _

@[expose] noncomputable def statedSLZModTwoEquivStatedProj (n : ℕ) :
    StatedSL n (ZMod 2) ≃* StatedProj (StatedSL n (ZMod 2)) :=
  ((QuotientGroup.quotientMulEquivOfEq (by
      rw [statedScalars_zmod_two_eq_bot, Subgroup.bot_subgroupOf])).trans
    QuotientGroup.quotientBot).symm

theorem statedClassicalModel_psl_of_mulEquiv_statedSL_zmod_two {n : ℕ} (hn : 3 ≤ n) {X : Type}
    [Group X] (e : X ≃* StatedSL n (ZMod 2)) : StatedClassicalModel X .PSL n 2 1 :=
  ⟨⟨Nat.prime_two, le_rfl, by omega, fun h => absurd (congrArg Prod.fst h) (by omega),
      fun h => absurd (congrArg Prod.fst h) (by omega)⟩,
    ZMod 2, inferInstance, inferInstance, by simp, ⟨e.trans (statedSLZModTwoEquivStatedProj n)⟩⟩

end CFSG.Open.StatedAPI
