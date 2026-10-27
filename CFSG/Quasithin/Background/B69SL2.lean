module

public import CFSG.Quasithin.Background.A3StructureDefs
public import CFSG.LieType.Simplicity.Classical
public import CFSG.Assembly.GL83LieDefs

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank

namespace B69

theorem statedScalars_subgroupOf_eq_bot {K : Type} [Field K] (hK : Nat.card K = 2) (n : ℕ) :
    (StatedScalars (Fin n) K).subgroupOf (StatedSL n K) = ⊥ := by
  have hfin : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  have hu : Nat.card Kˣ = 1 := by rw [Nat.card_units, hK]
  have hsub : Subsingleton Kˣ := (Nat.card_eq_one_iff_unique.mp hu).1
  have : StatedScalars (Fin n) K = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨c, rfl⟩
    rw [Subsingleton.elim c 1, map_one]
    exact Subgroup.one_mem _
  rw [this, Subgroup.bot_subgroupOf]

noncomputable def statedSLEquivStatedProj {K : Type} [Field K] (hK : Nat.card K = 2) (n : ℕ) :
    ↥(StatedSL n K) ≃* StatedProj (StatedSL n K) :=
  (QuotientGroup.quotientBot (G := ↥(StatedSL n K))).symm.trans
    (QuotientGroup.quotientMulEquivOfEq (statedScalars_subgroupOf_eq_bot hK n).symm)

theorem isSimpleGroup_statedSL_two {K : Type} [Field K] (hK : Nat.card K = 2) {n : ℕ} (hn : 3 ≤ n) :
    IsSimpleGroup ↥(StatedSL n K) := by
  have hfin : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  have hmod : IsPSL n 2 1 (StatedProj (StatedSL n K)) := by
    refine ⟨⟨Nat.prime_two, le_rfl, by omega, ?_, ?_⟩, K, inferInstance, hfin, by simpa using hK,
      ⟨MulEquiv.refl _⟩⟩
    · intro h
      simp only [Prod.mk.injEq] at h
      omega
    · intro h
      simp only [Prod.mk.injEq] at h
      omega
  have := (CFSG.LieType.Simplicity.fam_PSL_simplicity _ n 2 1 hmod).2
  exact (MulEquiv.isSimpleGroup_congr (statedSLEquivStatedProj hK n)).mpr this

theorem card_statedSL_two_four {K : Type} [Field K] (hK : Nat.card K = 2) :
    Nat.card ↥(StatedSL 4 K) = 20160 :=
  CFSG.Open.StatedAPI.card_statedSL_four_of_card_eq_two hK

theorem card_statedSL_two_five {K : Type} [Field K] (hK : Nat.card K = 2) :
    Nat.card ↥(StatedSL 5 K) = 9999360 :=
  CFSG.Open.StatedAPI.card_statedSL_five_of_card_eq_two hK

end B69

end CFSG.Quasithin
