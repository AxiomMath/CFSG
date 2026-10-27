module

public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPFinite

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsL2 IsU3 IsSp4)

private theorem wc813sch_card_multiplicative_zmod (k : ℕ) :
    Nat.card (Multiplicative (ZMod k)) = k :=
  (Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod k) ≃ ZMod k)).trans
    (Nat.card_zmod k)

private theorem wc813sch_card_center_dvd_griess_hopf {G : Type} [Group G] [Finite G]
    (hperf : Group.IsPerfect G) :
    Nat.card ↥(Subgroup.center G) ∣
      Nat.card (CFSG.Open.griessHopfMultiplier (G ⧸ Subgroup.center G)) := by
  haveI : Group.IsPerfect G := hperf
  haveI : Group.IsPerfect (G ⧸ Subgroup.center G) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (Subgroup.center G))
      (QuotientGroup.mk'_surjective _)
  obtain ⟨-, h, -, -, -, -, e, -⟩ :=
    CFSG.RankThree.PerfectCover.perfect_central_kernel_quotient_of_hopf_multiplier
      (S := G ⧸ Subgroup.center G) (QuotientGroup.mk' (Subgroup.center G))
      (QuotientGroup.mk'_surjective _) (by rw [QuotientGroup.ker_mk'])
  rw [Nat.card_congr (CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess
    (G ⧸ Subgroup.center G)).toEquiv]
  have hk : Nat.card ↥(Subgroup.center G) =
      Nat.card ↥(QuotientGroup.mk' (Subgroup.center G)).ker := by
    rw [QuotientGroup.ker_mk']
  rw [hk, ← Nat.card_congr e.toEquiv]
  exact Subgroup.card_quotient_dvd_card _

private theorem wc813sch_models_lieModel_of_ne_zero {X : Type} [Group X]
    {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {n p f : ℕ} (hn : n ≠ 0)
    (h : CFSG.Blueprint.LieModel X t n p f) : CFSG.Models.LieModel X t n p f :=
  ⟨CFSG.Blueprint.LieModel.admissible h,
    Or.inl (CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero hn h)⟩

private theorem wc813sch_card_center_dvd_table (hG : CFSG.Open.GriessAllModelsStatement)
    {Q : Type} [Group Q] [Finite Q] (hperf : Group.IsPerfect Q)
    {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {n p f : ℕ}
    (hm : CFSG.Models.LieModel (Q ⧸ Subgroup.center Q) t n p f) :
    Nat.card ↥(Subgroup.center Q) ∣
      (CFSG.Blueprint.Multiplier.genericOrders t n p f).1 *
        (CFSG.Blueprint.Multiplier.genericOrders t n p f).2 *
        ((CFSG.Blueprint.Multiplier.exceptionalOrders t n p f).1 *
          (CFSG.Blueprint.Multiplier.exceptionalOrders t n p f).2) := by
  have hdvd := wc813sch_card_center_dvd_griess_hopf (G := Q) hperf
  obtain ⟨-, ⟨e⟩⟩ := hG (Q ⧸ Subgroup.center Q) t n p f hm
  have hcard : Nat.card (CFSG.Open.griessHopfMultiplier (Q ⧸ Subgroup.center Q)) =
      (CFSG.Blueprint.Multiplier.genericOrders t n p f).1 *
        (CFSG.Blueprint.Multiplier.genericOrders t n p f).2 *
        ((CFSG.Blueprint.Multiplier.exceptionalOrders t n p f).1 *
          (CFSG.Blueprint.Multiplier.exceptionalOrders t n p f).2) := by
    rw [Nat.card_congr e.toEquiv, Nat.card_prod, Nat.card_prod, Nat.card_prod,
      wc813sch_card_multiplicative_zmod, wc813sch_card_multiplicative_zmod,
      wc813sch_card_multiplicative_zmod, wc813sch_card_multiplicative_zmod]
  rwa [hcard] at hdvd

private theorem wc813sch_tableOrder_PSL_two_two_two :
    (CFSG.Blueprint.Multiplier.genericOrders .PSL 2 2 2).1 *
        (CFSG.Blueprint.Multiplier.genericOrders .PSL 2 2 2).2 *
      ((CFSG.Blueprint.Multiplier.exceptionalOrders .PSL 2 2 2).1 *
        (CFSG.Blueprint.Multiplier.exceptionalOrders .PSL 2 2 2).2) = 2 := by
  decide

private theorem wc813sch_tableOrder_PSU_three_two_two :
    (CFSG.Blueprint.Multiplier.genericOrders .PSU 3 2 2).1 *
        (CFSG.Blueprint.Multiplier.genericOrders .PSU 3 2 2).2 *
      ((CFSG.Blueprint.Multiplier.exceptionalOrders .PSU 3 2 2).1 *
        (CFSG.Blueprint.Multiplier.exceptionalOrders .PSU 3 2 2).2) = 1 := by
  decide

private theorem wc813sch_tableOrder_PSp_two_two_two :
    (CFSG.Blueprint.Multiplier.genericOrders .PSp 2 2 2).1 *
        (CFSG.Blueprint.Multiplier.genericOrders .PSp 2 2 2).2 *
      ((CFSG.Blueprint.Multiplier.exceptionalOrders .PSp 2 2 2).1 *
        (CFSG.Blueprint.Multiplier.exceptionalOrders .PSp 2 2 2).2) = 1 := by
  decide

private theorem wc813sch_eq_one_of_odd_dvd_two {a : ℕ} (hodd : Odd a) (hdvd : a ∣ 2) :
    a = 1 := by
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
  · exact h1
  · exfalso
    obtain ⟨k, hk⟩ := hodd
    omega

theorem oddSchurMultiplierFact_of_griess (hG : CFSG.Open.GriessAllModelsStatement) :
    OddSchurMultiplierFact := by
  intro Q _ _ hQ hodd hX
  have hperf : Group.IsPerfect Q := Group.isPerfect_def.mpr hQ.1
  rcases hX with hX | hX | hX
  · have hm : CFSG.Models.LieModel (Q ⧸ Subgroup.center Q) .PSL 2 2 2 :=
      wc813sch_models_lieModel_of_ne_zero (by norm_num) hX
    have hle := wc813sch_card_center_dvd_table hG hperf hm
    rw [wc813sch_tableOrder_PSL_two_two_two] at hle
    exact wc813sch_eq_one_of_odd_dvd_two hodd hle
  · have hm : CFSG.Models.LieModel (Q ⧸ Subgroup.center Q) .PSU 3 2 2 :=
      wc813sch_models_lieModel_of_ne_zero (by norm_num) hX
    have hle := wc813sch_card_center_dvd_table hG hperf hm
    rw [wc813sch_tableOrder_PSU_three_two_two] at hle
    exact Nat.dvd_one.mp hle
  · have hm : CFSG.Models.LieModel (Q ⧸ Subgroup.center Q) .PSp 2 2 2 :=
      wc813sch_models_lieModel_of_ne_zero (by norm_num) hX
    have hle := wc813sch_card_center_dvd_table hG hperf hm
    rw [wc813sch_tableOrder_PSp_two_two_two] at hle
    exact Nat.dvd_one.mp hle

end CFSG.LocalAnalysis.WeakClosure81

end
