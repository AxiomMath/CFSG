module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KGroupFacts
public import CFSG.Adapters.StatedClassicalUnitaryOrders
public import CFSG.RankThree.PartOne.KF.ClsSUUpper
public import CFSG.Quasithin.Vol2.F134Orders
public import CFSG.Quasithin.EmptyFaithful.SBd10Lie
public import CFSG.RankThree.PartTwo.Sec4.Item417Res4ProofL3
public import CFSG.GH74.SmallRanks.PSU3
public import CFSG.GroupTheory.PGroup.PrimePartTransport
public import CFSG.GroupTheory.PRankCoprimeQuotient
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdRank
public import CFSG.LocalAnalysis.UniquenessCase.UCKOutPB
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15ACoreMatUni

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Open
open CFSG.LocalAnalysis.UniquenessCase.UC22

theorem k_U3FourPowThreeRankOne_holds : K_U3FourPowThreeRankOne := by
  intro X _ _ n hn hX
  have hSC : CFSG.Open.StatedClassicalModel X .PSU 3 2 (2 * n) :=
    CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero (by omega) hX
  have hSC' := hSC
  obtain ⟨-, K, hKfield, hKfin, hK, ⟨e⟩⟩ := hSC'
  have h2n : 1 ≤ 2 * n := by omega
  have hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 (2 * n) K :=
    CFSG.RankThree.PartOne.KFU.unitaryFieldData_two hK h2n
  have hq : 2 ^ (2 * n) % 3 = 1 := by
    rw [pow_mul]
    rw [Nat.pow_mod]
    norm_num
  have hN : ¬ 3 ∣ Nat.card ((StatedScalars (Fin 3) K).subgroupOf
      (StatedSU 3 (2 ^ (2 * n)) K)) := by
    rw [(CFSG.LinearGroups.unitary_scalar_kernel Nat.prime_two hK (n := 3)
      (by norm_num)).2.2]
    intro h
    have hdvd : 3 ∣ 2 ^ (2 * n) + 1 := h.trans (Nat.gcd_dvd_right 3 _)
    have hmod : (2 ^ (2 * n) + 1) % 3 = 2 := by
      rw [Nat.add_mod, hq]
    rw [Nat.dvd_iff_mod_eq_zero] at hdvd
    omega
  have hupper : CFSG.Open.pRank 3 (⊤ : Subgroup
      (StatedProj (StatedSU 3 (2 ^ (2 * n)) K))) ≤ 1 := by
    rw [← CFSG.SectionRank.pRank_eq_open_pRank_top]
    rw [CFSG.GroupTheory.PRankCoprimeQuotient.pRank_quotient_eq_of_not_dvd
      Nat.prime_three _ hN]
    exact CFSG.RankThree.PartTwo.Sec4.Res417Four.pRank_statedSU_three_le_one hU hq
  have htrans : CFSG.Open.pRank 3 (⊤ : Subgroup X) =
      CFSG.Open.pRank 3 (⊤ : Subgroup
        (StatedProj (StatedSU 3 (2 ^ (2 * n)) K))) :=
    CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) e
  have h3dvd : 3 ∣ Nat.card X :=
    CFSG.Quasithin.F134.three_dvd_card_of_statedPSU_three hSC
  have hlower : 1 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) := by
    by_contra h
    have h0 : CFSG.Open.pRank 3 (⊤ : Subgroup X) = 0 := by omega
    have hnot : ¬ 3 ∣ Nat.card X := by
      have := CFSG.GroupTheory.not_dvd_card_of_pRank_eq_zero Nat.prime_three h0
      simpa using this
    exact hnot h3dvd
  have hlower' : 1 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup
      (StatedProj (StatedSU 3 (2 ^ (2 * n)) K))) := htrans ▸ hlower
  rw [htrans]
  omega

theorem kU34Data_twoRank :
    ∀ (X : Type) [Group X] [Finite X], IsU3 X 2 →
      CFSG.pRank 2 ↥(⊤ : Subgroup X) = 2 := by
  intro X _ _ hX
  have hSC : CFSG.Open.StatedClassicalModel X .PSU 3 2 2 :=
    CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero (by norm_num) hX
  have hSC' := hSC
  have hbr2 : CFSG.pRank 2 ↥(⊤ : Subgroup X) = CFSG.Open.pRank 2 (⊤ : Subgroup X) :=
    (CFSG.SectionRank.pRank_eq_open_pRank_top 2 ↥(⊤ : Subgroup X)).trans
      (CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := 2) (⊤ : Subgroup X)).symm
  rw [hbr2]
  apply le_antisymm
  · simpa [CFSG.Open.twoRank] using
      CFSG.GH74.SmallRanks.twoRank_le_two_of_statedClassicalModel_PSU_three_four hSC'
  · obtain ⟨U⟩ := (inferInstance : Nonempty (Sylow 2 X))
    obtain ⟨hUcard, hZcard, hZsq⟩ :=
      CFSG.RankTwoShapes.unitaryFour_sylow_card hSC' U
    haveI hZcomm : IsMulCommutative ↥(Subgroup.center (U : Subgroup X)) :=
      Subgroup.center.isMulCommutative (G := ↥(U : Subgroup X))
    have hEA : CFSG.Open.IsElemAbelian 2 (Subgroup.center (U : Subgroup X)) :=
      ⟨hZcomm, fun z hz => hZsq z hz⟩
    have hEAcard : Nat.card ((Subgroup.center (U : Subgroup X)).map
        (U : Subgroup X).subtype) = 2 ^ 2 := by
      rw [Subgroup.card_map_of_injective (U : Subgroup X).subtype_injective, hZcard]
      norm_num
    have := CFSG.SectionRank.le_pRank (p := 2) (by norm_num)
      (E := (Subgroup.center (U : Subgroup X)).map (U : Subgroup X).subtype) le_top
      (CFSG.SectionRank.isElemAbelian_map hEA (U : Subgroup X).subtype) hEAcard
    simpa using this

theorem kU34Data_fiveRank :
    ∀ (X : Type) [Group X] [Finite X], IsU3 X 2 →
      CFSG.pRank 5 ↥(⊤ : Subgroup X) = 2 := by
  intro X _ _ hX
  have hSC : CFSG.Open.StatedClassicalModel X .PSU 3 2 2 :=
    CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero (by norm_num) hX
  have hSC' := hSC
  have hcard : Nat.card X = 62400 :=
    CFSG.Open.StatedAPI.card_of_statedClassicalModel_psu_three_four hSC
  have hbr5 : CFSG.pRank 5 ↥(⊤ : Subgroup X) = CFSG.Open.pRank 5 (⊤ : Subgroup X) :=
    (CFSG.SectionRank.pRank_eq_open_pRank_top 5 ↥(⊤ : Subgroup X)).trans
      (CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := 5) (⊤ : Subgroup X)).symm
  rw [hbr5]
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  apply le_antisymm
  ·
    refine CFSG.SectionRank.pRank_le (p := 5) (H := (⊤ : Subgroup X)) Nat.prime_five.one_lt
      (fun E _ hE => ?_)
    have h5E : IsPGroup 5 E := fun x => ⟨1, by rw [pow_one]; exact Subtype.ext (hE.2 x x.2)⟩
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp h5E
    rw [hm]
    by_contra h
    push Not at h
    have hdvd : 5 ^ 3 ∣ Nat.card X := by
      have hm3 : 3 ≤ m := by
        have := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 5)).mp h
        omega
      have h1 : 5 ^ 3 ∣ Nat.card E := by
        rw [hm]
        exact pow_dvd_pow 5 hm3
      have h2 : Nat.card E ∣ Nat.card X := Subgroup.card_subgroup_dvd_card E
      exact h1.trans h2
    rw [hcard] at hdvd
    norm_num at hdvd
  ·
    obtain ⟨x, y, hx5, hy5, hxy, hx1, hxy'⟩ := CFSG.Quasithin.SBd10.exists_two_five_u34 hSC'
    have hxord : orderOf x = 5 := by
      rcases (Nat.dvd_prime Nat.prime_five).mp (orderOf_dvd_of_pow_eq_one hx5) with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) hx1
      · exact h
    have hy1 : y ≠ 1 := fun h => hxy' 0 (by rw [pow_zero]; exact h.symm)
    have hyord : orderOf y = 5 := by
      rcases (Nat.dvd_prime Nat.prime_five).mp (orderOf_dvd_of_pow_eq_one hy5) with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) hy1
      · exact h
    have hx5z : x ^ (5 : ℤ) = 1 := by
      rw [show (5 : ℤ) = (5 : ℕ) by norm_num, zpow_natCast, hx5]
    have hyx : y ∉ Subgroup.zpowers x := by
      intro hy
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hy
      have hcast : ((k % 5).toNat : ℤ) = k % 5 :=
        Int.toNat_of_nonneg (Int.emod_nonneg k (by norm_num : (5 : ℤ) ≠ 0))
      have hk5 : x ^ k = x ^ ((k % 5).toNat : ℤ) := by
        rw [zpow_eq_zpow_emod' k hx5, hcast]
        norm_num
      have hk' : y = x ^ (k % 5).toNat := by
        rw [← hk, hk5, zpow_natCast]
      exact hxy' (k % 5).toNat hk'.symm
    have hcommxy : Commute x y := hxy
    obtain ⟨hEA, hEcard⟩ :=
      CFSG.GroupTheory.isElemAbelian_sup_zpowers_of_commute
        (r := 5) (X := Subgroup.zpowers x) (by rw [Nat.card_zpowers, hxord])
        (v := y) hyord hyx (fun a ha => by
          obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
          exact (hcommxy.zpow_left n).eq)
    have h25 : Nat.card (Subgroup.zpowers x ⊔ Subgroup.zpowers y : Subgroup X) = 5 ^ 2 := by
      rw [hEcard]
    have := CFSG.SectionRank.le_pRank (p := 5) (by norm_num)
      (E := Subgroup.zpowers x ⊔ Subgroup.zpowers y) le_top hEA h25
    simpa using this

theorem kU34Data_holds : KU34Data := by
  intro X _ _ hX
  have hSC : CFSG.Open.StatedClassicalModel X .PSU 3 2 2 :=
    CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero (by norm_num) hX
  have hcard : Nat.card X = 62400 :=
    CFSG.Open.StatedAPI.card_of_statedClassicalModel_psu_three_four hSC
  have hbr3 : CFSG.pRank 3 ↥(⊤ : Subgroup X) = CFSG.Open.pRank 3 (⊤ : Subgroup X) :=
    (CFSG.SectionRank.pRank_eq_open_pRank_top 3 ↥(⊤ : Subgroup X)).trans
      (CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := 3) (⊤ : Subgroup X)).symm
  have hbr13 : CFSG.pRank 13 ↥(⊤ : Subgroup X) = CFSG.Open.pRank 13 (⊤ : Subgroup X) :=
    (CFSG.SectionRank.pRank_eq_open_pRank_top 13 ↥(⊤ : Subgroup X)).trans
      (CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := 13) (⊤ : Subgroup X)).symm
  refine ⟨?_, kU34Data_twoRank X hX, ?_, kU34Data_fiveRank X hX, ?_⟩
  · rw [hcard]
    norm_num
  · rw [hbr3]
    apply le_antisymm
    · exact CFSG.QuasithinUnique.Id2519.pRank_le_one_of_not_sq_dvd Nat.prime_three
        (by rw [hcard]; norm_num)
    · by_contra h
      have h0 : CFSG.Open.pRank 3 (⊤ : Subgroup X) = 0 :=
        Nat.lt_one_iff.mp (Nat.lt_of_not_le h)
      have h3 : 3 ∣ Nat.card X := by rw [hcard]; norm_num
      have hnot : ¬ 3 ∣ Nat.card X := by
        have := CFSG.GroupTheory.not_dvd_card_of_pRank_eq_zero Nat.prime_three h0
        simpa using this
      exact hnot h3
  · rw [hbr13]
    apply le_antisymm
    · exact CFSG.QuasithinUnique.Id2519.pRank_le_one_of_not_sq_dvd (by norm_num : Nat.Prime 13)
        (by rw [hcard]; norm_num)
    · by_contra h
      have h0 : CFSG.Open.pRank 13 (⊤ : Subgroup X) = 0 :=
        Nat.lt_one_iff.mp (Nat.lt_of_not_le h)
      have h13 : 13 ∣ Nat.card X := by rw [hcard]; norm_num
      have hnot : ¬ 13 ∣ Nat.card X := by
        have := CFSG.GroupTheory.not_dvd_card_of_pRank_eq_zero (by norm_num : Nat.Prime 13) h0
        simpa using this
      exact hnot h13

theorem kU5OddTorusRank_lower :
    ∀ (X : Type) [Group X] [Finite X] (n s : ℕ), IsU5 X n → s.Prime → s ∣ 2 ^ n + 1 →
      (s = 5 ∧ ¬ 25 ∣ 2 ^ n + 1 →
        3 ≤ CFSG.pRank 5 ↥(⊤ : Subgroup X)) ∧
      (¬ (s = 5 ∧ ¬ 25 ∣ 2 ^ n + 1) → 3 < CFSG.pRank s ↥(⊤ : Subgroup X)) := by
  intro X _ _ n s hX hs hdvd
  have hSC : CFSG.Open.StatedClassicalModel X .PSU 5 2 n :=
    CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero
      (by have := hX.admissible.2.1; omega) hX
  have hSC' := hSC
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hSC'
  have hn1 : 1 ≤ n := hX.admissible.2.1
  have hq1 : 1 ≤ 2 ^ n := Nat.one_le_pow _ _ (by norm_num)
  have hq0 : 2 ^ n ≠ 0 := by positivity
  have hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 n K :=
    CFSG.RankThree.PartOne.KFU.unitaryFieldData_two hK hn1
  have hD : Nat.card ((StatedScalars (Fin 5) K).subgroupOf (StatedSU 5 (2 ^ n) K)) =
      Nat.gcd 5 (2 ^ n + 1) :=
    (CFSG.LinearGroups.unitary_scalar_kernel Nat.prime_two hK (n := 5) (by norm_num)).2.2
  have htrans : CFSG.Open.pRank s (⊤ : Subgroup X) =
      CFSG.Open.pRank s (⊤ : Subgroup (StatedProj (StatedSU 5 (2 ^ n) K))) :=
    CFSG.SectionRank.pRank_top_eq_of_mulEquiv
      (by have := hs.two_le; omega) e
  have hbr (r : ℕ) : CFSG.pRank r ↥(⊤ : Subgroup X) =
      CFSG.Open.pRank r (⊤ : Subgroup X) :=
    (CFSG.SectionRank.pRank_eq_open_pRank_top r ↥(⊤ : Subgroup X)).trans
      (CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := r) (⊤ : Subgroup X)).symm
  have hlower := fun r (hr : r.Prime) (hr2 : r ≠ 2) (hrd : r ∣ 2 ^ n + 1)
      (hrC : ¬ r ∣ Nat.card ((StatedScalars (Fin 5) K).subgroupOf
        (StatedSU 5 (2 ^ n) K))) => by
    haveI : Fact r.Prime := ⟨hr⟩
    exact (CFSG.SectionRank.OddCover.scalar_quotient_diagonal_torus_rank
      (p := 2) (f := n) (n := 5) (r := r) Nat.prime_two (by norm_num) hr2
      (Or.inr ⟨hK, rfl, hrd⟩)
      ((StatedScalars (Fin 5) K).subgroupOf (StatedSU 5 (2 ^ n) K)) le_rfl).2 hrC
  have hlower3 := fun r (hr : r.Prime) (hr2 : r ≠ 2) (hrd : r ∣ 2 ^ n + 1) => by
    haveI : Fact r.Prime := ⟨hr⟩
    exact (CFSG.SectionRank.OddCover.scalar_quotient_diagonal_torus_rank
      (p := 2) (f := n) (n := 5) (r := r) Nat.prime_two (by norm_num) hr2
      (Or.inr ⟨hK, rfl, hrd⟩)
      ((StatedScalars (Fin 5) K).subgroupOf (StatedSU 5 (2 ^ n) K)) le_rfl).1
  constructor
  · rintro ⟨rfl, h25⟩
    have h3 := hlower3 5 Nat.prime_five (by norm_num) hdvd
    rw [hbr 5, htrans]
    omega
  · intro hnot
    by_cases hs5 : s = 5
    · subst hs5
      have h25 : 25 ∣ 2 ^ n + 1 := by
        by_contra h
        exact hnot ⟨rfl, h⟩
      have h25K : 25 ∣ Nat.card Kˣ := by
        rw [Nat.card_units, hK, CFSG.SectionRank.OddCover.sq_sub_one_eq hq1]
        exact h25.trans (dvd_mul_right _ _)
      obtain ⟨ζ, hζ⟩ := CFSG.LocalAnalysis.UniquenessCase.UCK.OutP.exists_orderOf_eq_of_dvd h25K
      have hH : ∀ u : Fin 5 → Kˣ, (∀ i, u i ∈ Subgroup.zpowers ζ) → ∏ i, u i = 1 →
          CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureHeis.diagGL 5 u ∈
            StatedSU 5 (2 ^ n) K := by
        intro u hu hprod
        have hdet : ((CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureHeis.diagGL 5 u :
            GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K).det = 1 := by
          rw [CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureHeis.det_diagGL,
            ← Units.coe_prod, hprod, Units.val_one]
        let A : Matrix (Fin 5) (Fin 5) K :=
          ((CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureHeis.diagGL 5 u :
            GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K)
        have hA : A = Matrix.diagonal (fun i => (u i : K)) := by
          rw [show A = ((CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureHeis.diagGL 5 u :
            GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) from rfl,
            CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureHeis.coe_diagGL]
        have hunit : Matrix.transpose (A.map (fun x : K => x ^ (2 ^ n))) * A = 1 := by
          rw [hA, Matrix.diagonal_map (by simp [zero_pow hq0]), Matrix.diagonal_transpose,
            Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
          congr 1
          funext i
          have hui : (u i) ^ (2 ^ n + 1) = 1 := by
            rw [← orderOf_dvd_iff_pow_eq_one]
            exact (orderOf_dvd_of_mem_zpowers (hu i)).trans (by rw [hζ]; exact h25)
          rw [← pow_succ]
          simpa using congrArg Units.val hui
        unfold StatedSU
        exact Subgroup.subset_closure ⟨hdet, hunit⟩
      have h4 := CFSG.LocalAnalysis.UniquenessCase.UCK.OutP.four_le_pRank_projFive hζ
        (StatedSU 5 (2 ^ n) K) hH
      rw [hbr 5, htrans]
      omega
    · have hC : ¬ s ∣ Nat.card ((StatedScalars (Fin 5) K).subgroupOf
          (StatedSU 5 (2 ^ n) K)) := by
        rw [hD]
        intro h
        have h5 : s ∣ 5 := h.trans (Nat.gcd_dvd_left _ _)
        rcases (Nat.dvd_prime Nat.prime_five).mp h5 with h1 | h5'
        · exact hs.ne_one h1
        · exact hs5 h5'
      have h4 := hlower s hs (by
        intro h2
        subst h2
        have h2n : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega : n ≠ 0)
        exact (by norm_num : ¬ 2 ∣ 1) ((Nat.dvd_add_right h2n).mp hdvd)) hdvd hC
      rw [hbr s, htrans]
      omega

theorem kU5OddTorusRank_holds :
    ∀ (X : Type) [Group X] [Finite X] (n s : ℕ), IsU5 X n → s.Prime → s ∣ 2 ^ n + 1 →
      (s = 5 ∧ ¬ 25 ∣ 2 ^ n + 1 → pRank 5 (⊤ : Subgroup X) = 3) ∧
        (¬ (s = 5 ∧ ¬ 25 ∣ 2 ^ n + 1) → 3 < pRank s (⊤ : Subgroup X)) := by
  intro X _ _ n s hX hs hdvd
  obtain ⟨hlow1, hlow2⟩ := kU5OddTorusRank_lower X n s hX hs hdvd
  have hSC : CFSG.Open.StatedClassicalModel X .PSU 5 2 n :=
    CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero
      (by have := hX.admissible.2.1; omega) hX
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hSC
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have htrans : CFSG.Open.pRank 5 (⊤ : Subgroup X) =
      CFSG.Open.pRank 5 (⊤ : Subgroup (StatedProj (StatedSU 5 (2 ^ n) K))) :=
    CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) e
  have hbr (r : ℕ) : CFSG.pRank r ↥(⊤ : Subgroup X) =
      CFSG.Open.pRank r (⊤ : Subgroup X) :=
    (CFSG.SectionRank.pRank_eq_open_pRank_top r ↥(⊤ : Subgroup X)).trans
      (CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := r) (⊤ : Subgroup X)).symm
  refine ⟨?_, hlow2⟩
  rintro ⟨rfl, h25⟩
  apply le_antisymm
  ·
    have hF : Fintype.card K = (2 ^ n) ^ 2 := by
      rw [← Nat.card_eq_fintype_card]
      exact hK
    have hpv : padicValNat 5 (2 ^ n + 1) = 1 := by
      apply le_antisymm
      · by_contra h
        have h2 : 2 ≤ padicValNat 5 (2 ^ n + 1) := by omega
        exact h25 ((padicValNat_dvd_iff_le (by omega : 2 ^ n + 1 ≠ 0)).mpr h2)
      · exact one_le_padicValNat_of_dvd (by omega) hdvd
    have hcalc : CFSG.Open.pRank 5 (⊤ : Subgroup
        (StatedProj (StatedSU 5 (2 ^ n) K))) = 3 := by
      have h := CFSG.LocalAnalysis.RankThreeUC.S15.uniCoreMatrix K (2 ^ n) 5 5
        Nat.prime_five (by norm_num) hF hdvd (by norm_num) (by norm_num) (by omega)
        ((StatedScalars (Fin 5) K).subgroupOf (StatedSU 5 (2 ^ n) K)) le_rfl
      rw [if_pos] at h
      · simpa using h
      · refine ⟨rfl, by norm_num, ?_⟩
        rw [hpv, padicValNat_self]
    rw [hbr 5, htrans]
    omega
  · exact hlow1 ⟨rfl, h25⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

end
