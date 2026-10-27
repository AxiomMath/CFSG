module

public import CFSG.RankThree.PartTwo.Sec21.Hering214EK0Gen
public import CFSG.LieType.Steinberg.CentralExt.GriessNativeModels
public import CFSG.Models.PGL
public import CFSG.Sporadic.Recognition.M23MultiplierCert
public import CFSG.Sporadic.Recognition.HeMultiplierCert
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.TrivialRows
public import CFSG.RankThree.PartTwo.Sec21.Item22Res3ProofTheta
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011LabUniq2
public import CFSG.Quasithin.Vol2.Ch5Assembly
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.RankThree.PartTwo.Sec21.Hering214Even

open CFSG.Assembly.LowTwoRank CFSG.Blueprint.Multiplier CFSG.RankThree.PerfectCover
open CFSG.Assembly.RankThreeEven (projSp projSU)
open CFSG.Open CFSG.Blueprint

section Certificates


theorem multiplierOdd_M23 : MultiplierOdd ↥CFSG.Blueprint.NativeSporadic.M23 := by
  refine multiplierOdd_of_odd_hopfMultiplier ?_
  rw [← Nat.card_congr
      (hopfMultiplierEquivGriess (↥CFSG.Blueprint.NativeSporadic.M23)).toEquiv,
    CFSG.Sporadic.Recognition.M23Multiplier.card_griessHopfMultiplier_M23_of_certificate]
  exact odd_one

theorem multiplierOdd_He : MultiplierOdd CFSG.Blueprint.NativeSporadic.He := by
  refine multiplierOdd_of_odd_hopfMultiplier ?_
  rw [← Nat.card_congr (hopfMultiplierEquivGriess CFSG.Blueprint.NativeSporadic.He).toEquiv,
    CFSG.Sporadic.Recognition.HeMultiplier.card_griessHopfMultiplier_He_of_certificate]
  exact odd_one

theorem multiplierOdd_M24 : MultiplierOdd (CFSG.Blueprint.NativeSporadic.Carrier .M24) := by
  refine multiplierOdd_of_odd_hopfMultiplier ?_
  rw [CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.nativeRow_M24]
  decide

theorem multiplierOdd_J4 : MultiplierOdd (CFSG.Blueprint.NativeSporadic.Carrier .J4) := by
  refine multiplierOdd_of_odd_hopfMultiplier ?_
  rw [CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.nativeRow_J4]
  decide

theorem multiplierOdd_psl_five_two {X : Type} [Group X]
    (h : StatedClassicalModel X .PSL 5 2 1) : MultiplierOdd X := by
  refine multiplierOdd_of_odd_hopfMultiplier ?_
  rw [card_hopfMultiplier_of_row (CFSG.LieType.Steinberg.CentralExt.GriessClassical.psl_row h),
    CFSG.RankThree.PartTwo.Sec21.Item22Res3Proof.table_PSL_five_two]
  exact odd_one

theorem multiplierOdd_psu_five_two_two {X : Type} [Group X]
    (h : StatedClassicalModel X .PSU 5 2 2) : MultiplierOdd X := by
  refine multiplierOdd_of_odd_hopfMultiplier ?_
  rw [card_hopfMultiplier_of_row
      (CFSG.LieType.Steinberg.CentralExt.GriessClassical.psu_odd_row h (by decide)),
    CFSG.RankThree.PartTwo.Sec21.Item221Proof.table_PSU_five_four]
  decide

theorem multiplierOdd_psu_four_two {X : Type} [Group X] {k : ℕ} (hk : 2 ≤ k) (he : Even k)
    (h : StatedClassicalModel X .PSU 4 2 k) : MultiplierOdd X := by
  have hq : 4 ≤ 2 ^ k := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  refine multiplierOdd_of_odd_hopfMultiplier ?_
  rw [card_hopfMultiplier_of_row
    (CFSG.LieType.Steinberg.CentralExt.GriessClassical.psu_row h (by decide) (Or.inl hq))]
  have hodd : Odd (2 ^ k + 1) := (Nat.even_pow.mpr ⟨even_two, by omega⟩).add_one
  have hex : exceptionalOrders .PSU 4 2 k = (1, 1) := by
    have hkm : k % 2 = 0 := Nat.even_iff.mp he
    unfold exceptionalOrders
    split <;> first | rfl | omega
  rw [CFSG.LocalAnalysis.GLTheoremA.genericOrders_PSU, hex]
  simpa using CFSG.RankThree.PartTwo.Sec4.Census.odd_gcd_of_odd_right (m := 4) hodd

theorem multiplierOdd_psp_two_two {X : Type} [Group X] {k : ℕ} (hk : 2 ≤ k)
    (h : StatedClassicalModel X .PSp 2 2 k) : MultiplierOdd X := by
  have hq : 4 ≤ 2 ^ k := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have hq' : 5 ≤ 2 ^ k ∨ 2 ^ k = 4 ∨ (2 ^ k = 2 ∧ 4 ≤ 2) ∨ (2 ^ k = 3 ∧ 3 ≤ 2) := by
    by_cases h4 : 2 ^ k = 4
    · exact Or.inr (Or.inl h4)
    · exact Or.inl (by omega)
  refine multiplierOdd_of_odd_hopfMultiplier ?_
  rw [card_hopfMultiplier_of_row (CFSG.LieType.Steinberg.CentralExt.GriessClassical.psp_row h hq'),
    CFSG.RankThree.PartTwo.Sec21.Item221Proof.genericOrders_PSp_two (by omega),
    CFSG.RankThree.PartTwo.Sec21.Item221Proof.exceptionalOrders_PSp_two]
  decide

theorem multiplierOdd_g2 {X : Type} [Group X] {k : ℕ} (hk : 4 ≤ k)
    (h : ChevalleyExceptionalModel X .G2 2 k) : MultiplierOdd X := by
  have hq : 5 ≤ 2 ^ k := by
    calc 5 ≤ 2 ^ 4 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  refine multiplierOdd_of_odd_hopfMultiplier ?_
  rw [card_hopfMultiplier_of_row (t := .G2) (n := 0) (p := 2) (f := k)
    (CFSG.LieType.Steinberg.CentralExt.GriessNative.g2_row h hq)]
  have hg : genericOrders .G2 0 2 k = (1, 1) := rfl
  have hex : exceptionalOrders .G2 0 2 k = (1, 1) := by
    unfold exceptionalOrders
    split <;> first | rfl | simp_all | omega
  rw [hg, hex]
  decide

theorem multiplierOdd_3d4 {X : Type} [Group X] {k : ℕ}
    (h : ChevalleyExceptionalModel X .trialityD4 2 k) : MultiplierOdd X := by
  refine multiplierOdd_of_odd_hopfMultiplier ?_
  rw [card_hopfMultiplier_of_row (t := .trialityD4) (n := 0) (p := 2) (f := k)
    (CFSG.LieType.Steinberg.CentralExt.GriessNative.trialityD4_row h)]
  have hg : genericOrders .trialityD4 0 2 k = (1, 1) := rfl
  have hex : exceptionalOrders .trialityD4 0 2 k = (1, 1) := rfl
  rw [hg, hex]
  decide

theorem multiplierOdd_of_projSp {X : Type} [Group X] {k : ℕ} (hk : 2 ≤ k)
    (e : X ≃* projSp 2 (GaloisField 2 k)) : MultiplierOdd X :=
  multiplierOdd_psp_two_two hk
    (CFSG.PGLModel.statedClassicalModel_of_mulEquiv_projSp
      (CFSG.Quasithin.H13.admissible_PSp2 hk) e)

theorem multiplierOdd_of_projSU_four {X : Type} [Group X] {k : ℕ} (hk : 2 ≤ k) (he : Even k)
    (e : X ≃* projSU 4 2 k) : MultiplierOdd X :=
  multiplierOdd_psu_four_two hk he
    (CFSG.PGLModel.statedClassicalModel_of_mulEquiv_projSU
      (CFSG.Quasithin.H13.admissible_PSU4 hk) e)

theorem multiplierOdd_of_projSU_five (X : Type) [Group X] (e : X ≃* projSU 5 2 2) :
    MultiplierOdd X := by
  have hadm : StatedLieAdmissible .PSU 5 2 2 := by
    unfold StatedLieAdmissible
    refine ⟨Nat.prime_two, by omega, by norm_num, ?_⟩
    intro hc
    simp only [Prod.mk.injEq] at hc
    omega
  exact multiplierOdd_psu_five_two_two
    (CFSG.PGLModel.statedClassicalModel_of_mulEquiv_projSU hadm e)

theorem item214EvenMultOdd_of : Item214EvenMultOdd := by
  intro X _ _ h
  rcases h with hM23 | hM24 | hHe | hJ4 | hL5 | hG2 | h3D4 | hSp | hU5
  · obtain ⟨e⟩ := hM23
    intro K _ _ Z _ hK hZ hf
    obtain ⟨f⟩ := hf
    exact multiplierOdd_M23 K Z hK hZ ⟨f.trans e⟩
  · obtain ⟨e⟩ := hM24
    intro K _ _ Z _ hK hZ hf
    obtain ⟨f⟩ := hf
    exact multiplierOdd_M24 K Z hK hZ ⟨f.trans e⟩
  · obtain ⟨e⟩ := hHe
    intro K _ _ Z _ hK hZ hf
    obtain ⟨f⟩ := hf
    exact multiplierOdd_He K Z hK hZ ⟨f.trans e⟩
  · obtain ⟨e⟩ := hJ4
    intro K _ _ Z _ hK hZ hf
    obtain ⟨f⟩ := hf
    exact multiplierOdd_J4 K Z hK hZ ⟨f.trans e⟩
  · exact multiplierOdd_psl_five_two hL5
  · obtain ⟨n, hn4, -, hG2'⟩ := hG2
    exact multiplierOdd_g2 hn4 hG2'
  · obtain ⟨n, -, -, h3D4'⟩ := h3D4
    exact multiplierOdd_3d4 h3D4'
  · obtain ⟨n, hn, he, hA⟩ := hSp
    have hk : 2 ≤ n := by
      obtain ⟨m, rfl⟩ := he
      omega
    rcases hA with hA | hA
    · obtain ⟨eSp⟩ := hA
      exact multiplierOdd_of_projSp hk eSp
    · obtain ⟨eSU⟩ := hA
      exact multiplierOdd_of_projSU_four hk he eSU
  · obtain ⟨e⟩ := hU5
    exact multiplierOdd_of_projSU_five X e

end Certificates

end CFSG.RankThree.PartTwo.Sec21.Hering214Even
