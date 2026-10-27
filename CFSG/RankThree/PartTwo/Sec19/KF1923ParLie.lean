module

public import CFSG.RankThree.PartTwo.Sec19.Item1923KFParSolv
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K21dTitsModels

public section

namespace CFSG.RankThree.PartTwo.Late

open CFSG.RankThree.PartTwo
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)

private theorem kfParLie_sylowTwoOf {X : Type} [Group X] [Finite X] {T : Subgroup X}
    (hT : IsSylowOf 2 T ⊤) : CFSG.QuasithinUnique.IsSylowTwoOf T ⊤ := by
  obtain ⟨h1, h2, h3⟩ := (CFSG.ABGLocalTools.isSylowOf_iff).1 hT
  exact ⟨h1, h2, h3⟩

private theorem kfParLie_solvOver_sl3 {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK4 : ∃ s : Finset K, s.card = 4) :
    CFSG.Quasithin.H13.NQCat.SolvOver (Matrix.SpecialLinearGroup (Fin 3) K)
      (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.unitriangular 3 K) := by
  intro A hUA hA
  rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.normalizer_unitriangular]
  exact CFSG.Quasithin.H13.NQCat.SL3.le_upperTriangular_of_isSolvable hK4 hUA hA

private theorem kfParLie_solvOver_sl3_iso {X : Type} [Group X] [Finite X] {n : ℕ} (hn : 2 ≤ n)
    (e : X ≃* Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 n)) {U : Subgroup X}
    (hU : CFSG.QuasithinUnique.IsSylowTwoOf U ⊤) :
    CFSG.Quasithin.H13.NQCat.SolvOver X U := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK4 := CFSG.Quasithin.H13.NQCat.exists_finset_card_four_of_card hn
    (GaloisField.card 2 n (by omega))
  obtain ⟨P, hP⟩ := CFSG.LocalAnalysis.ComponentInitial.LinearFlag.exists_sylow_unitriangular
    (K := GaloisField 2 n) 2 (n := 3) (by norm_num)
  have hU₀ : CFSG.QuasithinUnique.IsSylowTwoOf
      (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.unitriangular 3 (GaloisField 2 n)) ⊤ :=
    hP ▸ CFSG.QuasithinUnique.isSylowTwoOf_top_of_sylow P
  exact CFSG.Quasithin.H13.NQCat.solvOver_of_sylow (kfParLie_solvOver_sl3 hK4) hU₀ e.symm hU

private theorem kfParLie_solvOver_psl {X : Type} [Group X] [Finite X] {m n : ℕ} (hm : 2 ≤ m)
    (hn : 2 ≤ n) (e : X ≃* projSL m (GaloisField 2 n)) {U : Subgroup X}
    (hU : CFSG.QuasithinUnique.IsSylowTwoOf U ⊤) :
    CFSG.Quasithin.H13.NQCat.SolvOver X U := by
  have h4 : 4 ≤ 2 ^ n :=
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hmodel : CFSG.Open.StatedClassicalModel X .PSL m 2 n := by
    refine ⟨⟨Nat.prime_two, by omega, hm, ?_, ?_⟩, GaloisField 2 n, inferInstance, inferInstance,
      GaloisField.card 2 n (by omega),
      ⟨e.trans (CFSG.PGLModel.projSLEquivStatedProj m (GaloisField 2 n))⟩⟩
    · intro h
      simp only [Prod.mk.injEq] at h
      omega
    · intro h
      simp only [Prod.mk.injEq] at h
      omega
  exact CFSG.LocalAnalysis.RankThreeUC.S15.K21dTitsProof.solvOver_of_model_psl hn hmodel hU

private theorem kfParLie_solvOver_psp {X : Type} [Group X] [Finite X] {n : ℕ} (hn : 2 ≤ n)
    (e : X ≃* projSp 2 (GaloisField 2 n)) {U : Subgroup X}
    (hU : CFSG.QuasithinUnique.IsSylowTwoOf U ⊤) :
    CFSG.Quasithin.H13.NQCat.SolvOver X U := by
  have h4 : 4 ≤ 2 ^ n :=
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hmodel : CFSG.Open.StatedClassicalModel X .PSp 2 2 n := by
    refine ⟨⟨Nat.prime_two, by omega, le_rfl, ?_⟩, GaloisField 2 n, inferInstance, inferInstance,
      GaloisField.card 2 n (by omega),
      ⟨e.trans (CFSG.PGLModel.projSpEquivStatedProj 2 (GaloisField 2 n))⟩⟩
    intro h
    simp only [Prod.mk.injEq] at h
    omega
  exact CFSG.LocalAnalysis.RankThreeUC.S15.K21dTitsProof.solvOver_of_model_psp hn hmodel hU

private theorem kfParLie_solvOver_psu {X : Type} [Group X] [Finite X]
    (e : X ≃* projSU 4 2 3) {U : Subgroup X}
    (hU : CFSG.QuasithinUnique.IsSylowTwoOf U ⊤) :
    CFSG.Quasithin.H13.NQCat.SolvOver X U := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmodel : CFSG.Open.StatedClassicalModel X .PSU 4 2 3 := by
    refine ⟨⟨Nat.prime_two, by norm_num, by norm_num, by norm_num⟩, GaloisField 2 (2 * 3),
      inferInstance, inferInstance, ?_,
      ⟨e.trans (CFSG.PGLModel.projSUEquivStatedProj 4 2 3)⟩⟩
    rw [GaloisField.card 2 (2 * 3) (by norm_num)]
    norm_num
  exact CFSG.LocalAnalysis.RankThreeUC.S15.K21dTitsProof.solvOver_of_model_psu (by norm_num)
    hmodel hU

private theorem kfParLie_solvOver_g2
    {X : Type} [Group X] [Finite X] {n : ℕ} (hn : 2 ≤ n)
    (hX : Sec8.IsoGTwoEven X n) {U : Subgroup X}
    (hU : CFSG.QuasithinUnique.IsSylowTwoOf U ⊤) :
    CFSG.Quasithin.H13.NQCat.SolvOver X U := by
  obtain ⟨K, hF, hFin, hcard, ⟨e⟩⟩ := hX
  have h4 : 4 ≤ 2 ^ n :=
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hZ := CFSG.LieType.Chevalley.center_adjointGroup_eq_bot (τ := .G2) (K := K)
  have hG2 : CFSG.Quasithin.IsG2 2 n X :=
    ⟨⟨Nat.prime_two, by omega, rfl, by omega⟩, K, hF, hFin, hcard,
      ⟨e.trans (((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm)⟩⟩
  exact CFSG.Quasithin.H13.NQCat.BN.solvOver_of_isG2 hn hG2 hU

theorem kfPar_lie_q4
    {X : Type} [Group X] [Finite X]
    (hX : (∃ n : ℕ, 2 ≤ n ∧
        (Nonempty (X ≃* Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 n)) ∨
          Nonempty (X ≃* projSL 3 (GaloisField 2 n)) ∨
          Nonempty (X ≃* projSp 2 (GaloisField 2 n)) ∨ Sec8.IsoGTwoEven X n)) ∨
      Nonempty (X ≃* projSL 4 (GaloisField 2 2)) ∨ Nonempty (X ≃* projSU 4 2 3)) :
    NoInvertingInParabolic X ∧ NoSquareInvertingInParabolic X := by
  refine noInverting_of_solvOver (fun T D hT hTD hD => ?_)
  have hU := kfParLie_sylowTwoOf hT
  have hS : CFSG.Quasithin.H13.NQCat.SolvOver X T := by
    rcases hX with ⟨n, hn, hfam⟩ | hfam | hfam
    · rcases hfam with hSL | hPSL | hPSp | hG2
      · obtain ⟨e⟩ := hSL
        exact kfParLie_solvOver_sl3_iso hn e hU
      · obtain ⟨e⟩ := hPSL
        exact kfParLie_solvOver_psl (m := 3) (by norm_num) hn e hU
      · obtain ⟨e⟩ := hPSp
        exact kfParLie_solvOver_psp hn e hU
      · exact kfParLie_solvOver_g2 hn hG2 hU
    · obtain ⟨e⟩ := hfam
      exact kfParLie_solvOver_psl (m := 4) (by norm_num) (by norm_num) e hU
    · obtain ⟨e⟩ := hfam
      exact kfParLie_solvOver_psu e hU
  exact hS D hTD hD

end CFSG.RankThree.PartTwo.Late
