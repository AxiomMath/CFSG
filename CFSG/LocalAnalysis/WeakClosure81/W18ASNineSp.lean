module

public import CFSG.LocalAnalysis.WeakClosure81.W18ASNineGap
public import CFSG.LocalAnalysis.WeakClosure81.W18ASNineT
import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotResidualHigherSLTwo

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open
open CFSG.ComponentClassification.CatLeaf (LieOrderFormulasInput lieOrderNumerator lieOrderDivisor)
open CFSG.SeitzReduction.F4Pilot (charP_two_of_natCard_eq_two_pow one_le_of_natCard_eq_two_pow)

theorem noSocle185Factor_sl2 (hO : LieOrderFormulasInput) {F : Type} [Field F] [Finite F] {n : ℕ}
    (hF : Nat.card F = 2 ^ n) : NoSocle185Factor (Matrix.SpecialLinearGroup (Fin 2) F) := by
  have hn : 1 ≤ n := one_le_of_natCard_eq_two_pow hF
  haveI : CharP F 2 := charP_two_of_natCard_eq_two_pow hF
  have hcard : Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) =
      lieOrderNumerator .PSL 2 (2 ^ n) := by
    rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (by norm_num), hF]
    rfl
  rcases (by omega : n = 1 ∨ 2 ≤ n) with rfl | hn2
  · refine NoSocle185Factor.of_not_dvd fun T _ hT hd => ?_
    have h6 : Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) = 6 := by
      rw [hcard]
      simp [lieOrderNumerator]
    rw [h6] at hd
    have := Nat.le_of_dvd (by norm_num) hd
    have := (hT.card_facts hO).1
    omega
  · have h4 : 4 ≤ Nat.card F := by
      rw [hF]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
    haveI : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) F) :=
      CFSG.RankThree.PartOne.KCRootAxis.sl2_isSimpleGroup h4
    refine NoSocle185Factor.of_isSimpleGroup fun T _ hT => ⟨fun e => ?_⟩
    have hadm : StatedLieAdmissible .PSL 2 2 n :=
      ⟨Nat.prime_two, hn, le_rfl, fun h => by simp at h; omega, fun h => by simp at h; omega⟩
    have hM : Nat.card T * lieOrderDivisor .PSL 2 (2 ^ n) = lieOrderNumerator .PSL 2 (2 ^ n) := by
      rw [lieOrderDivisor_psl_two_two_pow hn, mul_one, ← Nat.card_congr e.toEquiv, hcard]
    rcases hT.crossChar hO hadm hM with ⟨-, -, h2⟩ | ⟨-, h3, -⟩ | ⟨h1, -⟩
    · subst h2
      have : Nat.card T = 60 := by
        rw [← Nat.card_congr e.toEquiv, hcard]
        simp [lieOrderNumerator]
      have := (hT.card_facts hO).1
      omega
    · omega
    · exact absurd h1 (by decide)

theorem noSocle185Factor_statedSp (hO : LieOrderFormulasInput) (k : ℕ) {F : Type} [Field F]
    [Finite F] {n : ℕ} (hF : Nat.card F = 2 ^ n) : NoSocle185Factor ↥(StatedSp k F) := by
  have hn : 1 ≤ n := one_le_of_natCard_eq_two_pow hF
  haveI : CharP F 2 := charP_two_of_natCard_eq_two_pow hF
  rcases (by omega : k = 0 ∨ k = 1 ∨ 2 ≤ k) with rfl | rfl | hk
  · refine NoSocle185Factor.of_commute fun a b => ?_
    exact Subtype.ext (Units.ext (Matrix.ext fun i => isEmptyElim i))
  · exact (noSocle185Factor_sl2 hO hF).of_mulEquiv
      ((CFSG.SeitzReduction.OmegaPilot.spProjEquivCharTwo F 1).symm.trans
        (CFSG.SeitzReduction.OmegaPilot.spOneEquiv F)).symm
  · by_cases h22 : k = 2 ∧ n = 1
    · obtain ⟨rfl, rfl⟩ := h22
      refine NoSocle185Factor.of_not_dvd fun T _ hT hd => ?_
      have : Nat.card ↥(StatedSp 2 F) = 720 := by
        rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp_two, hF]
        norm_num
      rw [this] at hd
      exact (hT.card_facts hO).2.1 hd
    · have hadm : StatedLieAdmissible .PSp k 2 n := by
        refine ⟨Nat.prime_two, hn, hk, fun h => h22 ?_⟩
        obtain ⟨h1, h2⟩ := Prod.mk.inj h
        refine ⟨h1, ?_⟩
        have : 2 ^ n = 2 ^ 1 := by omega
        exact Nat.pow_right_injective le_rfl this
      have hmodel : StatedClassicalModel (StatedProj (StatedSp k F)) .PSp k 2 n :=
        ⟨hadm, F, inferInstance, inferInstance, hF, ⟨MulEquiv.refl _⟩⟩
      haveI : IsSimpleGroup (StatedProj (StatedSp k F)) :=
        CFSG.ClassicalGroups.Symplectic.isSimpleGroup_of_statedClassicalModel_PSp _ k 2 n hmodel
      haveI : IsSimpleGroup ↥(StatedSp k F) :=
        (CFSG.SeitzReduction.OmegaPilot.spProjEquivCharTwo F k).symm.isSimpleGroup
      refine NoSocle185Factor.of_isSimpleGroup fun T _ hT => ⟨fun e => ?_⟩
      have hM : Nat.card T * lieOrderDivisor .PSp k (2 ^ n) = lieOrderNumerator .PSp k (2 ^ n) := by
        rw [lieOrderDivisor_psp_two_pow k hn, mul_one, ← Nat.card_congr e.toEquiv,
          CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp, hF]
        rfl
      rcases hT.crossChar hO hadm hM with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> exact absurd h (by decide)

theorem noSocle185Factor_of_isSpGp (hO : LieOrderFormulasInput) {Y : Type} [Group Y] {m n : ℕ}
    (h : IsSpGp Y m n) : NoSocle185Factor Y := by
  obtain ⟨k, -, F, _, _, hF, ⟨e⟩⟩ := h
  exact (noSocle185Factor_statedSp hO k hF).of_mulEquiv e.symm

end CFSG.LocalAnalysis.WeakClosure81

end
