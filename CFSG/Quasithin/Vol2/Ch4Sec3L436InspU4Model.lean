module

public import CFSG.Quasithin.Background.A3Structure312Defs
public import CFSG.Quasithin.Background.F420Orders
public import CFSG.LieType.Steinberg.CentralExt.SUTwo
public import CFSG.Quasithin.Background.F1Models
public import CFSG.Quasithin.H13.U4ParCore
public import CFSG.Quasithin.H13.U4ParLine
public import CFSG.Quasithin.H13.U4ParModel

public section

namespace CFSG.Quasithin.H13.Ch4.U4A

open CFSG.Quasithin CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial CFSG.Quasithin.H13.U4Par

variable {m : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 m K)

theorem point_core_centralizes_center_pCore (hm : 2 ≤ m) :
    perfectCore (parP h) ≤
      Subgroup.centralizer (centerOf (CFSG.Open.pCoreOf 2 (perfectCore (parP h))) :
        Set (hypSU h 2 0)) := by
  rw [pCoreOf_perfectCore_parP h hm, centerOf_radQ]
  exact perfectCore_parP_le_centralizer h

theorem exists_line_modO2_surjection :
    ∃ f : ModO2 (perfectCore (parP2 h)) →* Matrix.SpecialLinearGroup (Fin 2) K,
      Function.Surjective f := by
  let P := perfectCore (parP2 h)
  let ρ : ↥P →* Matrix.SpecialLinearGroup (Fin 2) K :=
    (rho2F h).comp (Subgroup.inclusion (perfectCore_parP2_le_parH2 h))
  have hρ : Function.Surjective ρ := by
    intro A
    refine ⟨⟨lev2Hom h A, lev2Hom_range_le_perfectCore h ⟨A, rfl⟩⟩, ?_⟩
    exact rho2F_lev2Hom h A
  have hk : CFSG.pCore 2 ↥P ≤ ρ.ker := by
    intro g hg
    have hgO : (g : hypSU h 2 0) ∈ CFSG.Open.pCoreOf 2 P := ⟨g, hg, rfl⟩
    have hgQ := pCoreOf_perfectCore_parP2_le_radQ2 h hgO
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    change rho2 h (g : hypSU h 2 0) = 1
    obtain ⟨a1, a2, a3, a4, -⟩ := hgQ
    ext i j
    fin_cases i <;> fin_cases j <;> simp [rho2, a1, a2, a3, a4]
  let f : ModO2 P →* Matrix.SpecialLinearGroup (Fin 2) K :=
    QuotientGroup.lift (CFSG.pCore 2 ↥P) ρ hk
  refine ⟨f, ?_⟩
  intro A
  obtain ⟨g, hg⟩ := hρ A
  exact ⟨QuotientGroup.mk g, hg⟩

theorem not_psl2_modO2_line (hm : 2 ≤ m)
    (hpsl : CFSG.Quasithin.IsPSL 2 2 m (ModO2 (perfectCore (parP2 h)))) : False := by
  have := h.finite
  have := CFSG.Quasithin.H13.U4Par.finite_hypSU h
  obtain ⟨f, hf⟩ := exists_line_modO2_surjection h
  have hle := Nat.card_le_card_of_surjective f hf
  have hK : Nat.card K = (2 ^ m) ^ 2 := by rw [h.card, ← pow_mul, mul_comm]
  have hq2 : (2 ^ m) ^ 2 = 4 ^ m := by
    rw [← pow_mul, mul_comm, pow_mul]
    norm_num
  rw [CFSG.LieType.Steinberg.card_specialLinearGroup_fin_two, hK,
    CFSG.Quasithin.F420.card_of_statedPSL_two_two hpsl, ← hq2] at hle
  have hq : 4 ≤ 2 ^ m :=
    (show 4 = 2 ^ 2 by norm_num).le.trans (Nat.pow_le_pow_right (by norm_num) hm)
  have hlt : 2 ^ m < (2 ^ m) ^ 2 := by nlinarith
  have hpos : 0 < (2 ^ m) ^ 2 - 1 := by
    have : 1 < (2 ^ m) ^ 2 := by nlinarith
    omega
  have hsq : (2 ^ m) ^ 2 ≤ ((2 ^ m) ^ 2) ^ 2 := by nlinarith
  have hstrict : 2 ^ m * ((2 ^ m) ^ 2 - 1) <
      (2 ^ m) ^ 2 * (((2 ^ m) ^ 2) ^ 2 - 1) :=
    (Nat.mul_lt_mul_of_pos_right hlt hpos).trans_le
      (Nat.mul_le_mul_left _ (Nat.sub_le_sub_right hsq 1))
  exact (Nat.not_lt_of_ge hle) hstrict

end CFSG.Quasithin.H13.Ch4.U4A
