module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeLinDefs
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeUniModel
import CFSG.Assembly.GL83StatedBridge
import CFSG.LocalAnalysis.StandardType.GGLinearFusionSURepairBlock

public section

namespace CFSG.StandardType.TablePThreeKG

open CFSG CFSG.Assembly

private theorem uniPSU2_scalars_subgroupOf_suTwo_eq_bot {K : Type} [Field K] [Finite K] [CharP K 2]
    {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 2) :
    (LargeEvenScalars (Fin 2) K).subgroupOf (LargeEvenSUGroup (Fin 2) K (2 ^ f)) = ⊥ := by
  have hcard : Nat.card ((LargeEvenScalars (Fin 2) K).subgroupOf
      (LargeEvenSUGroup (Fin 2) K (2 ^ f))) = 1 := by
    rw [CFSG.Assembly.largeEvenSUGroup_eq_statedSU,
      CFSG.Assembly.largeEvenScalars_eq_statedScalars,
      (CFSG.LinearGroups.unitary_scalar_kernel (K := K) (p := 2) (f := f) Nat.prime_two hK
        (n := 2) (by norm_num)).2.2]
    have hodd : Odd (2 ^ f + 1) := by
      have h2 : Even (2 : ℕ) := by norm_num
      exact (h2.pow_of_ne_zero (n := f) (by omega)).add_one
    exact Nat.coprime_two_left.mpr hodd
  exact Subgroup.card_eq_one.mp hcard

private theorem uniPSU2_scalars_subgroupOf_slTwo_eq_bot {F : Type} [Field F] [CharP F 2] :
    (LargeEvenScalars (Fin 2) F).subgroupOf (LargeEvenSLGroup (Fin 2) F) = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  rw [Subgroup.mem_subgroupOf] at hg
  obtain ⟨c, hc⟩ := hg
  have hdet : Matrix.GeneralLinearGroup.det (g : Matrix.GeneralLinearGroup (Fin 2) F) = 1 := g.2
  rw [← hc, Matrix.GeneralLinearGroup.det_scalar] at hdet
  simp only [Fintype.card_fin] at hdet
  have h1 : (c : F) ^ 2 = 1 := by simpa using congrArg Units.val hdet
  have h2 : ((c : F) - 1) ^ 2 = 0 := by
    have : ((c : F) - 1) ^ 2 = (c : F) ^ 2 - 2 * c + 1 := by ring
    have two0 : (2 : F) = 0 := by exact_mod_cast CharP.cast_eq_zero F 2
    rw [this, h1, two0]
    linear_combination two0
  have h3 : (c : F) = 1 := sub_eq_zero.mp (pow_eq_zero_iff (two_ne_zero) |>.mp h2)
  have hc1 : c = 1 := Units.ext h3
  rw [hc1, map_one] at hc
  exact Subgroup.mem_bot.mpr (Subtype.ext hc.symm)

theorem psu2_equiv_psl2 {K : Type} [Field K] [Finite K] [CharP K 2] {q : ℕ} (hK : Nat.card K = q ^ 2) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = q ∧ Nonempty (PSUg 2 K q ≃* PSLg 2 F) := by
  obtain ⟨f, hf1, hq⟩ := CFSG.AGLEmbedding.ToralCensus.exists_eq_two_pow_of_card_eq_sq hK
  subst hq
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨↥(CFSG.LieType.Steinberg.fixedSubfield K 2 f), inferInstance, inferInstance, ?_, ?_⟩
  · rw [CFSG.LieType.Steinberg.card_fixedSubfield hK]
  · have hSU : LargeEvenProj (LargeEvenSUGroup (Fin 2) K (2 ^ f)) ≃*
        ↥(LargeEvenSUGroup (Fin 2) K (2 ^ f)) :=
      (QuotientGroup.quotientMulEquivOfEq (uniPSU2_scalars_subgroupOf_suTwo_eq_bot hf1 hK)).trans
        QuotientGroup.quotientBot
    have hSL : LargeEvenProj (LargeEvenSLGroup (Fin 2)
          ↥(CFSG.LieType.Steinberg.fixedSubfield K 2 f)) ≃*
        ↥(LargeEvenSLGroup (Fin 2) ↥(CFSG.LieType.Steinberg.fixedSubfield K 2 f)) :=
      (QuotientGroup.quotientMulEquivOfEq uniPSU2_scalars_subgroupOf_slTwo_eq_bot).trans
        QuotientGroup.quotientBot
    obtain ⟨e1⟩ :=
      CFSG.StandardType.SURepair.nonempty_sl2_mulEquiv_unitarySU_two (K := K) (f := f) hK
    exact ⟨hSU.trans ((e1.symm.trans
      (Matrix.SpecialLinearGroup.toGLKerEquiv (n := Fin 2)
        (R := ↥(CFSG.LieType.Steinberg.fixedSubfield K 2 f)))).trans hSL.symm)⟩

end CFSG.StandardType.TablePThreeKG

end
