module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFortyFiveWeylFiveNative
import CFSG.HardMathSupport.Lang.D4Three.PowNormalForm
import CFSG.HardMathSupport.Dickson.Sec6.I1431D4Aux.FieldPart.NormalForm
import CFSG.HardMathSupport.Lang.Coordinator.D4Bridge.Bridge
public import CFSG.HardMathSupport.Dickson.Sec6.I1431D4Aux.FieldPart.Hom

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.SzFive

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Lang.D4Three CFSG.HardMathSupport.Dickson.Sec6.I1431.FieldPart
  CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Lang.E6Descent
open Subgroup
open scoped commutatorElement

theorem weylFivePower_of_model_POmegaPlus_four {X : Type} [Group X] {p f : ℕ}
    (h : StatedClassicalModel X .POmegaPlus 4 p f) (hp31 : p ≠ 31) :
    WeylFivePower X := by
  obtain ⟨hadm, K, hfield, hfinite, hcard, ⟨eG⟩⟩ := h
  obtain ⟨hp, hf1, -⟩ := hadm
  exact
    letI : Field K := hfield
    letI : Finite K := hfinite
    by
      have hchar : ringChar K = p :=
        CFSG.ClassicalGroups.Orthogonal.ringChar_eq_of_card_eq hp hf1 hcard
      have hK31 : ringChar K ≠ 31 := by
        rw [hchar]
        exact hp31
      have hpow : WeylFivePower (adjointGroup Tag.D4 K) := by
        intro α E hα5 hEexp _ hEinv
        obtain ⟨g, a, σ, hαeq⟩ :=
          exists_normal_form_of_pow_eq_one (K := K) (α := α) (p := 5)
            (by norm_num) (by norm_num) (by norm_num) hα5
        have hcoef : ∀ x : adjointGroup Tag.D4 K,
            (α x : ModGL Tag.D4 K) =
              ((g : ModGL Tag.D4 K) * rootDiagUnit Tag.D4 a) *
                Units.map (entrywiseHom σ.toRingHom) (x : ModGL Tag.D4 K) *
                ((g : ModGL Tag.D4 K) * rootDiagUnit Tag.D4 a)⁻¹ := by
          intro x
          rw [hαeq, MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
            Subgroup.coe_inv, coe_exactNormalAut, exactQ_zero]
          simp only [mul_one, inv_one]
          group
        obtain ⟨k, hk⟩ :=
          weylFive_native (τ := Tag.D4) (Or.inr (Or.inl rfl)) (K := K) hK31
            (G := adjointGroup Tag.D4 K) le_rfl (g : ModGL Tag.D4 K) g.2 a σ α hcoef E
            hEexp hEinv
        refine ⟨Nat.card (WeylGroup Tag.D4), k, ?_, hk⟩
        change ¬ 5 ∣ Nat.card (WeylGroup (TwistTag.tag TwistTag.D4))
        exact CFSG.RankThree.PartOne.KGD.not_dvd_card_weylGroup_D4
          (p := 5) Nat.prime_five (by norm_num)
      obtain ⟨eC⟩ :=
        CFSG.HardMathSupport.Lang.Coordinator.D4Bridge.nonempty_statedProj_equiv_adjointGroup
          (F := K)
      exact WeylFivePower.of_mulEquiv ((eG.trans eC).symm) hpow

theorem weylFiveInner_of_model_POmegaPlus_four {X : Type} [Group X] {p f : ℕ}
    (h : StatedClassicalModel X .POmegaPlus 4 p f) : WeylFiveInner X := by
  obtain ⟨hadm, K, hfield, hfinite, hcard, ⟨eG⟩⟩ := h
  exact
    letI : Field K := hfield
    letI : Finite K := hfinite
    by
      have hinner : WeylFiveInner (adjointGroup Tag.D4 K) := by
        intro Â β hExp hComm α hα
        obtain ⟨g, a, σ, hαeq⟩ :=
          exists_normal_form_of_pow_eq_one (K := K) (α := α) (p := 31)
            (by norm_num) (by norm_num) (by norm_num) (hExp α hα)
        have hnf : fieldPart (exactNormalAut Tag.D4 K a σ 0) = σ := by
          simpa [d4Graph_zero] using fieldPart_normalForm (K := K) a σ 0
        have hf : fieldPart α = σ := by
          rw [hαeq, map_mul, fieldPart_conj, hnf, one_mul]
        have hfield1 : fieldPart α = 1 := by
          have hle : Â ≤ commutator (MulAut (adjointGroup Tag.D4 K)) := by
            rw [← hComm]
            exact Subgroup.commutator_mono le_top le_top
          exact fieldPart_eq_one_of_mem_commutator (hle hα)
        have hσ1 : σ = 1 := by
          rw [← hf, hfield1]
        have hαeq1 : α = MulAut.conj g * exactNormalAut Tag.D4 K a 1 0 := by
          rw [hαeq, hσ1]
        obtain ⟨h, hsq⟩ := exists_inner_sq_conj_mul_exactNormalAut_one (K := K) g a
        have hsq' : α ^ 2 = MulAut.conj h := by
          rw [hαeq1, hsq]
        have hαpow : α = (α ^ 2) ^ 16 := by
          have h32 : (α ^ 2) ^ 16 = α := by
            calc (α ^ 2) ^ 16 = α ^ (2 * 16) := by rw [pow_mul]
              _ = α ^ 32 := by norm_num
              _ = α := by
                simpa using (pow_eq_pow_mod (a := α) (n := 31) 32 (hExp α hα))
          exact h32.symm
        have hfin : α = MulAut.conj (h ^ 16) := by
          rw [hαpow, hsq', ← map_pow]
        exact ⟨h ^ 16, hfin.symm⟩
      obtain ⟨eC⟩ :=
        CFSG.HardMathSupport.Lang.Coordinator.D4Bridge.nonempty_statedProj_equiv_adjointGroup
          (F := K)
      exact WeylFiveInner.of_mulEquiv ((eG.trans eC).symm) hinner

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.SzFive
