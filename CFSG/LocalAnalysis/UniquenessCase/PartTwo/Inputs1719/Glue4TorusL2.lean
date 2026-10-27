module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Glue4TorusReduction
import CFSG.GH74.GLS.Stage4.LocalSL2
import CFSG.GH74.GLS.IVK.Proofs2.Sl2Inv
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilySmall

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

section Model

open CFSG.GH74.GLS.Stage4.Hex CFSG.GH74.GLS.Stage4.SL2

variable {F : Type} [Field F]

private theorem g4l2_pow_entries (x : SL2 F) (hx : (x : Matrix (Fin 2) (Fin 2) F) 1 0 = 0)
    (k : ℕ) :
    ((x ^ k : SL2 F) : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 ∧
      ((x ^ k : SL2 F) : Matrix (Fin 2) (Fin 2) F) 0 0 =
        (x : Matrix (Fin 2) (Fin 2) F) 0 0 ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Matrix.SpecialLinearGroup.coe_mul]
    simp only [Matrix.mul_apply, Fin.sum_univ_two, ih.1, ih.2, hx, pow_succ]
    constructor <;> ring

private theorem g4l2_entry_ne_zero (x : SL2 F) (hx : (x : Matrix (Fin 2) (Fin 2) F) 1 0 = 0) :
    (x : Matrix (Fin 2) (Fin 2) F) 0 0 ≠ 0 := by
  intro h
  have hdet := sl2_entries x
  rw [h, hx] at hdet
  simp at hdet

private theorem g4l2_pow_mem_upperSub [Finite F] (x : SL2 F)
    (hx : (x : Matrix (Fin 2) (Fin 2) F) 1 0 = 0) : x ^ (Nat.card F - 1) ∈ upperSub F := by
  obtain ⟨h10, h00⟩ := g4l2_pow_entries x hx (Nat.card F - 1)
  have h1 : (x : Matrix (Fin 2) (Fin 2) F) 0 0 ^ (Nat.card F - 1) = 1 := by
    have h := pow_card_eq_one' (x := Units.mk0 _ (g4l2_entry_ne_zero x hx))
    rw [Nat.card_units] at h
    simpa using congrArg Units.val h
  rw [h1] at h00
  have hdet := sl2_entries (x ^ (Nat.card F - 1))
  rw [h10, h00] at hdet
  refine (mem_upperSub_iff _).2
    ⟨((x ^ (Nat.card F - 1) : SL2 F) : Matrix (Fin 2) (Fin 2) F) 0 1, sl2_ext ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h10, h00]
  simpa using hdet

private theorem g4l2_mem_diagSub_sup (x : SL2 F) (hx : (x : Matrix (Fin 2) (Fin 2) F) 1 0 = 0) :
    x ∈ diagSub F ⊔ upperSub F := by
  have hdet := sl2_entries x
  rw [hx, mul_zero, sub_zero] at hdet
  have ha := g4l2_entry_ne_zero x hx
  have hx' : x = sl2D (Units.mk0 _ ha) *
      sl2U (((x : Matrix (Fin 2) (Fin 2) F) 0 0)⁻¹ * (x : Matrix (Fin 2) (Fin 2) F) 0 1) := by
    apply sl2_ext
    rw [Matrix.SpecialLinearGroup.coe_mul]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hx]
    · field_simp
    · exact (inv_eq_of_mul_eq_one_right hdet).symm
  rw [hx']
  exact mul_mem_sup ((mem_diagSub_iff _).2 ⟨_, rfl⟩) ((mem_upperSub_iff _).2 ⟨_, rfl⟩)

private theorem g4l2_sl2W_pow_four : sl2W F ^ 4 = 1 := by
  apply sl2_ext
  simp [pow_succ, Matrix.SpecialLinearGroup.coe_mul, Matrix.one_fin_two]

private theorem g4l2_sl2W_conj (t : Fˣ) : sl2W F * sl2D t * (sl2W F)⁻¹ = (sl2D t)⁻¹ := by
  apply sl2_ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_inv_entries,
    coe_inv_entries]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

private theorem g4l2_diagSub_equiv [Finite F] {n : ℕ} (hF : Nat.card F = 2 ^ n) :
    Nonempty (diagSub F ≃* Multiplicative (ZMod (2 ^ n - 1))) := by
  have e : diagSub F ≃* Fˣ := (MonoidHom.ofInjective diagHom_injective).symm
  haveI : IsCyclic (diagSub F) := (MulEquiv.isCyclic e).2 inferInstance
  have hcard : Nat.card (diagSub F) = 2 ^ n - 1 := by rw [card_diagSub, hF]
  have e' := (zmodCyclicMulEquiv (inferInstance : IsCyclic (diagSub F))).symm
  rw [hcard] at e'
  exact ⟨e'⟩

private theorem g4l2_isSylowOf_upperSub [Finite F] {n : ℕ} (hF : Nat.card F = 2 ^ n) :
    CFSG.ABGLocalTools.IsSylowOf 2 (upperSub F) ⊤ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine CFSG.ABGLocalTools.isSylowOf_of_card le_top ?_
  rw [Subgroup.card_top,
    CFSG.GH74.GLS.IVK.Proofs2.Sl2Inv.factorization_card_SL2 Nat.prime_two hF, card_upperSub, hF]

private theorem g4l2_cartanAt_upperSub [Finite F] {n : ℕ} (hF : Nat.card F = 2 ^ n) :
    CartanAt (upperSub F) n (Multiplicative (ZMod (2 ^ n - 1))) := by
  refine ⟨diagSub F, sl2W F, ?_, g4l2_diagSub_equiv hF, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨t, rfl⟩ := (mem_diagSub_iff x).1 hx
    exact (mem_normalizer_upper_iff _).2 (sl2D_entries_zero t).2
  · intro x hx
    have hc := (mem_normalizer_upper_iff x).1 hx
    have h1 := g4l2_pow_mem_upperSub x hc
    rw [hF] at h1
    exact iff_of_true h1 (g4l2_mem_diagSub_sup x hc)
  · have hdvd : orderOf (sl2W F) ∣ 2 ^ 2 := orderOf_dvd_of_pow_eq_one g4l2_sl2W_pow_four
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
    exact ⟨k, hk⟩
  · intro a ha
    obtain ⟨t, rfl⟩ := (mem_diagSub_iff a).1 ha
    exact g4l2_sl2W_conj t

end Model

private theorem g4l2_exists_sl2 {Y : Type} [Group Y] {n : ℕ} (h : IsL2 Y n) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ n ∧
      Nonempty (Y ≃* Matrix.SpecialLinearGroup (Fin 2) F) := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := CFSG.Blueprint.LieModel.statedClassicalModel h (by decide)
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 :=
    charP_of_card_eq_prime_pow (f := n) (by rw [← Nat.card_eq_fintype_card, hK])
  exact ⟨K, inferInstance, inferInstance, hK,
    ⟨e.trans (CFSG.QuasithinUnique.Setup.Family.statedProjSL_two_equiv K)⟩⟩

theorem cartanAt_of_isL2 {Y : Type} [Group Y] [Finite Y] {n : ℕ} (h : IsL2 Y n) :
    ∃ U : Subgroup Y, CFSG.ABGLocalTools.IsSylowOf 2 U ⊤ ∧
      CartanAt U n (Multiplicative (ZMod (2 ^ n - 1))) := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := g4l2_exists_sl2 h
  exact ⟨_, isSylowOf_map_equiv (g4l2_isSylowOf_upperSub hF) e.symm,
    (g4l2_cartanAt_upperSub hF).map e.symm⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
