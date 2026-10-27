
module

public import CFSG.Timmesfeld.Orders.ClassicalLinear
public import CFSG.RankThree.Native.Fi22UCheckInputs

@[expose] public noncomputable section

namespace CFSG.RankThree.Native.Fi22U

open CFSG.Monster.B.Fischer CFSG.Fischer CFSG.Certificates CFSG.Certificates.Native
  CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly.LowTwoRank CFSG.LinearGroups Matrix
open scoped Pointwise

theorem fi22U_fieldData : UnitaryFieldData 2 1 F4 :=
  ⟨Nat.prime_two, le_rfl, by rw [Nat.card_eq_fintype_card, F4.card]; rfl⟩

theorem fi22U_card : Nat.card F4 = (2 ^ 1) ^ 2 := by
  rw [Nat.card_eq_fintype_card, F4.card]
  rfl

theorem fi22U_bar (c : F4) : fi22U_fieldData.bar c = c ^ 2 := by
  rw [UnitaryFieldData.bar_apply, pow_one]

theorem stdHermForm_eq_fi22Herm (x y : Fin 6 → F4) :
    stdHermForm fi22U_fieldData 6 x y = fi22Herm x y := by
  simp only [stdHermForm_apply, fi22U_bar, fi22Herm]

theorem mem_fi22S_iff (A : GL (Fin 6) F4) : A ∈ StatedSU 6 (2 ^ 1) F4 ↔
    (A : Matrix (Fin 6) (Fin 6) F4).det = 1 ∧
      ((A : Matrix (Fin 6) (Fin 6) F4).map (· ^ 2))ᵀ * (A : Matrix (Fin 6) (Fin 6) F4) = 1 := by
  have := (CFSG.LinearGroups.unitary_scalar_kernel Nat.prime_two fi22U_card (n := 6)
    (by norm_num)).1
  rw [← SetLike.mem_coe, this]
  simp only [pow_one, Set.mem_ofPred_eq]

theorem fi22Normalize_eq_smul {v : Fin 6 → F4} (hv : v ≠ 0) :
    ∃ c : F4, c ≠ 0 ∧ fi22Normalize v = c • v := by
  unfold fi22Normalize
  rcases h : (List.finRange 6).find? (fun i => decide (v i ≠ 0)) with _ | i
  · exfalso
    apply hv
    funext j
    have := List.find?_eq_none.1 h j (List.mem_finRange j)
    simpa using this
  · have hi : v i ≠ 0 := by simpa using List.find?_some h
    exact ⟨(v i)⁻¹, inv_ne_zero hi, rfl⟩

theorem fi22Herm_smul (c : F4) (v w : Fin 6 → F4) :
    fi22Herm (c • v) (c • w) = c ^ 3 * fi22Herm v w := by
  simp only [fi22Herm, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => by ring

theorem span_fi22Normalize {v : Fin 6 → F4} (hv : v ≠ 0) :
    Submodule.span F4 {fi22Normalize v} = Submodule.span F4 {v} := by
  obtain ⟨c, hc, he⟩ := fi22Normalize_eq_smul hv
  rw [he, Submodule.span_singleton_smul_eq (IsUnit.mk0 c hc)]

theorem fi22LexLt_irrefl (v : Fin 6 → F4) : ¬ fi22LexLt v v := by
  intro h
  exact (List.Lex.asymm (r := (· < ·))).asymm _ _ h h

abbrev fi22NormIso : Finset (Fin 6 → F4) :=
  Finset.univ.filter fun v : Fin 6 → F4 => v ≠ 0 ∧ fi22Herm v v = 0 ∧ fi22Normalize v = v

theorem smul_span (g : StatedSU 6 (2 ^ 1) F4) (v : Fin 6 → F4) :
    g • Submodule.span F4 {v} =
      Submodule.span F4 {((g : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) *ᵥ v} := by
  rw [Subgroup.smul_def, smul_eq_map, Submodule.map_span, Set.image_singleton]
  rfl

theorem mulVec_ne_zero' (g : GL (Fin 6) F4) {v : Fin 6 → F4} (hv : v ≠ 0) :
    (g : Matrix (Fin 6) (Fin 6) F4) *ᵥ v ≠ 0 := by
  intro h
  apply hv
  have := congrArg (fun w => ((g⁻¹ : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) *ᵥ w) h
  simpa [Matrix.mulVec_mulVec, ← Units.val_mul] using this

theorem fi22Herm_smul_smul (g : StatedSU 6 (2 ^ 1) F4) (x y : Fin 6 → F4) :
    fi22Herm (((g : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) *ᵥ x)
      (((g : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) *ᵥ y) = fi22Herm x y := by
  rw [← stdHermForm_eq_fi22Herm, ← stdHermForm_eq_fi22Herm]
  exact stdHermForm_smul_smul fi22U_fieldData g x y

theorem one_mem_traceZero : (1 : F4) ∈ fi22U_fieldData.traceZero := by
  rw [UnitaryFieldData.mem_traceZero, UnitaryFieldData.trace, map_one]
  exact CharTwo.add_self_eq_zero 1

theorem exists_mem_fi22S_tv {v : Fin 6 → F4} (hv : fi22Herm v v = 0) :
    ∃ g : StatedSU 6 (2 ^ 1) F4, ∀ x,
      ((g : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) *ᵥ x = fi22Tv v x := by
  obtain ⟨g, hg⟩ := exists_mem_unitarySU_hermTransvection fi22U_fieldData
    (by rw [stdHermForm_eq_fi22Herm]; exact hv) one_mem_traceZero
  refine ⟨g, fun x => ?_⟩
  have := LinearMap.congr_fun hg x
  rw [Matrix.mulVecLin_apply, hermTransvection_apply, one_mul, stdHermForm_eq_fi22Herm] at this
  rw [this]
  rfl

theorem fi22OuterLine693_two (k : ℕ) : fi22OuterLine693 2 k = 15 + k := rfl

theorem fi22OuterStrong693_two_get {k : ℕ} (hk : k < 49) :
    (fi22OuterStrong693 2)[k]! = fi22OuterArr693 (15 + k) := by
  rw [fi22OuterStrong693, getElem!_pos _ k (by rw [Array.size_ofFn]; exact hk),
    Array.getElem_ofFn]
  exact congrArg fi22OuterArr693 (fi22OuterLine693_two k)

theorem card_statedProj_fi22S : Nat.card (StatedProj (StatedSU 6 (2 ^ 1) F4)) = 9196830720 := by
  rw [CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSU Nat.prime_two le_rfl fi22U_card
    (by norm_num : 2 ≤ 6)]
  decide

end CFSG.RankThree.Native.Fi22U
