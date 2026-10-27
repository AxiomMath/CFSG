module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2Gs03U62Data
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2Gs03U62Pigeon
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoHypIICoverU62Model

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Fischer CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
  CFSG.ComponentClassification.RankTwoHypIICover.U62 Gs03U62
open CFSG.F4.Native CFSG.Sporadic.Fi22.Native
open CFSG.LargeExtraspecial.SMod20.Aut

private theorem gs03_u62_code_val_sq (x : F4) :
    (x ^ 2).code.val = f4mul x.code.val x.code.val := by
  rw [pow_two, code_mul]

private theorem gs03_u62_codeOf_fvec_frob4 (c : ℕ) :
    codeOf (fvec frob4 (vecOfCode c)) = frobCode c := by
  have h : ∀ i : Fin 6, ((fvec frob4 (vecOfCode c)) i).code.val =
      f4mul (coord c i.val) (coord c i.val) := by
    intro i
    simp only [fvec, frob4_apply, vecOfCode]
    exact gs03_u62_code_val_sq _
  simp only [codeOf]
  rw [h 0, h 1, h 2, h 3, h 4, h 5]
  unfold frobCode
  rw [show List.range 6 = [0, 1, 2, 3, 4, 5] by decide]
  simp only [List.foldl_cons, List.foldl_nil]
  norm_num
  ring

theorem phiTab_rep : Rep 693 (phiTab ()) u62Phi := by
  intro i hi
  have hcode : codeOf (fvec frob4 (vecOfCode (uPts[i]!))) = frobCode (uPts[i]!) :=
    gs03_u62_codeOf_fvec_frob4 _
  have hb : normC (frobCode (uPts[i]!)) < 4096 := by
    rw [← hcode, normC_codeOf]
    exact codeOf_lt _
  have hl : ap (phiTab ()) i = uPos[normC (frobCode (uPts[i]!))]! := by
    unfold phiTab
    rw [ap_ofFn _ hi, UInt32.toNat_ofNat',
      Nat.mod_eq_of_lt (lt_of_le_of_lt (uPos_get_le hb) (by norm_num))]
  have hval : (u62Phi ⟨i, hi⟩).val = ptIdx (fvec frob4 (uVec i)) := by
    rw [u62Phi_eq, semiPerm_val]
    apply congrArg ptIdx
    rw [semiVec, Subgroup.coe_one, Units.val_one, Matrix.one_mulVec]
  have hpt : ptIdx (fvec frob4 (uVec i)) = uPos[normC (frobCode (uPts[i]!))]! := by
    unfold ptIdx
    change uPts.toList.idxOf (normC (codeOf (fvec frob4 (vecOfCode (uPts[i]!))))) = _
    rw [hcode]
    exact (uPos_get hb).symm
  rw [hl, idx_of_lt _ hi, Equiv.Perm.smul_def]
  exact (hval.trans hpt).symm

@[expose] def U62RepFacts (g₀ g₁ : Equiv.Perm (Fin 693)) : Prop :=
  (∃ t ∈ T46, g₀ = t * u62Phi) ∧ (∃ t ∈ T46, g₁ = t * u62Phi) ∧
    g₀ * g₀ = 1 ∧ g₁ * g₁ = 1 ∧ gs03FixCount g₀ ≠ gs03FixCount g₁ ∧
    (∃ s : Fin 4 → ↥T46, T46.subtype.range ≤
      Subgroup.closure (Set.range fun i => (T46.subtype (s i))⁻¹ * g₀ * T46.subtype (s i))) ∧
    (∃ s : Fin 3 → ↥T46, T46.subtype.range ≤
      Subgroup.closure (Set.range fun i => (T46.subtype (s i))⁻¹ * g₁ * T46.subtype (s i)))

