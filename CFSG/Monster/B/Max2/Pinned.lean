module

public import CFSG.Monster.B.Intertwiner.ArithSpec
public import Certificates.Certificate3108
public import Certificates.Data.CFSGNative.MonsterB.Max2Pinned
public import CFSG.Sporadic.HS.SmallF2Spec

public section

namespace CFSG.Monster.B

open Bin Matrix

theorem foldl_progStep (n : ℕ) :
    ∀ (l : List (ℕ × ℕ × ℕ)) (R : Array Mat) (r : ℕ → Matrix (Fin n) (Fin n) (ZMod 2)),
      (∀ ins ∈ l, ins.1 < 6 ∧ ins.2.1 < 6 ∧ ins.2.2 < 6) → R.size = 6 →
      (∀ i < 6, (R.getD i #[]).size ≤ n ∧ cmat n (R.getD i #[]) = r i) →
      (l.foldl (progStep n) R).size = 6 ∧
      ∀ i < 6, ((l.foldl (progStep n) R).getD i #[]).size ≤ n ∧
        cmat n ((l.foldl (progStep n) R).getD i #[]) = l.foldl progStepM r i
  | [], R, r, _, hR, h => ⟨hR, h⟩
  | ins :: l, R, r, hl, hR, h => by
    rw [List.foldl_cons, List.foldl_cons]
    obtain ⟨h1, h2, h3⟩ := hl ins (List.mem_cons_self ..)
    apply foldl_progStep n l _ _ (fun ins' h' => hl ins' (List.mem_cons_of_mem _ h'))
    · simp [progStep, hR]
    · intro i hi
      unfold progStep progStepM
      rw [Array.set!_eq_setIfInBounds, Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds]
      by_cases hk : ins.2.2 = i
      · subst hk
        rw [ite_eq_left rfl, ite_eq_left (by rw [hR]; exact h3), Option.getD_some,
          Function.update_self]
        refine ⟨by rw [mulP_size]; exact (h ins.1 h1).1, ?_⟩
        rw [cmat_mulP n _ _ (h ins.2.1 h2).1, (h ins.1 h1).2, (h ins.2.1 h2).2]
      · rw [ite_eq_right hk, Function.update_of_ne (Ne.symm hk), ← Array.getD_eq_getD_getElem?]
        exact h i hi

theorem runProg_spec {n : ℕ} {A B : Mat} (hA : A.size ≤ n) (hB : B.size ≤ n) (i : ℕ) (hi : i < 6) :
    ((runProg n A B).getD i #[]).size ≤ n ∧
      cmat n ((runProg n A B).getD i #[]) = progRegs (cmat n A) (cmat n B) i := by
  refine (foldl_progStep n max2Prog (initRegs n A B) (progInit (cmat n A) (cmat n B))
    (by decide) rfl ?_).2 i hi
  intro j hj
  unfold progInit
  interval_cases j <;> simp [initRegs, idMat_size, cmat_idMat, hA, hB]

theorem cmat_seedMat (s : String) :
    cmat 4370 (seedMat 4370 s) = CFSG.Blueprint.NativeSporadic.decode 2 4370 1 s := by
  rw [← CFSG.Sporadic.SmallF2.rowsMatrix_rowsOfPayload]
  ext i j
  rw [seedMat, cmat_matOfRows, CFSG.Sporadic.SmallF2.rowsMatrix_apply,
    CFSG.Sporadic.SmallF2.toVecD]

theorem seedMat_size (s : String) : (seedMat 4370 s).size ≤ 4370 := by
  simp [seedMat, matOfRows_size, CFSG.Sporadic.SmallF2.Native.rowsOfPayload]


@[expose] noncomputable def Tmat : Matrix (Fin 4370) (Fin 4370) (ZMod 2) := Dyadic.TK

noncomputable abbrev cMat : Matrix (Fin 4370) (Fin 4370) (ZMod 2) := progRegs genA₁ genA₂ 1

noncomputable abbrev dMat : Matrix (Fin 4370) (Fin 4370) (ZMod 2) := progRegs genA₁ genA₂ 2

theorem pinned_facts :
    cMat * cMat = 1 ∧ cMat ≠ 1 ∧ dMat ^ 48 = 1 ∧ dMat ^ 24 ≠ 1 ∧ dMat ^ 16 ≠ 1 ∧
    dMat ^ 24 * cMat = cMat * dMat ^ 24 ∧ IsUnit Tmat ∧ genA₂ * genA₂ * genA₂ = 1 ∧
    (dMat ^ 24 * (genA₂ * genA₂ * dMat ^ 24 * genA₂)) ^ 5 = 1 :=
  Certificates.certificate3108

end CFSG.Monster.B

end
