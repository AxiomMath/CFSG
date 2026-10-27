module

public import CFSG.RankThree.Asc83Table.MatFacts
public import CFSG.LocalAnalysis.SectionRank.Sporadic.Elem3

public section

namespace CFSG.RankThree.Asc83Table

open CFSG.SectionRank CFSG.SectionRank.Native CFSG.RankThree.Asc83Table.Native CFSG.Blueprint
open scoped Matrix

variable {p d : ℕ}

@[expose] noncomputable def matOps (p d : ℕ) :
    Ops (Matrix (Fin d) (Fin d) (ZMod p)) (Fin d → ZMod p) where
  decode := NativeSporadic.decode p d 1
  mul X Y := X * Y
  one := 1
  eq X Y := @decide (X = Y) (Classical.propDecidable _)
  vmul v X := v ᵥ* X
  unit k i := if (i : ℕ) = k then 1 else 0
  vne u w := @decide (u ≠ w) (Classical.propDecidable _)

@[expose] noncomputable def matOpsSpec (p d : ℕ) : OpsSpec (matOps p d) p d where
  toMat X := X
  toVec v := v
  WF _ := True
  VWF _ := True
  decode_wf _ := trivial
  toMat_decode _ := rfl
  mul_wf _ _ := trivial
  toMat_mul _ _ := rfl
  one_wf := trivial
  toMat_one := rfl
  toMat_eq _ _ h := @of_decide_eq_true _ (Classical.propDecidable _) h
  vmul_wf _ _ := trivial
  toVec_vmul _ _ := rfl
  unit_wf _ := trivial
  toVec_ne h := @of_decide_eq_true _ (Classical.propDecidable _) h

theorem matOps_pow (X : Matrix (Fin d) (Fin d) (ZMod p)) (e : ℕ) : (matOps p d).pow X e = X ^ e :=
  ((matOpsSpec p d).pow_spec trivial e).2

theorem step_matOps {n : ℕ} {R : Array (Matrix (Fin d) (Fin d) (ZMod p))}
    {S : ℕ → Matrix (Fin d) (Fin d) (ZMod p)} (hs : R.size = n) (hR : ∀ r < n, R[r]! = S r)
    {op : Op} (hop : op.lt n = true) :
    ((matOps p d).step R op).size = n ∧ ∀ r < n, ((matOps p d).step R op)[r]! = slpStep S op r := by
  cases op with
  | mul i j k =>
    simp only [Op.lt, Bool.and_eq_true, decide_eq_true_eq] at hop
    obtain ⟨⟨hi, hj⟩, -⟩ := hop
    refine ⟨by simp [Ops.step, Array.set!, hs], fun r hr => ?_⟩
    simp only [Ops.step, Array.set!, slpStep]
    rw [OpsSpec.getElem!_setIfInBounds_of_lt (by omega), Function.update_apply]
    by_cases hk : k = r
    · rw [if_pos hk, if_pos hk.symm, hR i hi, hR j hj]
      rfl
    · rw [if_neg hk, if_neg (Ne.symm hk), hR r hr]
  | pow e i k =>
    simp only [Op.lt, Bool.and_eq_true, decide_eq_true_eq] at hop
    obtain ⟨hi, -⟩ := hop
    refine ⟨by simp [Ops.step, Array.set!, hs], fun r hr => ?_⟩
    simp only [Ops.step, Array.set!, slpStep]
    rw [OpsSpec.getElem!_setIfInBounds_of_lt (by omega), Function.update_apply]
    by_cases hk : k = r
    · rw [if_pos hk, if_pos hk.symm, hR i hi, matOps_pow]
    · rw [if_neg hk, if_neg (Ne.symm hk), hR r hr]

theorem run_matOps {n : ℕ} : ∀ (prog : List Op) {R : Array (Matrix (Fin d) (Fin d) (ZMod p))}
    {S : ℕ → Matrix (Fin d) (Fin d) (ZMod p)}, R.size = n → (∀ r < n, R[r]! = S r) →
    prog.all (Op.lt n) = true → ∀ r < n, ((matOps p d).run prog R)[r]! = prog.foldl slpStep S r
  | [], _, _, _, hR, _ => hR
  | op :: prog, R, S, hs, hR, hp => by
    rw [List.all_cons, Bool.and_eq_true] at hp
    obtain ⟨hs', hR'⟩ := step_matOps hs hR hp.1
    exact run_matOps prog hs' hR' hp.2

theorem regsOf_matOps (sA sB : String) {n : ℕ} {prog : List Op}
    (hp : prog.all (Op.lt n) = true) {r : ℕ} (hr : r < n) :
    ((matOps p d).regsOf sA sB n prog)[r]! =
      slpRegs (NativeSporadic.decode p d 1 sA) (NativeSporadic.decode p d 1 sB) prog r := by
  refine run_matOps prog (by simp [Ops.initRegs]) (fun r hr => ?_) hp r hr
  unfold Ops.initRegs
  rw [getElem!_pos _ r (by simpa using hr), Array.getElem_ofFn]
  rfl

theorem evalW_matOps (R : Array (Matrix (Fin d) (Fin d) (ZMod p))) :
    ∀ w : Word, evalW (matOps p d) R w = wordProd (fun r => R[r]!) w
  | [] => rfl
  | (r, e) :: w => by
    rw [evalW, evalW_matOps R w, matOps_pow]
    simp only [wordProd, List.map_cons, List.prod_cons]
    rfl

theorem unit_vecMul_matOps {t : ℕ} (ht : t < d) (X : Matrix (Fin d) (Fin d) (ZMod p)) :
    (matOps p d).vmul ((matOps p d).unit t) X = X ⟨t, ht⟩ := by
  have hu : (matOps p d).unit t = Pi.single (⟨t, ht⟩ : Fin d) 1 := by
    funext i
    simp only [matOps, Pi.single_apply, Fin.ext_iff]
  change (matOps p d).unit t ᵥ* X = _
  rw [hu, Matrix.single_one_vecMul]
  rfl

theorem factOK_matOps {R : Array (Matrix (Fin d) (Fin d) (ZMod p))} {n : ℕ} {f : MFact}
    (h : f.Holds (fun r => R[r]!) n) : factOK (matOps p d) R n f = true := by
  cases f with
  | ord r e =>
    obtain ⟨hr, he, h1⟩ := h
    simp only [factOK, Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨⟨hr, he⟩, ?_⟩
    rw [matOps_pow]
    exact @decide_eq_true _ (Classical.propDecidable _) h1
  | conj g u w =>
    obtain ⟨hg, hu, hw, e⟩ := h
    simp only [factOK, Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨⟨⟨hg, hu⟩, hw⟩, ?_⟩
    rw [evalW_matOps, evalW_matOps]
    exact @decide_eq_true _ (Classical.propDecidable _) e
  | ne w₁ w₂ t =>
    obtain ⟨h₁, h₂, ht, e⟩ := h
    simp only [factOK, Bool.and_eq_true]
    refine ⟨⟨h₁, h₂⟩, ?_⟩
    rw [unit_vecMul_matOps ht, unit_vecMul_matOps ht, evalW_matOps, evalW_matOps]
    exact @decide_eq_true _ (Classical.propDecidable _) e
  | eq w₁ w₂ =>
    obtain ⟨h₁, h₂, e⟩ := h
    simp only [factOK, Bool.and_eq_true]
    refine ⟨⟨h₁, h₂⟩, ?_⟩
    rw [evalW_matOps, evalW_matOps]
    exact @decide_eq_true _ (Classical.propDecidable _) e

theorem mcertCheck_matOps {sA sB : String} {n : ℕ} {prog : List Op} {facts : List MFact}
    (hn : 2 ≤ n) (hp : prog.all (Op.lt n) = true)
    (hf : ∀ f ∈ facts, f.Holds
      (slpRegs (NativeSporadic.decode p d 1 sA) (NativeSporadic.decode p d 1 sB) prog) n) :
    mcertCheck (matOps p d) sA sB ⟨n, prog, facts⟩ = true := by
  simp only [mcertCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
  refine ⟨⟨hn, List.all_eq_true.1 hp⟩, fun f hf' => factOK_matOps ?_⟩
  exact (hf f hf').congr fun r hr => (regsOf_matOps sA sB hp hr).symm

theorem eq_seed_matOps {sA sB s : String} {n : ℕ} {prog : List Op} {r : ℕ}
    (hp : prog.all (Op.lt n) = true) (hr : r < n)
    (h : slpRegs (NativeSporadic.decode p d 1 sA) (NativeSporadic.decode p d 1 sB) prog r =
      NativeSporadic.decode p d 1 s) :
    (matOps p d).eq ((matOps p d).regsOf sA sB n prog)[r]! ((matOps p d).decode s) = true := by
  rw [regsOf_matOps sA sB hp hr, h]
  exact @decide_eq_true _ (Classical.propDecidable _) rfl

end CFSG.RankThree.Asc83Table

end
