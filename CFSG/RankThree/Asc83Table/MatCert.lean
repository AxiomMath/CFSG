module

public import CFSG.RankThree.Asc83Table.MatCertDefs
public import CFSG.LocalAnalysis.SectionRank.Sporadic.LocalWitness

public section

namespace CFSG.RankThree.Asc83Table

open CFSG.SectionRank CFSG.SectionRank.Native CFSG.SectionRank.LocalWitness CFSG.Blueprint
open CFSG.RankThree.Asc83Table.Native
open scoped Matrix

variable {M V : Type} {O : Ops M V} {p d : ℕ} (Sp : OpsSpec O p d) [Inhabited M]
  {sA sB : String} {C : MCert}

abbrev certRegs (O : Ops M V) (sA sB : String) (C : MCert) : Array M :=
  O.regsOf sA sB C.nregs C.prog

abbrev certMonoid (p d : ℕ) (sA sB : String) : Submonoid (Matrix (Fin d) (Fin d) (ZMod p)) :=
  NativeSporadic.seedMonoid p d 1 sA sB

theorem mem_facts {C : MCert} {f : MFact} (k : ℕ) (h : C.facts[k]? = some f) : f ∈ C.facts :=
  List.mem_of_getElem? h

@[expose] def wordPow (w : Word) (k : ℕ) : Word := (List.replicate k w).flatten

@[expose] def HasOrd (C : MCert) (w : Word) : Prop := ∀ q ∈ w, ∃ e, MFact.ord q.1 e ∈ C.facts

theorem hasOrd_nil (C : MCert) : HasOrd C [] := fun _ h => absurd h List.not_mem_nil

theorem hasOrd_of_bool {C : MCert} {w : Word}
    (h : w.all (fun q => C.facts.any fun f => match f with
      | .ord r _ => r == q.1
      | _ => false) = true) : HasOrd C w := by
  intro q hq
  have h' := List.all_eq_true.1 h q hq
  obtain ⟨f, hf, hfq⟩ := List.any_eq_true.1 h'
  cases f with
  | ord r e =>
    simp only [beq_iff_eq] at hfq
    exact ⟨e, hfq ▸ hf⟩
  | conj _ _ _ => exact absurd hfq Bool.false_ne_true
  | ne _ _ _ => exact absurd hfq Bool.false_ne_true
  | eq _ _ => exact absurd hfq Bool.false_ne_true

theorem hasOrd_append {C : MCert} {w₁ w₂ : Word} (h₁ : HasOrd C w₁) (h₂ : HasOrd C w₂) :
    HasOrd C (w₁ ++ w₂) := by
  intro q hq
  rcases List.mem_append.1 hq with h | h
  · exact h₁ q h
  · exact h₂ q h

theorem hasOrd_wordPow {C : MCert} {w : Word} (h : HasOrd C w) (k : ℕ) :
    HasOrd C (wordPow w k) := by
  intro q hq
  obtain ⟨l, hl, hql⟩ := List.mem_flatten.1 hq
  rw [List.eq_of_mem_replicate hl] at hql
  exact h q hql

section Check

variable (hC : mcertCheck O sA sB C = true)
include hC

theorem prog_ok : C.prog.all (Op.lt C.nregs) = true := by
  unfold mcertCheck at hC
  simp only [Bool.and_eq_true] at hC
  exact hC.1.2

theorem factOK_of_mem {f : MFact} (hf : f ∈ C.facts) :
    factOK O (certRegs O sA sB C) C.nregs f = true := by
  unfold mcertCheck at hC
  simp only [Bool.and_eq_true, List.all_eq_true] at hC
  exact hC.2 f hf

include Sp in
theorem reg_ok {r : ℕ} (hr : r < C.nregs) :
    Sp.WF (certRegs O sA sB C)[r]! ∧ Sp.toMat (certRegs O sA sB C)[r]! ∈ certMonoid p d sA sB :=
  Sp.regsOf_ok (prog_ok hC) hr

include Sp in
theorem evalW_ok : ∀ {w : Word}, wordLt C.nregs w = true →
    Sp.WF (evalW O (certRegs O sA sB C) w) ∧
      Sp.toMat (evalW O (certRegs O sA sB C) w) =
        (w.map fun q => Sp.toMat (certRegs O sA sB C)[q.1]! ^ q.2).prod
  | [], _ => ⟨Sp.one_wf, by rw [evalW, Sp.toMat_one]; rfl⟩
  | (r, e) :: w, hw => by
    simp only [wordLt, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hw
    obtain ⟨wr, -⟩ := reg_ok Sp hC hw.1
    obtain ⟨ww, hww⟩ := evalW_ok (w := w) hw.2
    obtain ⟨wp, hwp⟩ := Sp.pow_spec wr e
    refine ⟨Sp.mul_wf wp ww, ?_⟩
    rw [evalW, Sp.toMat_mul wp ww, hwp, hww, List.map_cons, List.prod_cons]

include Sp in
theorem reg_pow {r e : ℕ} (hf : MFact.ord r e ∈ C.facts) :
    r < C.nregs ∧ 0 < e ∧ Sp.toMat (certRegs O sA sB C)[r]! ^ e = 1 := by
  have h := factOK_of_mem hC hf
  simp only [factOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hr, he⟩, hpow⟩ := h
  exact ⟨hr, he, Sp.pow_eq_one_of_check (reg_ok Sp hC hr).1 hpow⟩

@[expose] noncomputable def regUnit (r : ℕ) : (certMonoid p d sA sB)ˣ :=
  haveI := Classical.propDecidable (∃ e, MFact.ord r e ∈ C.facts)
  if h : ∃ e, MFact.ord r e ∈ C.facts then
    unitOf _ (reg_ok Sp hC (reg_pow Sp hC h.choose_spec).1).2
      (reg_pow Sp hC h.choose_spec).2.1.ne' (reg_pow Sp hC h.choose_spec).2.2
  else 1

theorem val_regUnit {r e : ℕ} (hf : MFact.ord r e ∈ C.facts) :
    valHom _ (regUnit Sp hC r) = Sp.toMat (certRegs O sA sB C)[r]! := by
  have h : ∃ e, MFact.ord r e ∈ C.facts := ⟨e, hf⟩
  unfold regUnit
  rw [dite_eq_left_of_eq_true (eq_true h), valHom_unitOf]

theorem regUnit_pow {r e : ℕ} (hf : MFact.ord r e ∈ C.facts) : regUnit Sp hC r ^ e = 1 := by
  apply valHom_injective
  rw [map_pow, val_regUnit Sp hC hf, (reg_pow Sp hC hf).2.2, map_one]

@[expose] noncomputable def wordUnit (w : Word) : (certMonoid p d sA sB)ˣ :=
  (w.map fun q => regUnit Sp hC q.1 ^ q.2).prod

theorem val_wordUnit {w : Word} (hw : HasOrd C w) :
    valHom _ (wordUnit Sp hC w) =
      (w.map fun q => Sp.toMat (certRegs O sA sB C)[q.1]! ^ q.2).prod := by
  induction w with
  | nil => simp [wordUnit]
  | cons q w ih =>
    obtain ⟨e, he⟩ := hw q List.mem_cons_self
    rw [wordUnit, List.map_cons, List.prod_cons, map_mul, map_pow, val_regUnit Sp hC he]
    rw [List.map_cons, List.prod_cons, ← ih (fun q' hq' => hw q' (List.mem_cons_of_mem q hq'))]
    rfl

include Sp in
theorem wordLt_of_hasOrd {w : Word} (hw : HasOrd C w) : wordLt C.nregs w = true := by
  simp only [wordLt, List.all_eq_true, decide_eq_true_eq]
  intro q hq
  obtain ⟨e, he⟩ := hw q hq
  exact (reg_pow Sp hC he).1

theorem val_wordUnit_eq {w : Word} (hw : HasOrd C w) :
    valHom _ (wordUnit Sp hC w) = Sp.toMat (evalW O (certRegs O sA sB C) w) := by
  rw [val_wordUnit Sp hC hw, (evalW_ok Sp hC (wordLt_of_hasOrd Sp hC hw)).2]

theorem regUnit_conj {h e₁ : ℕ} {u w : Word} (hf : MFact.conj h u w ∈ C.facts)
    (hh : MFact.ord h e₁ ∈ C.facts) (hu : HasOrd C u) (hw : HasOrd C w) :
    regUnit Sp hC h * wordUnit Sp hC u * (regUnit Sp hC h)⁻¹ = wordUnit Sp hC w := by
  have hck := factOK_of_mem hC hf
  simp only [factOK, Bool.and_eq_true, decide_eq_true_eq] at hck
  obtain ⟨⟨⟨hhn, -⟩, -⟩, heq⟩ := hck
  rw [mul_inv_eq_iff_eq_mul]
  apply valHom_injective
  rw [map_mul, map_mul, val_regUnit Sp hC hh, val_wordUnit_eq Sp hC hu, val_wordUnit_eq Sp hC hw]
  obtain ⟨wh, -⟩ := reg_ok Sp hC hhn
  obtain ⟨wu, -⟩ := evalW_ok Sp hC (wordLt_of_hasOrd Sp hC hu)
  obtain ⟨ww, -⟩ := evalW_ok Sp hC (wordLt_of_hasOrd Sp hC hw)
  exact Sp.toMat_of_conjOK wh wu ww heq

theorem wordUnit_append (w₁ w₂ : Word) :
    wordUnit Sp hC (w₁ ++ w₂) = wordUnit Sp hC w₁ * wordUnit Sp hC w₂ := by
  simp [wordUnit, List.map_append, List.prod_append]

theorem wordUnit_nil : wordUnit Sp hC [] = 1 := rfl

theorem wordUnit_cons (q : ℕ × ℕ) (w : Word) :
    wordUnit Sp hC (q :: w) = regUnit Sp hC q.1 ^ q.2 * wordUnit Sp hC w := by
  simp [wordUnit]

theorem wordUnit_wordPow (w : Word) (k : ℕ) :
    wordUnit Sp hC (wordPow w k) = wordUnit Sp hC w ^ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [wordPow, List.replicate_succ', List.flatten_append, List.flatten_singleton,
      wordUnit_append, ← wordPow, ih, pow_succ]

theorem regUnit_ne {w₁ w₂ : Word} {t : ℕ} (hf : MFact.ne w₁ w₂ t ∈ C.facts) (hw₁ : HasOrd C w₁)
    (hw₂ : HasOrd C w₂) : wordUnit Sp hC w₁ ≠ wordUnit Sp hC w₂ := by
  have hck := factOK_of_mem hC hf
  simp only [factOK, Bool.and_eq_true] at hck
  intro heq
  have hm := congrArg (valHom _) heq
  rw [val_wordUnit_eq Sp hC hw₁, val_wordUnit_eq Sp hC hw₂] at hm
  obtain ⟨ww₁, -⟩ := evalW_ok Sp hC (wordLt_of_hasOrd Sp hC hw₁)
  obtain ⟨ww₂, -⟩ := evalW_ok Sp hC (wordLt_of_hasOrd Sp hC hw₂)
  apply Sp.toVec_ne hck.2
  rw [Sp.toVec_vmul (Sp.unit_wf t) ww₁, Sp.toVec_vmul (Sp.unit_wf t) ww₂, hm]

theorem regUnit_eq {w₁ w₂ : Word} (hf : MFact.eq w₁ w₂ ∈ C.facts) (hw₁ : HasOrd C w₁)
    (hw₂ : HasOrd C w₂) : wordUnit Sp hC w₁ = wordUnit Sp hC w₂ := by
  have hck := factOK_of_mem hC hf
  simp only [factOK, Bool.and_eq_true] at hck
  apply valHom_injective
  rw [val_wordUnit_eq Sp hC hw₁, val_wordUnit_eq Sp hC hw₂]
  obtain ⟨ww₁, -⟩ := evalW_ok Sp hC (wordLt_of_hasOrd Sp hC hw₁)
  obtain ⟨ww₂, -⟩ := evalW_ok Sp hC (wordLt_of_hasOrd Sp hC hw₂)
  exact Sp.toMat_eq ww₁ ww₂ hck.2

end Check

end CFSG.RankThree.Asc83Table
