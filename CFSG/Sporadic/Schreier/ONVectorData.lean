module

public import CFSG.Sporadic.Schreier.ONActionData
public import CFSG.Sporadic.ON.VecSpec
public import Certificates.Data.CFSGNative.ONSchreier.Vectors
public import CFSG.Sporadic.ON.SetupBase

public noncomputable section

namespace CFSG.ONSchreier

open CFSG.Sporadic.ON CFSG.Sporadic.ON.Native CFSG.ONSchreier.Native Matrix

abbrev N : ℕ := 245520

abbrev nL : ℕ := 122760

abbrev Vec : Type := Fin 154 → ZMod 3

@[expose] def initialVector : Vec :=
  fun j => (((Data.rootDigits.toList.getD j.val '0').toNat - '0'.toNat : ℕ) : ZMod 3)

@[expose] def invariantForm : Matrix (Fin 154) (Fin 154) (ZMod 3) :=
  Blueprint.NativeSporadic.decode 3 154 1 Data.formPayload

@[expose] def spanningBasisInverse : Matrix (Fin 154) (Fin 154) (ZMod 3) :=
  Blueprint.NativeSporadic.decode 3 154 1 Data.spanInvPayload

@[expose] def spanIndex (k : Fin 154) : ℕ := Data.spanIdx[k.val]!

@[expose] def baseIndex (k : ℕ) : ℕ := Data.baseList.getD k 0

@[expose, irreducible] def leadCoord (z : Vec) : ZMod 3 :=
  ((List.finRange 154).find? fun j => z j != 0).elim 0 z

@[expose, irreducible] def normalize (z : Vec) : Vec := if leadCoord z = 2 then -z else z

@[expose, irreducible] def vectorOrbit : VOrbit := vorbit (digitsW Data.rootDigits)

@[expose, irreducible] def lineOrbit : VOrbit := lineBFS colsA colsB (digitsW Data.rootDigits) nL

theorem vectorOrbit_def : vectorOrbit = vorbit (digitsW Data.rootDigits) := by
  unfold vectorOrbit
  rfl

theorem lineOrbit_def : lineOrbit = lineBFS colsA colsB (digitsW Data.rootDigits) nL := by
  unfold lineOrbit
  rfl

@[expose] def vv (i : ℕ) : Vec :=
  if i < vectorOrbit.keys.size then vecOf vectorOrbit.keys[i]! else 0

@[expose] def uu (j : ℕ) : Vec :=
  if j < lineOrbit.keys.size then vecOf lineOrbit.keys[j]! else 0

open scoped Classical in
@[expose] def lookup (f : ℕ → Vec) (m : ℕ) (w : Vec) : ℕ :=
  if h : ∃ j, j < m ∧ f j = w then Nat.find h else 0

@[expose] def f0 (i : ℕ) : ℕ := lookup vv N (mA *ᵥ vv i)

@[expose] def f1 (i : ℕ) : ℕ := lookup vv N (mB *ᵥ vv i)

@[expose] def l0 (j : ℕ) : ℕ := lookup uu nL (normalize (mA *ᵥ uu j))

@[expose] def l1 (j : ℕ) : ℕ := lookup uu nL (normalize (mB *ᵥ uu j))

@[expose] def piMap (i : ℕ) : ℕ := lookup uu nL (normalize (vv i))

@[expose] def sigmaMap (i : ℕ) : ℕ := lookup vv N (-vv i)

@[expose] def basisMatrix : Matrix (Fin 154) (Fin 154) (ZMod 3) :=
  Matrix.of fun r k => vv (spanIndex k) r

@[expose] def pairing (i j : ℕ) : ZMod 3 := vv i ⬝ᵥ (invariantForm *ᵥ vv j)

@[expose] def runProgram {G : Type*} [Group G] : (ℕ → G) → List Data.Instr → ℕ → G
  | regs, [] => regs
  | regs, .mu a b c :: rest => runProgram (Function.update regs c (regs a * regs b)) rest
  | regs, .iv a b :: rest => runProgram (Function.update regs b (regs a)⁻¹) rest

@[expose] def firstUninitialized : List ℕ → List Data.Instr → Option ℕ
  | _, [] => none
  | init, .mu a b c :: rest =>
    if a ∉ init then some a else if b ∉ init then some b else firstUninitialized (c :: init) rest
  | init, .iv a b :: rest =>
    if a ∉ init then some a else firstUninitialized (b :: init) rest

theorem leadCoord_eq_of_find {z : Vec} {j : Fin 154}
    (h : (List.finRange 154).find? (fun j => z j != 0) = some j) : leadCoord z = z j := by
  unfold leadCoord
  rw [h]
  rfl

theorem leadCoord_ne_zero {z : Vec} (hz : z ≠ 0) : leadCoord z ≠ 0 := by
  obtain ⟨i, hi⟩ : ∃ i, z i ≠ 0 := by
    by_contra h
    exact hz (funext fun i => by simpa using fun hi => h ⟨i, hi⟩)
  cases hf : (List.finRange 154).find? (fun j => z j != 0) with
  | none =>
    rw [List.find?_eq_none] at hf
    exact absurd (hf i (List.mem_finRange i)) (by simpa using hi)
  | some j =>
    rw [leadCoord_eq_of_find hf]
    simpa using List.find?_some hf

theorem leadCoord_smul (c : ZMod 3) (hc : c ≠ 0) (z : Vec) :
    leadCoord (c • z) = c * leadCoord z := by
  have hiff : (fun j => (c • z) j != 0) = (fun j => z j != 0) := by
    funext j
    simp only [Pi.smul_apply, smul_eq_mul]
    generalize z j = x
    revert c x
    decide
  unfold leadCoord
  rw [hiff]
  cases (List.finRange 154).find? (fun j => z j != 0) <;> simp

theorem zmod3_ne_zero {c : ZMod 3} (hc : c ≠ 0) : c = 1 ∨ c = 2 := by
  revert c hc
  decide

theorem normalize_eq_smul (z : Vec) :
    normalize z = (if leadCoord z = 2 then (2 : ZMod 3) else 1) • z := by
  unfold normalize
  split_ifs
  · funext j
    simp only [Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
    generalize z j = x
    revert x
    decide
  · simp

theorem normalize_spec {z : Vec} (hz : z ≠ 0) :
    (∃ c : ZMod 3, c ≠ 0 ∧ normalize z = c • z) ∧ leadCoord (normalize z) = 1 ∧
      ∀ c : ZMod 3, c ≠ 0 → normalize (c • z) = normalize z := by
  have hl := leadCoord_ne_zero hz
  refine ⟨⟨_, ?_, normalize_eq_smul z⟩, ?_, fun c hc => ?_⟩
  · split_ifs <;> decide
  · rw [normalize_eq_smul, leadCoord_smul _ (by split_ifs <;> decide)]
    generalize leadCoord z = x at hl ⊢
    revert x
    decide
  · rw [normalize_eq_smul, normalize_eq_smul, leadCoord_smul c hc, smul_smul]
    congr 1
    generalize leadCoord z = x at hl ⊢
    revert c x
    decide


theorem base_facts : Data.baseList.length = 29 ∧ Data.baseList.Nodup ∧
    ∀ b ∈ Data.baseList, b < N := by
  decide

theorem spanIdx_facts : Data.spanIdx.size = 154 ∧ ∀ i ∈ Data.spanIdx.toList, i < N := by
  decide +kernel

theorem words_facts : Data.strongWords.size = 7 ∧ Data.strongWords[0]! = [] ∧
    Data.strongWords[1]! = [] ∧
    ∀ j < 7, 2 ≤ j → ∀ l ∈ Data.strongWords[j]!, l ≠ 0 ∧ l.natAbs ≤ j := by
  decide +kernel

theorem normalize_zero : normalize 0 = 0 := by
  unfold normalize
  split_ifs
  · exact neg_zero
  · rfl

theorem program_facts : Data.subgroupProgram.length = 9 ∧
    firstUninitialized [1, 2] Data.subgroupProgram = none := by
  decide

theorem cert_on_vector_line_data :
    (Data.baseList.length = 29 ∧ Data.baseList.Nodup ∧ ∀ b ∈ Data.baseList, b < N) ∧
    (Data.spanIdx.size = 154 ∧ ∀ i ∈ Data.spanIdx.toList, i < N) ∧
    (Data.strongWords.size = 7 ∧ Data.strongWords[0]! = [] ∧ Data.strongWords[1]! = [] ∧
      ∀ j < 7, 2 ≤ j → ∀ l ∈ Data.strongWords[j]!, l ≠ 0 ∧ l.natAbs ≤ j) ∧
    (Data.subgroupProgram.length = 9 ∧ firstUninitialized [1, 2] Data.subgroupProgram = none) ∧
    (∀ z : Vec, z ≠ 0 → (∃ c : ZMod 3, c ≠ 0 ∧ normalize z = c • z) ∧
      leadCoord (normalize z) = 1 ∧ ∀ c : ZMod 3, c ≠ 0 → normalize (c • z) = normalize z) ∧
    normalize 0 = 0 ∧
    (∀ i, f0 i = lookup vv N (mA *ᵥ vv i) ∧ f1 i = lookup vv N (mB *ᵥ vv i)) ∧
    (∀ j, l0 j = lookup uu nL (normalize (mA *ᵥ uu j)) ∧
      l1 j = lookup uu nL (normalize (mB *ᵥ uu j))) ∧
    (∀ i, piMap i = lookup uu nL (normalize (vv i)) ∧ sigmaMap i = lookup vv N (-vv i)) ∧
    (∀ r k, basisMatrix r k = vv (spanIndex k) r) ∧
    ∀ i j, pairing i j = vv i ⬝ᵥ (invariantForm *ᵥ vv j) :=
  ⟨base_facts, spanIdx_facts, words_facts, program_facts, fun _ hz => normalize_spec hz,
    normalize_zero, fun _ => ⟨rfl, rfl⟩, fun _ => ⟨rfl, rfl⟩,
    fun _ => ⟨rfl, rfl⟩, fun _ _ => rfl, fun _ _ => rfl⟩

end CFSG.ONSchreier
