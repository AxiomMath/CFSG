module

public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Data.ZMod.Basic

public section

namespace CFSG.StandardType.GGSixE6Two.ILK

@[expose] def bitZ (b : Bool) : ZMod 2 := if b then 1 else 0

@[expose] def dec (n : ℕ) : Fin 16 → ZMod 2 := fun i => bitZ (n.testBit i)

@[expose] def code8 (b0 b1 b2 b3 b4 b5 b6 b7 : Fin 2) : ℕ :=
  b0.val + 2 * b1.val + 4 * b2.val + 8 * b3.val + 16 * b4.val + 32 * b5.val + 64 * b6.val +
    128 * b7.val

@[expose] def selK (n j c : ℕ) : ℕ := if n.testBit j then c else 0

@[expose] def mulCm (c : ℕ → ℕ) (n : ℕ) (m : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0 (fun j acc => Nat.xor acc (selK n j (c j))) m

theorem bitZ_xor (a b : Bool) : bitZ (a ^^ b) = bitZ a + bitZ b := by
  cases a <;> cases b <;> decide

theorem dec_zero : dec 0 = 0 := by
  funext i
  simp [dec, bitZ]

theorem dec_xor (a b : ℕ) : dec (Nat.xor a b) = dec a + dec b := by
  funext i
  have h : (Nat.xor a b).testBit i = (a ^^^ b).testBit i := rfl
  simp only [dec, Pi.add_apply]
  rw [h, Nat.testBit_xor, bitZ_xor]

theorem dec_selK (n j c : ℕ) : dec (selK n j c) = bitZ (n.testBit j) • dec c := by
  unfold selK
  cases n.testBit j
  · simp [dec_zero, bitZ]
  · simp [bitZ]

theorem dec_mulCm (c : ℕ → ℕ) (n : ℕ) :
    ∀ m : ℕ, dec (mulCm c n m) = ∑ j ∈ Finset.range m, bitZ (n.testBit j) • dec (c j)
  | 0 => by
    have e : mulCm c n 0 = 0 := rfl
    rw [e, dec_zero, Finset.sum_range_zero]
  | m + 1 => by
    have e : mulCm c n (m + 1) = Nat.xor (mulCm c n m) (selK n m (c m)) := rfl
    rw [e, dec_xor, dec_mulCm c n m, dec_selK, Finset.sum_range_succ]

theorem mulVec_dec (M : Matrix (Fin 16) (Fin 16) (ZMod 2)) (c : ℕ → ℕ)
    (hM : ∀ i j : Fin 16, M i j = dec (c j) i) (n : ℕ) :
    M.mulVec (dec n) = dec (mulCm c n 16) := by
  funext i
  rw [dec_mulCm, Finset.sum_apply,
    ← Fin.sum_univ_eq_sum_range (fun j => (bitZ (n.testBit j) • dec (c j)) i) 16]
  simp only [Matrix.mulVec, dotProduct, hM, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)

@[expose] def colTab : ℕ :=
  40164507118395964025432399535391028128358647046991019172510174046168287635511668987213824817627968648233963191152679100515911982928153287940495473500143407702895401552305667269086031879442493699867170535855672788986526739353983703537503403979635847391402343107565050018050757880261324717205947404275951260162139629812117040007938986897733174839784047213596963248713301148972316956140202164052609756348388844268882055486346473398057934025581441023216279752047633218894915040083963817730333919935311552465240352512577463042365288838254788714576466614265028854750738473733061081781181883176821965950905637556651021436404113558101646656544474529423884537137774459466490784595082154353817469686770925089413583708082751756967234048303591005406705436600719888175025019156976897939291262139086517638319649798255189650325556779986541038342766078382993528500072116188193731058128674925288900532870500203843229073336380513100356712470990654252707781132354852382386366396235005987582941718463478787396182124542527601090297378699699089953495425510443120376431688920588386904575371899410972737

@[expose] def colK (k j : ℕ) : ℕ :=
  Nat.land (Nat.shiftRight colTab (Nat.mul 16 (Nat.add (Nat.mul 16 k) j))) 65535

@[expose] def forceK (y : ℕ) (f : ℕ → ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) (f 0) (fun m _ => f (Nat.succ m)) y

theorem forceK_eq (y : ℕ) (f : ℕ → ℕ) : forceK y f = f y := by
  cases y <;> rfl

@[expose] def applyK (w : List (Fin 14)) (n : ℕ) : ℕ :=
  List.rec (motive := fun _ => ℕ → ℕ) (fun n => n)
    (fun k _ ih n => forceK (mulCm (colK k.val) n 16) ih) w n

theorem applyWord_dec (M : Fin 14 → Matrix (Fin 16) (Fin 16) (ZMod 2))
    (hM : ∀ (k : Fin 14) (i j : Fin 16), M k i j = dec (colK k.val j.val) i)
    (ap : List (Fin 14) → (Fin 16 → ZMod 2) → Fin 16 → ZMod 2) (hnil : ∀ v, ap [] v = v)
    (hcons : ∀ k w v, ap (k :: w) v = ap w ((M k).mulVec v)) :
    ∀ (w : List (Fin 14)) (n : ℕ), ap w (dec n) = dec (applyK w n)
  | [], n => hnil _
  | k :: w, n => by
    have e : applyK (k :: w) n = applyK w (mulCm (colK k.val) n 16) := by
      change forceK (mulCm (colK k.val) n 16) (applyK w) = _
      rw [forceK_eq]
    rw [hcons, mulVec_dec (M k) (colK k.val) (hM k) n, e, applyWord_dec M hM ap hnil hcons w]

@[expose] def matC (c : ℕ → ℕ) : Matrix (Fin 16) (Fin 16) (ZMod 2) := Matrix.of fun i j => dec (c j) i

@[expose] def colOf (P j : ℕ) : ℕ := Nat.land (Nat.shiftRight P (Nat.mul 16 j)) 65535

theorem eq_matC {M : Matrix (Fin 16) (Fin 16) (ZMod 2)} {c : ℕ → ℕ}
    (h : ∀ i j : Fin 16, M i j = dec (c j) i) : M = matC c :=
  Matrix.ext h

@[expose] def eqColB (f : Fin 16 → Fin 16 → ZMod 2) (c : ℕ → ℕ) : Bool :=
  (List.finRange 16).all fun i => (List.finRange 16).all fun j => decide (f i j = dec (c j) i)

theorem eqColB_sound {f : Fin 16 → Fin 16 → ZMod 2} {c : ℕ → ℕ} (h : eqColB f c = true) :
    ∀ i j : Fin 16, f i j = dec (c j) i := by
  intro i j
  unfold eqColB at h
  rw [List.all_eq_true] at h
  have h2 := List.all_eq_true.1 (h i (List.mem_finRange i)) j (List.mem_finRange j)
  exact of_decide_eq_true h2

theorem matC_congr {a b : ℕ → ℕ} (h : ∀ j : Fin 16, a j = b j) : matC a = matC b := by
  ext i j
  simp only [matC, Matrix.of_apply, h]

theorem matC_mul (a b : ℕ → ℕ) : matC a * matC b = matC (fun j => mulCm a (b j) 16) := by
  ext i j
  have h := congrFun (mulVec_dec (matC a) a (fun _ _ => rfl) (b j)) i
  rw [Matrix.mul_apply]
  exact h

theorem matC_add (a b : ℕ → ℕ) : matC a + matC b = matC (fun j => Nat.xor (a j) (b j)) := by
  ext i j
  simp only [Matrix.add_apply, matC, Matrix.of_apply, dec_xor, Pi.add_apply]

theorem dec_ne_zero {m : ℕ} (h : m % 65536 ≠ 0) : dec m ≠ 0 := by
  intro h0
  apply h
  apply Nat.eq_of_testBit_eq
  intro i
  have e : (65536 : ℕ) = 2 ^ 16 := by decide
  rw [e, Nat.testBit_mod_two_pow, Nat.zero_testBit]
  by_cases hi : i < 16
  · have hz := congrFun h0 ⟨i, hi⟩
    simp only [dec, bitZ, Pi.zero_apply] at hz
    cases hb : m.testBit i
    · simp
    · rw [hb] at hz
      exact absurd hz (by decide)
  · simp [hi]

@[expose] def y1C : ℕ :=
  1356945448338650717569038149218170551966101713056501374663644651403306205251

@[expose] def p1C : ℕ :=
  58801118932707190919777023128572428565230212454716209486743332435149017055232

@[expose] def y2C : ℕ :=
  97247821495176041009177660740151902782267267858646082421039242621770029924488

@[expose] def y2sqC : ℕ :=
  36185138316814417845593587840432844028822007169741302079146468317827135307843

@[expose] def p2C : ℕ := 353087278533476209161121491216105551

end CFSG.StandardType.GGSixE6Two.ILK

end
