module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Wong77.ClsData
public import Certificates.Data.Kernel.RangeSplit

public section

namespace CFSG.EvenSporadicStandard.Wong77.Cls

@[expose] noncomputable def bitT (v j : ℕ) : Bool := Nat.beq (Nat.land 1 (Nat.shiftRight v j)) 1

theorem bitT_eq (v j : ℕ) : bitT v j = v.testBit j := by
  unfold bitT
  rw [Nat.testBit_eq_decide_div_mod_eq]
  have h : Nat.land 1 (Nat.shiftRight v j) = v / 2 ^ j % 2 := by
    show 1 &&& v >>> j = _
    rw [Nat.and_comm, Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow]
  rw [h]
  cases hh : Nat.beq (v / 2 ^ j % 2) 1
  · have := Nat.ne_of_beq_eq_false hh
    simp [this]
  · have := Nat.eq_of_beq_eq_true hh
    simp [this]

@[expose] noncomputable def mvNF (cols : List ℕ) (v : ℕ) : ℕ :=
  (List.range 11).foldl (fun acc j =>
    Bool.rec (motive := fun _ => ℕ) acc (Nat.xor acc (cols.getD j 0)) (bitT v j)) 0

theorem mvNF_fun : mvNF = mvN := by
  funext cols v
  unfold mvNF mvN
  congr 1
  funext acc j
  rw [bitT_eq]
  cases v.testBit j <;> rfl

@[expose] noncomputable def eqVF (a b : ℕ) : Bool := Nat.beq (Nat.mod a 2048) (Nat.mod b 2048)

theorem eqV_iff_mod (a b : ℕ) : eqV a b = true ↔ a % 2 ^ 11 = b % 2 ^ 11 := by
  unfold eqV
  rw [List.all_eq_true]
  constructor
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow]
    by_cases hi : i < 11
    · have := h i (List.mem_range.2 hi)
      simp only [beq_iff_eq] at this
      simp [hi, this]
    · simp [hi]
  · intro h k hk
    have hk' := List.mem_range.1 hk
    have := congrArg (fun x => x.testBit k) h
    simp only [Nat.testBit_mod_two_pow] at this
    simp [hk'] at this
    simp [this]

theorem eqVF_fun : eqVF = eqV := by
  funext a b
  unfold eqVF
  cases h : eqV a b
  · cases h2 : Nat.beq (Nat.mod a 2048) (Nat.mod b 2048)
    · rfl
    · exfalso
      have e := Nat.eq_of_beq_eq_true h2
      have := (eqV_iff_mod a b).2 e
      rw [h] at this
      exact absurd this (by decide)
  · have e := (eqV_iff_mod a b).1 h
    exact Nat.beq_eq_true_eq _ _ ▸ e

section G

variable (mv : List ℕ → ℕ → ℕ) (eq : ℕ → ℕ → Bool)

@[expose] def mulNG (A B : List ℕ) : List ℕ := B.map (mv A)

@[expose] def powNG (A : List ℕ) : ℕ → List ℕ
  | 0 => oneN
  | n + 1 => mulNG mv (powNG A n) A

@[expose] def kryNG (A : List ℕ) (z₀ z₁ : ℕ) : List ℕ :=
  z₀ :: (List.range 10).map fun k => (mv A)^[k] z₁

@[expose] def eqMG (A B : List ℕ) : Bool :=
  (List.range 11).all fun j => eq (A.getD j 0) (B.getD j 0)

@[expose] def cycTestG (a : ℕ) : Bool := !eq ((mv (compN a))^[23] 1) 1 || a == aN 0 || a == aN 1

@[expose] def checkCycG : Bool := (List.range 2048).all (cycTestG mv eq)

@[expose] def checkYG (Y C : List ℕ) : Bool :=
  eq (mv Y 1) 1 && eqMG eq (mulNG mv Y C) (mulNG mv (powNG mv C 16) Y)

@[expose] def checkFixG (Y : List ℕ) : Bool :=
  (List.range 2048).all fun z => !eq (mv Y z) z || z == 0 || z == 1

@[expose] def checkEpG (Up : List ℕ) (ep : ℕ) : Bool := eq (mv Up ep) ep && !eq ep 0

@[expose] def checkBinvG (Up : List ℕ) (ep : ℕ) (Binv : List ℕ) : Bool :=
  eqMG eq (mulNG mv (kryNG mv Up ep 1) Binv) oneN

@[expose] def uniqTestG (Y Up X : List ℕ) (y y₀ : ℕ) : Bool :=
  !eqMG eq (mulNG mv Y X) (mulNG mv X Up) || !eqMG eq (powNG mv X 4) oneN || y == y₀

@[expose] def uniqAtG (Y Up Binv : List ℕ) (y₀ y : ℕ) : Bool :=
  uniqTestG mv eq Y Up (mulNG mv (kryNG mv Y 1 y) Binv) y y₀

@[expose] def checkUniqG (Y Up Binv : List ℕ) (y₀ : ℕ) : Bool :=
  (List.range 2048).all (uniqAtG mv eq Y Up Binv y₀)

@[expose] def wordANG (C Y X : List ℕ) : List ℕ :=
  mulNG mv (mulNG mv (mulNG mv (mulNG mv (mulNG mv (mulNG mv (mulNG mv (mulNG mv
    (mulNG mv (powNG mv X 3) C) X) (powNG mv C 21)) Y) (powNG mv X 3)) (powNG mv C 22))
    (powNG mv X 3)) Y) (powNG mv X 3)

@[expose] def checkWordsG (A B C Y X : List ℕ) : Bool :=
  eqMG eq A (wordANG mv C Y X) && eqMG eq B (mulNG mv A C)

@[expose] def upG (C Y : List ℕ) : List ℕ := mulNG mv (powNG mv C 9) (powNG mv Y 5)

@[expose] def epG (C : List ℕ) : ℕ := mv (powNG mv C 12) 1

@[expose] def oneHeadG (C Y Binv : List ℕ) : Bool :=
  checkYG mv eq Y C && checkFixG mv eq Y && checkEpG mv eq (upG mv C Y) (epG mv C) &&
    checkBinvG mv eq (upG mv C Y) (epG mv C) Binv

@[expose] def checkOneAuxG (C Y Binv : List ℕ) (y₀ : ℕ) (A B : List ℕ) : Bool :=
  oneHeadG mv eq C Y Binv && checkUniqG mv eq Y (upG mv C Y) Binv y₀ &&
    checkWordsG mv eq A B C Y (mulNG mv (kryNG mv Y 1 y₀) Binv)

@[expose] def checkOneG (i : Fin 2) : Bool :=
  checkOneAuxG mv eq (compN (aN i)) (YN i) (BinvN i) (yN i) (stdAN i) (stdBN i)

end G

theorem powNG_eq (A : List ℕ) : ∀ n, powNG mvN A n = powN A n
  | 0 => rfl
  | n + 1 => by
    rw [powNG, powNG_eq A n]
    rfl

theorem checkCycG_eq : checkCycG mvN eqV = checkCyc := rfl

theorem checkOneG_eq (i : Fin 2) : checkOneG mvN eqV i = checkOne i := by
  simp only [checkOneG, checkOneAuxG, oneHeadG, checkYG, checkFixG, checkEpG, checkBinvG,
    checkUniqG, uniqAtG, uniqTestG, checkWordsG, wordANG, upG, epG, mulNG, kryNG, eqMG, powNG_eq]
  rfl

end CFSG.EvenSporadicStandard.Wong77.Cls

end
