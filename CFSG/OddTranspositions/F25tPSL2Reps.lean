module

public import CFSG.CharacterTheory.PSL2Table.Basic
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.OddTranspositions.F25Field

public section

namespace CFSG.OddTranspositions.QZ

open CFSG.GorensteinWalter

@[expose] def f25Code (x : F25t) : ℕ := x.a.val * 5 + x.b.val

theorem f25Code_lt (x : F25t) : f25Code x < 25 := by
  have h1 : x.a.val < 5 := ZMod.val_lt x.a
  have h2 : x.b.val < 5 := ZMod.val_lt x.b
  simp only [f25Code]
  omega

theorem f25Code_injective : Function.Injective f25Code := by
  intro x y h
  have hxb : x.b.val < 5 := ZMod.val_lt x.b
  have hyb : y.b.val < 5 := ZMod.val_lt y.b
  simp only [f25Code] at h
  have h2 : x.b.val = y.b.val := by
    have h' := congrArg (fun z : ℕ => z % 5) h
    rwa [Nat.mul_add_mod_of_lt (a := x.a.val) hxb,
      Nat.mul_add_mod_of_lt (a := y.a.val) hyb] at h'
  have h1 : x.a.val = y.a.val := by
    have h' : x.a.val * 5 = y.a.val * 5 := by
      have h'' := h
      rw [h2] at h''
      exact Nat.add_right_cancel h''
    exact Nat.mul_right_cancel (by norm_num : 0 < 5) h'
  exact F25t.ext (ZMod.val_injective 5 h1) (ZMod.val_injective 5 h2)

@[expose] def matCode (M : Matrix (Fin 2) (Fin 2) F25t) : ℕ :=
  (((f25Code (M 0 0) * 25 + f25Code (M 0 1)) * 25 + f25Code (M 1 0)) * 25 +
    f25Code (M 1 1))

theorem matCode_digits {a b c d a' b' c' d' : ℕ}
    (hb : b < 25) (hc : c < 25) (hd : d < 25)
    (hb' : b' < 25) (hc' : c' < 25) (hd' : d' < 25)
    (h : ((a * 25 + b) * 25 + c) * 25 + d = ((a' * 25 + b') * 25 + c') * 25 + d') :
    a = a' ∧ b = b' ∧ c = c' ∧ d = d' := by
  have hd_eq : d = d' := by
    have h' := congrArg (fun z : ℕ => z % 25) h
    rwa [Nat.mul_add_mod_of_lt (a := (a * 25 + b) * 25 + c) hd,
      Nat.mul_add_mod_of_lt (a := (a' * 25 + b') * 25 + c') hd'] at h'
  have h2 : ((a * 25 + b) * 25 + c) * 25 = ((a' * 25 + b') * 25 + c') * 25 := by
    have h' := h
    rw [hd_eq] at h'
    exact Nat.add_right_cancel h'
  have h2' : (a * 25 + b) * 25 + c = (a' * 25 + b') * 25 + c' :=
    Nat.mul_right_cancel (by norm_num : 0 < 25) h2
  have hc_eq : c = c' := by
    have h' := congrArg (fun z : ℕ => z % 25) h2'
    rwa [Nat.mul_add_mod_of_lt (a := a * 25 + b) hc,
      Nat.mul_add_mod_of_lt (a := a' * 25 + b') hc'] at h'
  have h3 : (a * 25 + b) * 25 = (a' * 25 + b') * 25 := by
    have h' := h2'
    rw [hc_eq] at h'
    exact Nat.add_right_cancel h'
  have h3' : a * 25 + b = a' * 25 + b' :=
    Nat.mul_right_cancel (by norm_num : 0 < 25) h3
  have hb_eq : b = b' := by
    have h' := congrArg (fun z : ℕ => z % 25) h3'
    rwa [Nat.mul_add_mod_of_lt (a := a) hb,
      Nat.mul_add_mod_of_lt (a := a') hb'] at h'
  have h4 : a * 25 = a' * 25 := by
    have h' := h3'
    rw [hb_eq] at h'
    exact Nat.add_right_cancel h'
  exact ⟨Nat.mul_right_cancel (by norm_num : 0 < 25) h4, hb_eq, hc_eq, hd_eq⟩

theorem matCode_injective : Function.Injective matCode := by
  intro M N h
  have key := matCode_digits (a := f25Code (M 0 0)) (b := f25Code (M 0 1))
    (c := f25Code (M 1 0)) (d := f25Code (M 1 1))
    (a' := f25Code (N 0 0)) (b' := f25Code (N 0 1))
    (c' := f25Code (N 1 0)) (d' := f25Code (N 1 1))
    (f25Code_lt (M 0 1)) (f25Code_lt (M 1 0)) (f25Code_lt (M 1 1))
    (f25Code_lt (N 0 1)) (f25Code_lt (N 1 0)) (f25Code_lt (N 1 1)) h
  have e00 : M 0 0 = N 0 0 := f25Code_injective key.1
  have e01 : M 0 1 = N 0 1 := f25Code_injective key.2.1
  have e10 : M 1 0 = N 1 0 := f25Code_injective key.2.2.1
  have e11 : M 1 1 = N 1 1 := f25Code_injective key.2.2.2
  funext i j
  fin_cases i <;> fin_cases j <;> assumption

theorem matCode_neg_ne (M : Matrix.SpecialLinearGroup (Fin 2) F25t) :
    matCode (M : Matrix (Fin 2) (Fin 2) F25t) ≠
      matCode (-(M : Matrix.SpecialLinearGroup (Fin 2) F25t) :
        Matrix (Fin 2) (Fin 2) F25t) := by
  intro h
  have hmat : (M : Matrix (Fin 2) (Fin 2) F25t) =
      (-(M : Matrix.SpecialLinearGroup (Fin 2) F25t) : Matrix (Fin 2) (Fin 2) F25t) :=
    matCode_injective h
  have h2cancel : ∀ y : ZMod 5, (2 : ZMod 5) * y = 0 → y = 0 := by
    intro y hy
    have h3 : (3 : ZMod 5) * 2 = 1 := by decide
    calc y = 1 * y := (one_mul y).symm
      _ = ((3 : ZMod 5) * 2) * y := by rw [h3]
      _ = (3 : ZMod 5) * ((2 : ZMod 5) * y) := by rw [mul_assoc]
      _ = 0 := by rw [hy, mul_zero]
  have hzero : ∀ x : F25t, x = -x → x = 0 := by
    intro x hx
    have hxa : x.a = -x.a := by
      have := congrArg F25t.a hx
      simpa using this
    have hxb : x.b = -x.b := by
      have := congrArg F25t.b hx
      simpa using this
    refine F25t.ext ?_ ?_
    · show x.a = (0 : ZMod 5)
      have hsum : x.a + x.a = 0 := (eq_neg_iff_add_eq_zero).mp hxa
      have hs : (2 : ZMod 5) * x.a = 0 := by
        rw [two_mul]
        exact hsum
      exact h2cancel x.a hs
    · show x.b = (0 : ZMod 5)
      have hsum : x.b + x.b = 0 := (eq_neg_iff_add_eq_zero).mp hxb
      have hs : (2 : ZMod 5) * x.b = 0 := by
        rw [two_mul]
        exact hsum
      exact h2cancel x.b hs
  have hz : ∀ i j, (M : Matrix (Fin 2) (Fin 2) F25t) i j = 0 := by
    intro i j
    apply hzero
    have := congrArg (fun A : Matrix (Fin 2) (Fin 2) F25t => A i j) hmat
    simpa using this
  have hdet := M.2
  rw [Matrix.det_fin_two] at hdet
  rw [hz 0 0, hz 0 1, hz 1 0, hz 1 1] at hdet
  have h01 : (0 : F25t) = 1 := by simpa using hdet
  exact zero_ne_one h01

@[expose] def canonSL (M : Matrix.SpecialLinearGroup (Fin 2) F25t) :
    Matrix.SpecialLinearGroup (Fin 2) F25t :=
  if matCode (M : Matrix (Fin 2) (Fin 2) F25t) ≤
      matCode ((-M : Matrix.SpecialLinearGroup (Fin 2) F25t) :
        Matrix (Fin 2) (Fin 2) F25t)
    then M else -M

theorem canonSL_mk (M : Matrix.SpecialLinearGroup (Fin 2) F25t) :
    CFSG.PSL2Table.mk (canonSL M) = CFSG.PSL2Table.mk M := by
  unfold canonSL
  by_cases h : matCode (M : Matrix (Fin 2) (Fin 2) F25t) ≤
      matCode ((-M : Matrix.SpecialLinearGroup (Fin 2) F25t) :
        Matrix (Fin 2) (Fin 2) F25t)
  · rw [if_pos h]
  · rw [if_neg h]
    exact CFSG.PSL2Table.mk_neg M

theorem canonSL_neg (M : Matrix.SpecialLinearGroup (Fin 2) F25t) :
    canonSL (-M) = canonSL M := by
  have hne : matCode (M : Matrix (Fin 2) (Fin 2) F25t) ≠
      matCode (-(M : Matrix (Fin 2) (Fin 2) F25t)) := by
    simpa using matCode_neg_ne M
  by_cases hp : matCode (M : Matrix (Fin 2) (Fin 2) F25t) ≤
      matCode (-(M : Matrix (Fin 2) (Fin 2) F25t))
  · have hq : ¬ (matCode (-(M : Matrix (Fin 2) (Fin 2) F25t)) ≤
        matCode (M : Matrix (Fin 2) (Fin 2) F25t)) :=
      fun hq => hne (le_antisymm hp hq)
    simp [canonSL, hp, hq]
  · have hq : matCode (-(M : Matrix (Fin 2) (Fin 2) F25t)) ≤
        matCode (M : Matrix (Fin 2) (Fin 2) F25t) := by
      omega
    simp [canonSL, hp, hq]

theorem canonSL_eq_of_mk_eq {M N : Matrix.SpecialLinearGroup (Fin 2) F25t}
    (h : CFSG.PSL2Table.mk M = CFSG.PSL2Table.mk N) : canonSL M = canonSL N := by
  rcases (CFSG.PSL2Table.mk_eq_mk_iff M N).mp h with hN | hN
  · rw [hN]
  · rw [hN, canonSL_neg]

theorem canonSL_idem (M : Matrix.SpecialLinearGroup (Fin 2) F25t) :
    canonSL (canonSL M) = canonSL M :=
  canonSL_eq_of_mk_eq (canonSL_mk M)

@[expose] def psl2Reps : Finset (Matrix.SpecialLinearGroup (Fin 2) F25t) :=
  Finset.univ.image canonSL

theorem mem_psl2Reps {M : Matrix.SpecialLinearGroup (Fin 2) F25t} :
    M ∈ psl2Reps ↔ canonSL M = M := by
  unfold psl2Reps
  rw [Finset.mem_image]
  simp only [Finset.mem_univ, true_and]
  constructor
  · rintro ⟨A, hA⟩
    rw [← hA, canonSL_idem]
  · intro h
    exact ⟨M, h⟩

theorem mk_inj_on_reps {M N : Matrix.SpecialLinearGroup (Fin 2) F25t}
    (hM : M ∈ psl2Reps) (hN : N ∈ psl2Reps)
    (h : CFSG.PSL2Table.mk M = CFSG.PSL2Table.mk N) : M = N := by
  have hM' : canonSL M = M := mem_psl2Reps.mp hM
  have hN' : canonSL N = N := mem_psl2Reps.mp hN
  rw [← hM', ← hN']
  exact canonSL_eq_of_mk_eq h

end CFSG.OddTranspositions.QZ
