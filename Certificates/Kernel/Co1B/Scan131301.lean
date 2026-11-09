module

public import Certificates.Data.Kernel.Co1BS0
public import CFSG.Certificates.Kernel.Co1BSpinSound
public import CFSG.Certificates.Kernel.Co1BSound

public section

namespace CertificateChecks.KernelCo1B.S0131301

open CFSG.KC.Loop CFSG.KC.Co1BS0 CFSG.KC.Co1BSpin CFSG.KC.Co1B CFSG.KLie.CT CFSG.KC.StrNlSp

theorem okC131_cases {c : Char} (h : okC131 c = true) :
    (Nat.blt 47 c.toNat = true → c.isDigit = true ∧ nlSp c = c ∧ (c == ' ') = false) ∧
      (Nat.blt 47 c.toNat = false → nlSp c = ' ') := by
  unfold okC131 at h
  rw [strictB_eq'] at h
  have hn : (47 < c.toNat ∧ c.toNat < 58) ∨ c.toNat = 32 ∨ c.toNat = 10 := by
    revert h
    cases h1 : Nat.blt 47 c.toNat <;> cases h2 : Nat.blt c.toNat 58 <;>
      cases h3 : Nat.beq c.toNat 32 <;> cases h4 : Nat.beq c.toNat 10 <;>
      simp_all [andB, orB, Nat.blt_eq]
  have hc := Char.ofNat_toNat c
  constructor
  · intro hb
    have h47 : 47 < c.toNat := Nat.blt_eq.mp hb
    have h58 : c.toNat < 58 := by omega
    have : c.toNat = 48 ∨ c.toNat = 49 ∨ c.toNat = 50 ∨ c.toNat = 51 ∨ c.toNat = 52 ∨
        c.toNat = 53 ∨ c.toNat = 54 ∨ c.toNat = 55 ∨ c.toNat = 56 ∨ c.toNat = 57 := by omega
    rcases this with e | e | e | e | e | e | e | e | e | e <;> rw [e] at hc <;> subst hc <;> decide
  · intro hb
    have h47 : ¬ 47 < c.toNat := fun e => by simp [Nat.blt_eq.mpr e] at hb
    rcases hn with hn | e | e
    · omega
    all_goals rw [e] at hc; subst hc; decide

theorem good131R_cons {c : Char} {cs : List Char} (h : good131R (c :: cs) = true) :
    okC131 c = true ∧ good131R cs = true := andB_true h

theorem nums131R_cons (c : Char) (cs : List Char) (v : Nat) (b : Bool) :
    nums131R (c :: cs) v b = Bool.rec (motive := fun _ => List Nat)
      (Bool.rec (motive := fun _ => List Nat) (nums131R cs 0 false) (v :: nums131R cs 0 false) b)
      (nums131R cs (Nat.add (Nat.mul v 10) (Nat.sub c.toNat 48)) true) (Nat.blt 47 c.toNat) := rfl

theorem decVal_snoc (ds : List Char) (c : Char) :
    CFSG.KC.Str.decVal (ds ++ [c]) = CFSG.KC.Str.decVal ds * 10 + (c.toNat - 48) := by
  simp [CFSG.KC.Str.decVal, List.foldl_append]

theorem scan131_aux :∀ (cs acc : List Char), good131R cs = true → (∀ c ∈ acc, c.isDigit = true) →
    ((List.splitOnPPrepend (· == ' ') (cs.map nlSp) acc).all fun p => p.all Char.isDigit) = true ∧
      ((List.splitOnPPrepend (· == ' ') (cs.map nlSp) acc).filter fun p => !p.isEmpty).map
        CFSG.KC.Str.decVal = nums131R cs (CFSG.KC.Str.decVal acc.reverse) (!acc.isEmpty)
  | [], acc, _, hacc => by
    cases acc with
    | nil => simp [nums131R]
    | cons a acc =>
      refine ⟨?_, ?_⟩
      · simpa [and_comm] using hacc
      · simp [nums131R]
  | c :: cs, acc, h, hacc => by
    obtain ⟨hc, hcs⟩ := good131R_cons h
    obtain ⟨hd, hs⟩ := okC131_cases hc
    rw [nums131R_cons, List.map_cons]
    cases hb : Nat.blt 47 c.toNat
    · rw [hs hb, List.splitOnPPrepend_cons_pos (p := fun x => x == ' ') (by decide)]
      obtain ⟨g, e⟩ := scan131_aux cs [] hcs (by simp)
      rw [List.splitOnPPrepend_nil_right] at g e
      refine ⟨?_, ?_⟩
      · simp only [List.all_cons, Bool.and_eq_true]
        exact ⟨by simpa using hacc, g⟩
      · have hd0 : CFSG.KC.Str.decVal [] = 0 := rfl
        cases acc with
        | nil => simpa [hd0] using e
        | cons a acc => simpa [hd0] using e
    · obtain ⟨hdig, hnl, hsp⟩ := hd hb
      rw [hnl, List.splitOnPPrepend_cons_neg (p := fun x => x == ' ') hsp]
      obtain ⟨g, e⟩ := scan131_aux cs (c :: acc) hcs (by
        intro x hx
        rcases List.mem_cons.1 hx with rfl | hx
        · exact hdig
        · exact hacc x hx)
      refine ⟨g, ?_⟩
      rw [e, List.reverse_cons, decVal_snoc]
      rfl

theorem scan131 (cs : List Char) (h : good131R cs = true) :
    goodNl cs = true ∧ numsNl cs = nums131R cs 0 false := by
  obtain ⟨g, e⟩ := scan131_aux cs [] h (by simp)
  rw [List.splitOnPPrepend_nil_right] at g e
  refine ⟨?_, ?_⟩
  · unfold goodNl
    rw [List.splitOn_eq_splitOnP]
    exact g
  · unfold numsNl
    rw [List.splitOn_eq_splitOnP]
    exact e

end CertificateChecks.KernelCo1B.S0131301

end
