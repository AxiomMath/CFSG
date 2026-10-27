module

public import Certificates.Data.M23Group

public section

namespace CFSG

namespace M23.M23Group

open scoped Pointwise

@[expose] def inH1 (p : Perm23) (hp : p ∈ H0) (h0 : p 0 = 0) : H1 :=
  ⟨⟨p, hp⟩, by simpa [Equiv.Perm.smul_def] using h0⟩

@[expose] def inH2 (p : Perm23) (hp : p ∈ H0) (h0 : p 0 = 0) (h1 : p 1 = 1) : H2 :=
  ⟨inH1 p hp h0, by change p 1 = 1; exact h1⟩

@[expose] def inH3 (p : Perm23) (hp : p ∈ H0) (h0 : p 0 = 0) (h1 : p 1 = 1)
    (h2 : p 2 = 2) : H3 :=
  ⟨inH2 p hp h0 h1, by change p 2 = 2; exact h2⟩

@[expose] def inH4 (p : Perm23) (hp : p ∈ H0) (h0 : p 0 = 0) (h1 : p 1 = 1)
    (h2 : p 2 = 2) (h3 : p 3 = 3) : H4 :=
  ⟨inH3 p hp h0 h1 h2, by change p 3 = 3; exact h3⟩

@[expose] def inH5 (p : Perm23) (hp : p ∈ H0) (h0 : p 0 = 0) (h1 : p 1 = 1)
    (h2 : p 2 = 2) (h3 : p 3 = 3) (h4 : p 4 = 4) : H5 :=
  ⟨inH4 p hp h0 h1 h2 h3, by change p 4 = 4; exact h4⟩

@[expose] def S0 (i : Fin 2) : H0 := ⟨baseGen i, baseGen_mem i⟩

@[expose] def S1 (i : Fin 4) : H1 :=
  inH1 (h1Gen i) (h1Gen_mem i) (by
    fin_cases i
    · exact g2_fix0
    · exact g3_fix0
    · exact g4_fix0
    · exact g5_fix0)

@[expose] def S2 (i : Fin 5) : H2 :=
  inH2 (h2Gen i) (h2Gen_mem i)
    (by fin_cases i <;> simp [h2Gen, g6_fix01, g7_fix01, g8_fix01, g9_fix01,
      g10_fix01])
    (by fin_cases i <;> simp [h2Gen, g6_fix01, g7_fix01, g8_fix01, g9_fix01,
      g10_fix01])

@[expose] def S3 (i : Fin 2) : H3 :=
  inH3 (h3Gen i) (h3Gen_mem i)
    (by fin_cases i <;> simp [h3Gen, g11_fix012, g12_fix012])
    (by fin_cases i <;> simp [h3Gen, g11_fix012, g12_fix012])
    (by fin_cases i <;> simp [h3Gen, g11_fix012, g12_fix012])

@[expose] def S4 (i : Fin 3) : H4 :=
  inH4 (h4Gen i) (h4Gen_mem i)
    (by fin_cases i <;> simp [h4Gen, g13_fix0123, g14_fix0123, g15_fix0123])
    (by fin_cases i <;> simp [h4Gen, g13_fix0123, g14_fix0123, g15_fix0123])
    (by fin_cases i <;> simp [h4Gen, g13_fix0123, g14_fix0123, g15_fix0123])
    (by fin_cases i <;> simp [h4Gen, g13_fix0123, g14_fix0123, g15_fix0123])

@[expose] def S5 (i : Fin 4) : H5 :=
  inH5 (h5Gen i) (h5Gen_mem i)
    (by fin_cases i <;> simp [h5Gen, g16_fix01234, g17_fix01234, g18_fix01234,
      g19_fix01234])
    (by fin_cases i <;> simp [h5Gen, g16_fix01234, g17_fix01234, g18_fix01234,
      g19_fix01234])
    (by fin_cases i <;> simp [h5Gen, g16_fix01234, g17_fix01234, g18_fix01234,
      g19_fix01234])
    (by fin_cases i <;> simp [h5Gen, g16_fix01234, g17_fix01234, g18_fix01234,
      g19_fix01234])
    (by fin_cases i <;> simp [h5Gen, g16_fix01234, g17_fix01234, g18_fix01234,
      g19_fix01234])

@[expose] def S6 : Fin 0 → H6 := Fin.elim0

@[expose] def t0 (x : Fin 23) : H0 := evalGroupWord S0 (T0 x)
@[expose] def t1 (x : Fin 23) : H1 := evalGroupWord S1 (T1 x)
@[expose] def t2 (x : Fin 23) : H2 := evalGroupWord S2 (T2 x)
@[expose] def t3 (x : Fin 23) : H3 := evalGroupWord S3 (T3 x)
@[expose] def t4 (x : Fin 23) : H4 := evalGroupWord S4 (T4 x)
@[expose] def t5 (x : Fin 23) : H5 := evalGroupWord S5 (T5 x)

@[expose] def Q (x : Fin 23) : Prop := x = 4 ∨ x = 10 ∨ x = 16

@[expose] def R (x : Fin 23) : Prop :=
  x = 5 ∨ x = 6 ∨ x = 7 ∨ x = 8 ∨ x = 9 ∨ x = 11 ∨ x = 12 ∨
    x = 13 ∨ x = 14 ∨ x = 15 ∨ x = 17 ∨ x = 18 ∨ x = 19 ∨ x = 20 ∨
    x = 21 ∨ x = 22

end M23.M23Group

end CFSG
