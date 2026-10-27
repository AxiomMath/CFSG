module

public import Certificates.Data.Th687.MFactsC
import Certificates.Kernel.Th.Fam.C687011
import Certificates.Kernel.Th.Fam.Ctx

public section

namespace Certificates

open CFSG.KC.Th.Expr CFSG.Sporadic.Th.Native CFSG.Sporadic.Th.Max3 CFSG.Sporadic.Th.Recog
open CFSG.Sporadic.Th.Recog.MFactsCData CertificateChecks.KernelTh.Fam.F11

private theorem eqR (e f : TE) : eqRows e.rows f.rows = bq e f := by
  kernel_exact eqRows_eq_beq CertificateChecks.KernelTh.Fam.thCtx e f

private theorem commR_eq (e f : TE) : commR e.rows f.rows = cm e f := by
  kernel_exact eqRows_eq_beq CertificateChecks.KernelTh.Fam.thCtx (.mul e f) (.mul f e)

private theorem mulT (e f : TE) : (TE.mul e f).rows = mulRows e.rows f.rows := rfl

private theorem powT (e : TE) (n : Nat) : (TE.pow e n).rows = powRows e.rows n := rfl

private theorem oneT : TE.one.rows = idRows := rfl

private theorem aT : TE.a.rows = rowsA := rfl

private theorem nfT (k : Fin 512) : (TE.nf k).rows = rowsNfAt k := rfl

private theorem rc : rowsWJ 2 = cT.rows := rfl
private theorem rd : rowsWJ 3 = dT.rows := rfl
private theorem re : rowsWJ 4 = eT.rows := rfl
private theorem rs : rowsWJ 5 = sT.rows := rfl
private theorem rt : rowsWJ 6 = tT.rows := rfl
private theorem ru : rowsWJ 7 = uT.rows := rfl

private theorem lt8 (l : Fin 4) : l.val < 8 := Nat.lt_of_lt_of_le l.isLt (by decide)

private theorem e8getN (Z E0 E1 : Array V4) (n : Nat) (h : n < 8) :
    (e8Tab Z E0 E1)[n]! = rowsE8 Z E0 E1 ⟨n, h⟩ :=
  e8Tab_get Z E0 E1 ⟨n, h⟩

private theorem e8get4 (Z E0 E1 : Array V4) (l : Fin 4) :
    (e8Tab Z E0 E1)[l.val]! = rowsE8 Z E0 E1 ⟨l.val, lt8 l⟩ :=
  e8getN Z E0 E1 l.val (lt8 l)

private theorem e8getLt (Z E0 E1 : Array V4) (l : Fin 8) (l' : Fin l.val) :
    (e8Tab Z E0 E1)[l'.val]! = rowsE8 Z E0 E1 ⟨l'.val, l'.isLt.trans l.isLt⟩ :=
  e8getN Z E0 E1 l'.val (l'.isLt.trans l.isLt)

private theorem tg0_lt (i : Fin 5) : tg0 i < 8 := by fin_cases i <;> decide

private theorem tg1_lt (i : Fin 5) : tg1 i < 8 := by fin_cases i <;> decide

private theorem e8tg0 (Z E0 E1 : Array V4) (i : Fin 5) :
    (e8Tab Z E0 E1)[neTgt0[i.val]!]! = rowsE8 Z E0 E1 ⟨tg0 i, tg0_lt i⟩ := by
  fin_cases i <;> exact e8getN Z E0 E1 _ _

private theorem e8tg1 (Z E0 E1 : Array V4) (i : Fin 5) :
    (e8Tab Z E0 E1)[neTgt1[i.val]!]! = rowsE8 Z E0 E1 ⟨tg1 i, tg1_lt i⟩ := by
  fin_cases i <;> exact e8getN Z E0 E1 _ _

private theorem ofFn8get4 (f : Fin 8 → Array V4) (l : Fin 4) :
    (Array.ofFn f)[l.val]! = f ⟨l.val, lt8 l⟩ := by
  rw [getElem!_pos _ _ (by simp only [Array.size_ofFn]; exact lt8 l)]
  simp only [Array.getElem_ofFn]

private theorem lk5 (a₀ a₁ a₂ a₃ a₄ : TE) (i : Fin 5) :
    #[a₀.rows, a₁.rows, a₂.rows, a₃.rows, a₄.rows][i.val]! =
      ([a₀, a₁, a₂, a₃, a₄].getD i.val .one).rows := by
  fin_cases i <;> rfl

private theorem lk6 (a₀ a₁ a₂ a₃ a₄ a₅ : TE) (i : Fin 6) :
    #[a₀.rows, a₁.rows, a₂.rows, a₃.rows, a₄.rows, a₅.rows][i.val]! =
      ([a₀, a₁, a₂, a₃, a₄, a₅].getD i.val .one).rows := by
  fin_cases i <;> rfl

private theorem lk7 (a₀ a₁ a₂ a₃ a₄ a₅ a₆ : TE) (i : Fin 7) :
    #[a₀.rows, a₁.rows, a₂.rows, a₃.rows, a₄.rows, a₅.rows, a₆.rows][i.val]! =
      ([a₀, a₁, a₂, a₃, a₄, a₅, a₆].getD i.val .one).rows := by
  fin_cases i <;> rfl

private theorem check0 : checkR687011 () = true := by
  simp only [checkR687011, rc, rd, re, rs, rt, ru, rowsUI, rowsX1, rowsW1, rowsW1I, rowsY1,
    rowsX2, rowsW2, ← mulT, ← powT, eqR, commR_eq]
  kernel_exact ok687011R

private theorem check1 : checkE687011 () = true := by
  simp only [checkE687011, Fin.getElem!_fin, rc, rd, re, rs, rt, ru, rowsUI, rowsE0, rowsE1,
    e8Tab_get, e8getLt, rowsE8, ← aT, ← mulT, ← powT, eqR, commR_eq]
  kernel_exact ok687011E

private theorem check2 : checkN687011 () = true := by
  simp only [checkN687011, Fin.getElem!_fin, rc, rd, re, rs, rt, ru, rowsUI, rowsE0, rowsE1,
    e8tg0, e8tg1, rowsE8, neTab, ← aT, ← mulT, ← powT, lk5, eqR, commR_eq]
  kernel_exact ok687011N

private theorem check3 : checkCE687011 () = true := by
  simp only [checkCE687011, Fin.getElem!_fin, rc, rd, re, rs, rt, ru, rowsUI, rowsE0, rowsE1,
    rowsW1, rowsW2, e8Tab_get, rowsE8, preTab_get, rowsPRE, rowsNfTab_get, ← nfT, ← aT, ← mulT,
    ← powT, eqR, commR_eq]
  kernel_exact ok687011CE

private theorem check4 : checkC687011 () = true := by
  simp only [checkC687011, Fin.getElem!_fin, rc, rd, re, rs, rt, ru, rowsUI, rowsE0, ceTab,
    ceiTab, cnTab, cniTab, ← oneT, ← mulT, ← powT, lk6, lk7, eqR, commR_eq]
  kernel_exact ok687011C

private theorem check5 : checkA687011 () = true := by
  simp only [checkA687011, Fin.getElem!_fin, rc, rd, re, rs, rt, ru, rowsUI, rowsE0, rowsE1,
    ofFn8get4, e8get4, rowsE8, rowsNfTab_get, ceTab, ceiTab, cnTab, cniTab, ← nfT, ← aT, ← oneT,
    ← mulT, ← powT, lk6, lk7, eqR, commR_eq]
  kernel_exact ok687011A

open CFSG.Sporadic.Th.Native CFSG.Sporadic.Th.Max3 in
open CFSG.Sporadic.Th.Recog.MFactsCData in
theorem certificate687011 :
    checkR687011 () = true ∧
      checkE687011 () = true ∧
      checkN687011 () = true ∧
      checkCE687011 () = true ∧
      checkC687011 () = true ∧
      checkA687011 () = true :=
  ⟨check0, check1, check2, check3, check4, check5⟩

end Certificates
