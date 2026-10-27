
module

public import CFSG.Quasithin.Vol2.GoldschmidtF431TwoF4SpecBase

public import Certificates.Certificate4180
public import Certificates.Data.TwoF4LieCheck
public import CFSG.Monster.B.Co2.PermArr
public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.SetTheory.Cardinal.Finite
public import CFSG.Quasithin.Vol2.GoldschmidtF45RuArr
public import CFSG.Quasithin.Vol2.GoldschmidtF45RuModel
public import CFSG.Quasithin.Recognition.RuTypeJ47Cert

public section

namespace CFSG.Quasithin.H13.F431.TwoF4

open CFSG.Quasithin CFSG.Quasithin.RuType.J47 CFSG.Quasithin.H13.F45Ru
  CFSG.Sporadic.Schreier.Tits CFSG.RuF45 CFSG.TwoF4Lie CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native

open scoped Pointwise

set_option linter.unusedSectionVars false

theorem tEl_eq : tEl.1 = Certificates.c4180T := by
  have e : decodeWord tWord =
      [(3, true), (2, true), (3, true), (0, true), (3, true), (2, true), (3, false)] := by decide
  simp [tEl, wEl, e, wordElt, letterElt, kgen_val, Certificates.c4180T, mul_assoc]

theorem cEl_eq : cEl.1 = Certificates.c4180C := by
  have e : decodeWord cWord = [(1, true), (2, true), (1, false), (2, true), (1, true), (2, true),
      (1, true), (2, true), (2, true), (0, true)] := by decide
  simp [cEl, wEl, e, wordElt, letterElt, kgen_val, Certificates.c4180C, mul_assoc]

theorem tEl_mem_S : tEl.1 ∈ twoF4S := by
  obtain ⟨⟨h0, hL, -⟩, -⟩ := Certificates.certificate4180
  rw [mem_twoF4S_iff tEl.2, tEl_eq]
  exact ⟨h0, hL⟩

theorem tEl_invol : tEl.1 * tEl.1 = 1 ∧ tEl.1 ≠ 1 := by
  obtain ⟨⟨-, -, h2, h1, -⟩, -⟩ := Certificates.certificate4180
  rw [tEl_eq]
  exact ⟨h2, h1⟩

theorem cEl_pow : cEl.1 ^ 3 = 1 ∧ cEl.1 ≠ 1 := by
  obtain ⟨-, ⟨h3, h1, -⟩, -⟩ := Certificates.certificate4180
  rw [cEl_eq]
  exact ⟨h3, h1⟩

theorem cEl_comm : cEl.1 * tEl.1 = tEl.1 * cEl.1 := by
  obtain ⟨-, ⟨-, -, hc⟩, -⟩ := Certificates.certificate4180
  rw [cEl_eq, tEl_eq]
  exact hc

end CFSG.Quasithin.H13.F431.TwoF4
