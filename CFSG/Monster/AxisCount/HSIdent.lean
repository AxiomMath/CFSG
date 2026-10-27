module

public import CFSG.Monster.AxisCount.HSIdentSmall
public import CFSG.Monster.AxisCount.HSIdentRec0
public import CFSG.Monster.AxisCount.HSIdentRec1
public import CFSG.Monster.AxisCount.HSIdentRec2
public import CFSG.Monster.AxisCount.HSIdentRec3
public import CFSG.Monster.AxisCount.HSIdentRec4
public import CFSG.Monster.AxisCount.HSIdentRec5
public import CFSG.Monster.AxisCount.HSIdentRec6
public import CFSG.Monster.AxisCount.HSIdentRec7
public import Certificates.Certificate16018

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.AxisCount.HS

open CFSG.Monster CFSG.Monster.Griess CFSG.Monster.B.Short

theorem recShards_ok :
    ∀ s ∈ recShards, ∀ r, s.2.1 ≤ r → r < s.2.2 → ∀ ε, RecSpec s.1 r ε := by
  intro s hs
  simp only [recShards, List.mem_append] at hs
  rcases hs with (((((((h | h) | h) | h) | h) | h) | h) | h)
  · exact rec_ok_0 s h
  · exact rec_ok_1 s h
  · exact rec_ok_2 s h
  · exact rec_ok_3 s h
  · exact rec_ok_4 s h
  · exact rec_ok_5 s h
  · exact rec_ok_6 s h
  · exact rec_ok_7 s h

theorem recShards_cover : ∀ i : Fin 12, ∀ r, r < Cert.nW i →
    ∃ s ∈ recShards, s.1 = i ∧ s.2.1 ≤ r ∧ r < s.2.2 :=
  Certificates.certificate16018

theorem hs_rec
    (i : Fin 12) (r : Nat) (hr : r < Cert.nW i) (ε : Bool) : RecSpec i r ε := by
  obtain ⟨s, hs, rfl, h1, h2⟩ := recShards_cover i r hr
  exact recShards_ok s hs r h1 h2 ε

theorem hs_stab :
    ∀ (i : Fin 12), ∀ k, k < 2 → wordLin (uW i k) (vv i) = vv i :=
  stabAll_ok

theorem hs_trans
    (i : Fin 12) (r : Nat) (hr : r < Cert.nW i) (ε : Bool) :
    wordLin (xW i r ε) (vv i) = vv (Cert.tFin i r ε) := (hs_rec i r hr ε).1

theorem hs_e1L
    (i : Fin 12) (r : Nat) (hr : r < Cert.nW i) (ε : Bool) :
    bbL i r ε < 10 ∧ wordLin (xW i r ε) (wordLin (Cert.gammaW i) aStarMinus) =
      wordLin (hppL i r ε ++ Cert.gammaW (Cert.tFin i r ε))
        (wordLin (babyW (bbL i r ε)) aStarMinus) := (hs_rec i r hr ε).2.1

theorem hs_e2L
    (i : Fin 12) (r : Nat) (hr : r < Cert.nW i) (ε : Bool) :
    wordLin (hppL i r ε) aStar = aStar := (hs_rec i r hr ε).2.2

theorem hs_e1U
    (i : Fin 12) (k : Nat) (hk : k < 2) :
    bbU i k < 10 ∧ wordLin (uW i k) (wordLin (Cert.gammaW i) aStarMinus) =
      wordLin (hppU i k ++ Cert.gammaW i) (wordLin (babyW (bbU i k)) aStarMinus) :=
  e1UAll_ok i k hk

theorem hs_e2U
    (i : Fin 12) (k : Nat) (hk : k < 2) : wordLin (hppU i k) aStar = aStar :=
  e2UAll_ok i k hk

theorem hs_trace_injective :
    Function.Injective fun i : Fin 12 => trA2 (vv i) := trace_injective

end CFSG.Monster.AxisCount.HS
