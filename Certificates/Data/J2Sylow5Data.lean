module

public import CFSG.Sporadic.Bridge.J2Native

public section

namespace CFSG.Sporadic.J2.Sylow5Data

open CFSG.Sporadic.Bridge.J2

@[expose] def wg : List (ℕ × Bool) := [(1, false), (0, false), (1, false), (0, false), (1, true), (0, false), (1, false), (0, false), (1, true), (0, false), (1, false), (0, false), (1, true), (0, false), (1, false), (1, false), (0, true), (1, false), (0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, false), (0, true), (1, false), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, false), (1, false), (0, false), (1, true), (0, false), (1, true), (0, false), (1, false), (0, false), (1, false), (0, false), (1, true), (0, false), (1, false), (0, false), (1, true)]

@[expose] def ZP5a : List (List ℕ) := lwordL natX natXi wP5a idL

@[expose] def ZP5b : List (List ℕ) := lwordL natX natXi wP5b idL

@[expose] def Zg : List (List ℕ) := lwordL natX natXi wg idL

@[expose] def mZg : List (List ℕ) := [[0,0,4,3,0,4,2,3,0,1,1,4,0,0],[0,3,4,4,4,1,0,1,0,0,4,4,2,2],[4,4,2,3,3,0,3,1,0,2,3,4,4,0],[0,3,2,4,4,0,3,0,0,4,4,2,0,0],[0,2,0,3,4,0,0,1,0,0,3,1,4,2],[2,1,3,2,3,1,0,0,0,4,3,2,0,1],[3,0,1,4,1,0,0,1,0,2,0,4,3,0],[2,0,4,4,3,1,4,1,0,4,2,0,2,3],[2,2,1,0,0,2,3,4,0,3,3,1,0,1],[3,0,2,1,3,4,4,3,0,3,0,3,4,0],[1,3,2,3,3,0,3,2,1,1,4,4,4,0],[1,2,4,4,3,2,0,3,3,2,1,0,3,3],[1,3,1,3,0,4,4,1,0,4,0,4,4,0],[4,0,1,0,1,4,1,4,0,0,1,3,1,3]]

theorem lwordL_wg : lwordL natX natXi wg idL = mZg := by decide +kernel

theorem ZP5a_eq : ZP5a = mP5a := lwordL_sylow.2.2.2.2.2.1

theorem ZP5b_eq : ZP5b = mP5b := lwordL_sylow.2.2.2.2.2.2

end CFSG.Sporadic.J2.Sylow5Data
