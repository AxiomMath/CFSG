module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P514Lab
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P512Base
public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.Quasithin.Fan86

namespace P516

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T P514

variable {V G : Type} [Group G] [MulAction G V] {Γ : SimpleGraph V}

structure Sit (T : Track Γ G) (z : G) (a r m : ℤ) : Prop where
  xi : InXi T
  zz : z ∈ T.line.ZZ
  ne : z ≠ 1
  fix : T.line.IsCoreFix z a (a + 2) (a - r) (a + 2 + r)
  cinv : z ∈ Cinv G (T.line.vert (a + 1))
  val : valence Γ (T.line.vert (a + 1)) ≠ 3
  r7 : 7 ≤ r
  hm : 2 * m = r + 3

namespace Sit

variable {T : Track Γ G} {z : G} {a r m : ℤ}

theorem fixes (S : Sit T z a r m) (i : ℤ) :
    z • T.line.vert i = T.line.vert i ↔ a - r ≤ i ∧ i ≤ a + 2 + r :=
  S.fix.fix i

theorem lab_fix (S : Sit T z a r m) (n : ℤ) :
    T.line.IsCoreFix (lab T z n) (a + 2 * n) (a + 2 * n + 2) (a - r + 2 * n)
      (a + 2 + r + 2 * n) := by
  have := isCoreFix_lab T n S.fix
  rwa [show a + 2 + 2 * n = a + 2 * n + 2 by ring] at this

theorem lab_fixes (S : Sit T z a r m) (n i : ℤ) :
    lab T z n • T.line.vert i = T.line.vert i ↔ a - r + 2 * n ≤ i ∧ i ≤ a + 2 + r + 2 * n :=
  (S.lab_fix n).fix i

theorem lab_cinv (S : Sit T z a r m) (n : ℤ) :
    lab T z n ∈ Cinv G (T.line.vert (a + 1 + 2 * n)) := by
  have h := P512.cinv_conj S.cinv (T.τ ^ n)
  rw [T.zpow_smul_vert, ← zpow_neg] at h
  exact h

theorem lab_zz (S : Sit T z a r m) (n : ℤ) : lab T z n ∈ T.line.ZZ := lab_mem_ZZ T S.zz n

theorem lab_ne (S : Sit T z a r m) (n : ℤ) : lab T z n ≠ 1 := lab_ne_one T S.ne n

theorem lab_sq (S : Sit T z a r m) (n : ℤ) : lab T z n * lab T z n = 1 :=
  lab_mul_self T S.zz.1 n

theorem cfix (F : FanTree Γ G) (h40 : Fan40 F) (h53b : Fan53b F) (S : Sit T z a r m) :
    T.line.IsCoreCFix z a (a + 2) (a - r) (a + 2 + r) :=
  ⟨S.fix.fix, h53b h40 T.line z a (a + 2) S.zz S.fix.core⟩

theorem lab_cfix (F : FanTree Γ G) (h40 : Fan40 F) (h53b : Fan53b F) (S : Sit T z a r m)
    (n : ℤ) : T.line.IsCoreCFix (lab T z n) (a + 2 * n) (a + 2 * n + 2) (a - r + 2 * n)
      (a + 2 + r + 2 * n) := by
  have := isCoreCFix_lab F T n (S.cfix F h40 h53b)
  rwa [show a + 2 + 2 * n = a + 2 * n + 2 by ring] at this

theorem inPos (F : FanTree Γ G) (h40 : Fan40 F) (h53b : Fan53b F) (S : Sit T z a r m) :
    T.line.InPos z (lab T z m) a (a + 2) (a - r) (a + 2 + r) (a + 2 * m) (a + 2 * m + 2)
      (a - r + 2 * m) (a + 2 + r + 2 * m) := by
  have hm := S.hm
  exact ⟨S.cfix F h40 h53b, S.lab_cfix F h40 h53b m, 1, 1, Or.inr rfl, Or.inr rfl, by omega,
    by omega⟩

end Sit

end P516

end CFSG.Quasithin.Fan86
