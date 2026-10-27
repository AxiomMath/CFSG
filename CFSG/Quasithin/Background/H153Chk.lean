module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Milestones.ASVolI.H1
public import CFSG.Quasithin.Background.HZ82Base
public import CFSG.Quasithin.Background.HZCoc24Gen

public section

namespace CFSG.Quasithin.H153

open CFSG.ASVolI.ChH CFSG.Open CFSG.Monster.Code CFSG.Quasithin CFSG.Quasithin.H.Mathieu
  CFSG.Quasithin.H.Coc24 CFSG.Quasithin.H.ModChk CFSG.Quasithin.H.FixSyl CFSG.Quasithin.H.ZTrans

theorem ks_trans_check : ∀ c < 64, ∀ m ∈ combos w0Basis,
    act11 (ksC c) m ^^^ m = 0 ∨ act11 (ksC c) m ^^^ m = 31 := by
  decide +kernel

theorem w0_of_gens_check : ∀ m < 2048,
    (∀ i < 6, act11 (ksArr i) m ^^^ m = 0 ∨ act11 (ksArr i) m ^^^ m = 31) →
      m ∈ combos w0Basis := by
  decide +kernel

theorem ks_faith_check : ∀ c < 64, (∀ b ∈ w0Basis, act11 (ksC c) b = b) → c = 0 := by
  decide +kernel

theorem w0Basis_mem_combos : ∀ b ∈ w0Basis, b ∈ combos w0Basis := by decide +kernel

theorem pat_check : ∀ ε : Fin 7 → Bool, ε 3 = false →
    ∃ c : Fin 64, ∀ i : Fin 7, act11 (ksC c) (w0Basis.getD i 0) =
      w0Basis.getD i 0 ^^^ (if ε i then 31 else 0) := by
  decide +kernel

theorem w0Basis_getD : ∀ a ∈ w0Basis, ∃ i : Fin 7, w0Basis.getD i 0 = a := by decide +kernel

theorem w0Basis_three : w0Basis.getD ((3 : Fin 7) : ℕ) 0 = 31 := by decide

theorem w0Basis_getD_mem : ∀ i : Fin 7, w0Basis.getD i 0 ∈ combos w0Basis := by decide +kernel

@[expose] def xiData : List (ℕ × ℕ) :=
  [(1, 3), (1, 28), (1, 32), (1, 64), (1, 128), (1, 256), (1, 1024), (2, 512), (4, 5), (5, 9),
    (6, 14)]

theorem xi_fix : ∀ e ∈ xiData, 0 < e.1 ∧ e.1 < 64 ∧ act11 (ksC e.1) e.2 = e.2 := by
  decide +kernel

theorem xi_span : ∀ m < 2 ^ 11, m ∈ combos (xiData.map Prod.snd) := by decide +kernel

end CFSG.Quasithin.H153
