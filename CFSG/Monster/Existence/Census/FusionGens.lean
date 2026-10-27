module

public import CFSG.Monster.Existence.Census.TrialityWitnesses
public meta import Certificates.Data.CFSGNative.MonsterAxis.Dense
public meta import CFSG.Monster.Existence.Census.Rigid
public meta import CFSG.Monster.Existence.Census.TrialityWitnesses
public import CFSG.Monster.Existence.Census.FusionGensInputs
public import Certificates.Certificate6022
public import Certificates.Certificate6023
public import Certificates.Certificate6007
public import Certificates.Certificate1020
public import Certificates.Certificate1022
public import Certificates.Certificate3015
public import Certificates.Certificate3016
public import Certificates.Certificate3017
public import Certificates.Certificate3018

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Existence.Census

open CFSG.Monster CFSG.Monster.B CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.ScalarKernel CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated
  CFSG.Monster.AxisCount CFSG.Monster.B.TwoA.Census Matrix
open CFSG.Monster.B.Rep4371 hiding interp interp_eq_sum

theorem fusCheck_sign : fusCheckC (Native.mkCtx ()) 0 4 = true :=
  Certificates.certificate6022.1

theorem fusCheck_perm : fusCheckC (Native.mkCtx ()) 4 8 = true :=
  Certificates.certificate6022.2.1

theorem fusCheck_rest : fusCheckC (Native.mkCtx ()) 8 11 = true :=
  Certificates.certificate6022.2.2

theorem fusCheck_all (j : ℕ) (hj : j < 11) :
    checkRigid (Native.mkCtx ())
      ([Native.Gen.sign 3, Native.Gen.perm idArr] ++ [fusGen j])
      ([fusGen j, Native.Gen.rho (fusShift j)] ++ [Native.Gen.sign 3, Native.Gen.perm idArr]) =
      true := by
  have key : ∀ lo hi : ℕ, fusCheckC (Native.mkCtx ()) lo hi = true → lo ≤ j → j < hi →
      checkRigid (Native.mkCtx ())
        ([Native.Gen.sign 3, Native.Gen.perm idArr] ++ [fusGen j])
        ([fusGen j, Native.Gen.rho (fusShift j)] ++ [Native.Gen.sign 3, Native.Gen.perm idArr]) =
        true := by
    intro lo hi h hlo hhi
    have := List.all_eq_true.1 h j (List.mem_range.2 hhi)
    simpa [not_lt.2 hlo] using this
  by_cases h1 : j < 4
  · exact key 0 4 fusCheck_sign (Nat.zero_le _) h1
  · by_cases h2 : j < 8
    · exact key 4 8 fusCheck_perm (by omega) h2
    · exact key 8 11 fusCheck_rest (by omega) hj

theorem fusGen_ne_tau (j : ℕ) : ¬ fusGen j = Native.Gen.tau := by
  unfold fusGen fusGens
  rcases Nat.lt_or_ge j 11 with h | h
  · interval_cases j <;> simp
  · rw [List.getD_eq_default _ _ (by simp; omega)]
    simp

theorem fusGens_comm
    (j : ℕ) (hj : j < 11) :
    (fusGen j).toLin * (cosetRep 1 : SpaceB ≃ₗ[ℚ] SpaceB) =
      (cosetRep 1 : SpaceB ≃ₗ[ℚ] SpaceB) * rhoEquiv (pauliQ (fusShift j)) * (fusGen j).toLin := by
  have h := wordLin_eq_of_check (w₁ := [Native.Gen.sign 3, Native.Gen.perm idArr] ++ [fusGen j])
    (w₂ := [fusGen j, Native.Gen.rho (fusShift j)] ++ [Native.Gen.sign 3, Native.Gen.perm idArr])
    (by
      intro g hg
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with (rfl | rfl) | rfl
      · simp
      · simp
      · exact fusGen_ne_tau j)
    (by
      intro g hg
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with (rfl | rfl) | rfl | rfl
      · exact fusGen_ne_tau j
      · simp
      · simp
      · simp)
    (fusCheck_all j hj)
  have h1 := wordLin_hWord 1
  rw [hWord_one] at h1
  rw [wordLin_append, wordLin_append, h1] at h
  simp only [wordLin_cons, wordLin_nil, one_mul] at h
  rw [Native.Gen.toLin_rho] at h
  simpa [mul_assoc] using h

end CFSG.Monster.Existence.Census
