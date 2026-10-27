module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmPlusWeyl

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.LieType.Universal.Spin
open CFSG.StandardType

@[expose] def omNatWt (n : ℕ) : Fin n → ℤ :=
  omFromStdD2 n (fun a => if a.val = 0 then 1 else 0)

private def c2slomqon_unit (n : ℕ) (q : Fin n) (m : ℤ) : Fin n → ℤ :=
  fun b => if b = q then m else 0

private theorem c2slomqon_unit_self {n : ℕ} (q : Fin n) (m : ℤ) :
    c2slomqon_unit n q m q = m := by
  simp [c2slomqon_unit]

private theorem c2slomqon_unit_of_ne {n : ℕ} {b q : Fin n} (h : b ≠ q) (m : ℤ) :
    c2slomqon_unit n q m b = 0 := by
  simp [c2slomqon_unit, h]

private theorem c2slomqon_toStdD_omNatWt {n : ℕ} (hn : 2 ≤ n) (i0 : Fin n) (h0 : i0.val = 0) :
    toStdD n (omNatWt n) = c2slomqon_unit n i0 2 := by
  rw [show omNatWt n = omFromStdD2 n (fun a => if a.val = 0 then (1 : ℤ) else 0) from rfl,
    toStdD_omFromStdD2 hn]
  funext b
  by_cases hb : b = i0
  · subst hb
    simp [c2slomqon_unit, h0]
  · have hb' : b.val ≠ 0 := fun hv => hb (Fin.ext (by rw [hv, h0]))
    simp [c2slomqon_unit, hb, hb']

private theorem c2slomqon_toStdD_orbit {n : ℕ} (hn : 2 ≤ n) (i0 : Fin n) (h0 : i0.val = 0)
    {w : (coxeterMatrix (isFiniteType_cartanD n)).Group} {π : Equiv.Perm (Fin n)}
    {s : Fin n → ℤ} (h : OmRealizes n w π s) :
    toStdD n (weylAction (isFiniteType_cartanD n) w (omNatWt n)) =
      c2slomqon_unit n (π i0) (2 * s i0) := by
  rw [h (omNatWt n), c2slomqon_toStdD_omNatWt hn i0 h0]
  funext b
  by_cases hb : π.symm b = i0
  · have hb' : b = π i0 := by rw [← hb, Equiv.apply_symm_apply]
    rw [hb, c2slomqon_unit_self, hb', c2slomqon_unit_self]
    ring
  · have hb' : b ≠ π i0 := fun hh => hb (by rw [hh, Equiv.symm_apply_apply])
    rw [c2slomqon_unit_of_ne hb 2, c2slomqon_unit_of_ne hb' (2 * s i0)]
    ring

theorem weylAction_simple_omNatWt {n : ℕ} (hn : 3 ≤ n) {k : Fin n} (hk : k.val ≠ 0) :
    weylAction (isFiniteType_cartanD n)
        ((coxeterMatrix (isFiniteType_cartanD n)).toCoxeterSystem.simple k) (omNatWt n) =
      omNatWt n := by
  have hn2 : 2 ≤ n := by omega
  have h0 : (⟨0, by omega⟩ : Fin n).val = 0 := rfl
  have hne_k : (⟨0, by omega⟩ : Fin n) ≠ k := fun hh => hk (congrArg Fin.val hh).symm
  have key : toStdD n
      (weylAction (isFiniteType_cartanD n)
        ((coxeterMatrix (isFiniteType_cartanD n)).toCoxeterSystem.simple k) (omNatWt n)) =
      c2slomqon_unit n (⟨0, by omega⟩ : Fin n) 2 := by
    by_cases hlt : k.val + 1 < n
    · have h := c2slomqon_toStdD_orbit hn2 (⟨0, by omega⟩ : Fin n) h0
        (omRealizes_simple_of_lt (n := n) hlt)
      have hne1 : (⟨0, by omega⟩ : Fin n) ≠ ⟨k.val + 1, hlt⟩ := fun hh => by
        have hv := congrArg Fin.val hh
        simp only [Fin.val_mk] at hv
        omega
      rw [Equiv.swap_apply_of_ne_of_ne hne_k hne1] at h
      simpa using h
    · have h := c2slomqon_toStdD_orbit hn2 (⟨0, by omega⟩ : Fin n) h0
        (omRealizes_simple_of_not_lt (n := n) hn2 hlt)
      have hne1 : (⟨0, by omega⟩ : Fin n) ≠ ⟨n - 2, by omega⟩ := fun hh => by
        have hv := congrArg Fin.val hh
        simp only [Fin.val_mk] at hv
        omega
      have hif : (if n ≤ (⟨0, by omega⟩ : Fin n).val + 2 then (-1 : ℤ) else 1) = 1 :=
        if_neg (by simp only [Fin.val_mk]; omega)
      rw [Equiv.swap_apply_of_ne_of_ne hne1 hne_k, hif] at h
      simpa using h
  apply toStdD_injective n
  rw [key, c2slomqon_toStdD_omNatWt hn2 (⟨0, by omega⟩ : Fin n) h0]

end CFSG.LocalAnalysis.WeakClosure81
