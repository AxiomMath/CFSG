module

public import CFSG.Certificates.Kernel.Co2KillSound
public import CFSG.Certificates.Kernel.Co2.Bound3.Model
public import CFSG.Certificates.Kernel.CosetBounds
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelCo2

open CFSG.KC CFSG.KC.LceS CFSG.KC.HOrb CFSG.KC.Co2K CFSG.Certificates.Co2Kill

theorem dec7_one : dec7 ONE7 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp only [Matrix.one_apply] <;> decide

theorem wf7_one : wf7 ONE7 = true := by quickRfl

theorem wf7_neg : wf7 NEG7 = true := by quickRfl

theorem evalE_dec (FS : ℕ → ℕ) (w : ℕ)
    (hFS : ∀ q < wLen w, wf7 (FS (Nat.shiftRight (byte (wWord w) q) 1)) = true) :
    wf7 (evalE FS w) = true ∧ dec7 (evalE FS w) =
      ((List.range (wLen w)).map fun q => dec7 (FS (Nat.shiftRight (byte (wWord w) q) 1))).prod := by
  have key : ∀ n ≤ wLen w,
      wf7 (Nat.rec (motive := fun _ => Nat) ONE7
        (fun q acc => CFSG.KC.Loop.strictN acc (fun x => mul7 x (FS (Nat.shiftRight (byte (wWord w) q) 1))))
        n) = true ∧
      dec7 (Nat.rec (motive := fun _ => Nat) ONE7
        (fun q acc => CFSG.KC.Loop.strictN acc (fun x => mul7 x (FS (Nat.shiftRight (byte (wWord w) q) 1))))
        n) = ((List.range n).map fun q => dec7 (FS (Nat.shiftRight (byte (wWord w) q) 1))).prod := by
    intro n
    induction n with
    | zero => exact fun _ => ⟨wf7_one, dec7_one⟩
    | succ n ih =>
      intro hn
      obtain ⟨h1, h2⟩ := ih (by omega)
      have hs : ∀ (y : ℕ) (k : ℕ → ℕ), CFSG.KC.Loop.strictN y k = k y := fun y k => by
        cases y <;> rfl
      change wf7 (CFSG.KC.Loop.strictN _ _) = true ∧ dec7 (CFSG.KC.Loop.strictN _ _) = _
      rw [hs]
      obtain ⟨m1, m2⟩ := mul7_sound h1 (hFS n (by omega))
      refine ⟨m1, ?_⟩
      rw [m2, h2, List.range_succ, List.map_append, List.prod_append]
      simp
  exact key _ le_rfl

@[expose] noncomputable def unit7 (X : ℕ) (h : invol7 X = true) : (Matrix (Fin 10) (Fin 10) (ZMod 7))ˣ :=
  have hw : wf7 X = true := (CFSG.Certificates.KB.andB_true h).1
  have hm : dec7 X * dec7 X = 1 := by
    rw [← (mul7_sound hw hw).2, Nat.eq_of_beq_eq_true (CFSG.Certificates.KB.andB_true h).2, dec7_one]
  ⟨dec7 X, dec7 X, hm, hm⟩

end CertificateChecks.KernelCo2

end
