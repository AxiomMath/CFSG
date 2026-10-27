module

public import Certificates.Data.Kernel.PermCent.M11BTwin
public import Certificates.Data.Kernel.PermCent.SplitC

public section

namespace CFSG.Certificates.Kernel.PkCV.M11B

open CFSG.KC.Enum CFSG.KS CFSG.Certificates.Kernel.PkCV

variable {n : Nat} [Small n]

theorem fpow_mulPt (x y : CV n) (k : Nat) (i : Fin n) :
    fpow (fun j => img n x.1 (img n y.1 j)) k i = (ev ((x * y) ^ k) i : Nat) := by
  have hp : ev ((x * y) ^ k) = ev (x * y) ^ k := map_pow (evHom n) _ k
  rw [hp, ev_mul]
  clear hp
  induction k generalizing i with
  | zero => rfl
  | succ k ih =>
    rw [fpow_succ', pow_succ, Equiv.Perm.mul_apply]
    have := ih ⟨img n x.1 (img n y.1 i), x.2.2.1 _ (y.2.2.1 i i.2)⟩
    exact this

@[expose] noncomputable def pairPre (x y : CV 11) : Bool :=
  Nat.beq (fpow (fun j => img 11 x.1 (img 11 y.1 j)) 11 0) 0 &&
    Nat.beq (fpow (fun j => img 11 x.1 (img 11 y.1 j)) 11 1) 1

@[expose] noncomputable def orderQ (g : CV 11) (m : Nat) (ps : List Nat) : Bool :=
  powOneC g m && ps.all fun p => !powOneC g (m / p)

theorem orderQ_eq (g : CV 11) (m : Nat) (ps : List Nat) : orderQ g m ps = orderIsP g m ps := by
  simp only [orderQ, orderIsP, pow_fast]

theorem pairPre_of (x y : CV 11) (h : orderIsP (x * y) 11 [11] = true) : pairPre x y = true := by
  rw [orderIsP, Bool.and_eq_true, decide_eq_true_iff] at h
  have h1 : ev ((x * y) ^ 11) = 1 := by rw [h.1, ev_one]
  have e0 := fpow_mulPt x y 11 ⟨0, by norm_num⟩
  have e1 := fpow_mulPt x y 11 ⟨1, by norm_num⟩
  rw [h1] at e0 e1
  rw [pairPre, Bool.and_eq_true, Nat.beq_eq, Nat.beq_eq]
  exact ⟨e0, e1⟩

@[expose] noncomputable def pairQ (x y : CV 11) : Bool :=
  orderQ (x * y) 11 [11] && orderQ (x * y * x⁻¹ * y⁻¹) 6 [2, 3] &&
    orderQ (x * y * x * y⁻¹ * x * y * y) 5 [5]

@[expose] noncomputable def pairCntQ : Nat :=
  ((E.filter (orderIsP · 2 [2]) ×ˢ E.filter (orderIsP · 4 [2])).filter
    fun q => pairPre q.1 q.2 && pairQ q.1 q.2).length

theorem pairCntQ_eq : pairCntQ = pairCntC := by
  have h : ∀ q : CV 11 × CV 11, (pairPre q.1 q.2 && pairQ q.1 q.2) =
      (orderIsP (q.1 * q.2) 11 [11] && orderIsP (q.1 * q.2 * q.1⁻¹ * q.2⁻¹) 6 [2, 3] &&
        orderIsP (q.1 * q.2 * q.1 * q.2⁻¹ * q.1 * q.2 * q.2) 5 [5]) := by
    intro q
    simp only [pairQ, orderQ_eq]
    cases e : orderIsP (q.1 * q.2) 11 [11]
    · simp only [Bool.false_and, Bool.and_false]
    · rw [pairPre_of q.1 q.2 e, Bool.true_and]
  rw [pairCntQ, pairCntC]
  exact congrArg List.length (List.filter_congr fun q _ => h q)

end CFSG.Certificates.Kernel.PkCV.M11B

end
