module

public import CFSG.RankThree.Native.F2Ops
public import CFSG.Certificates.Kernel.Spor.Loops

public section

namespace CFSG.RankThree.Native.F2

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.KC.Enum CFSG.KS

@[expose] def stepM (MS MSI IX : ℕ → ℕ) (c j : ℕ) : ℕ :=
  if j < c then MS (IX j) else MSI (IX (j - c))

@[expose] def stepIM (MS MSI IX : ℕ → ℕ) (c j : ℕ) : ℕ :=
  if j < c then MSI (IX j) else MS (IX (j - c))

@[expose] def lvlOf (d : ℕ) (V : Array ℕ) (m : ℕ) (PT PO PA LB TM TIM : ℕ → ℕ) : Level :=
  ⟨Array.ofFn (n := m) fun k => PT k, Array.ofFn (n := V.size) fun z => PO z,
    Array.ofFn (n := m) fun k => PA k, Array.ofFn (n := m) fun k => LB k,
    Array.ofFn (n := m) fun k => permOfMat d V (TM k),
    Array.ofFn (n := m) fun k => permOfMat d V (TIM k)⟩

@[expose] def lexLtN (a b c e : ℕ) : Bool := a < c || (a == c && b < e)

@[expose] noncomputable def edgeM (vm : ℕ → ℕ → ℕ) (VG : ℕ → ℕ) (m r : ℕ) (PT PA LB : ℕ → ℕ)
    (ED : ℕ → ℕ → ℕ) (SM : ℕ → ℕ) (h : ℕ) : Bool :=
  allN r fun j => Nat.blt (ED h j) m &&
    Nat.beq (VG (PT (ED h j))) (vm (VG (PT h)) (SM j)) &&
    (Nat.beq (ED h j) 0 || !(lexLtN h j (PA (ED h j)) (LB (ED h j))))

@[expose] noncomputable def levelHd (vm mm : ℕ → ℕ → ℕ) (I n : ℕ) (VG : ℕ → ℕ) (root m r : ℕ)
    (PT PO PA LB : ℕ → ℕ) (SM SIM TM TIM : ℕ → ℕ) : Bool :=
  Nat.blt 0 m && Nat.ble m n && Nat.beq (PT 0) root && Nat.beq (PA 0) 0 && Nat.beq (LB 0) 0 &&
    Nat.beq (TM 0) I && Nat.beq (TIM 0) I &&
    allN m (fun k => Nat.blt (PT k) n && Nat.beq (PO (PT k)) k) &&
    allN n (fun z => (Nat.blt (PO z) m && Nat.beq (PT (PO z)) z) || Nat.beq (PO z) n) &&
    allN m (fun k => Nat.beq k 0 || (Nat.blt (PA k) k && Nat.blt (LB k) r &&
      Nat.beq (VG (PT k)) (vm (VG (PT (PA k))) (SM (LB k))) &&
      Nat.beq (TM k) (mm (TM (PA k)) (SM (LB k))) &&
      Nat.beq (TIM k) (mm (SIM (LB k)) (TIM (PA k))))) &&
    allN m (fun k => Nat.beq k 0 || !(Nat.blt (k + 1) m) ||
      lexLtN (PA k) (LB k) (PA (k + 1)) (LB (k + 1)))

@[expose] noncomputable def levelM (vm mm : ℕ → ℕ → ℕ) (I n : ℕ) (VG : ℕ → ℕ) (root m r : ℕ)
    (PT PO PA LB : ℕ → ℕ) (ED : ℕ → ℕ → ℕ) (SM SIM TM TIM : ℕ → ℕ) : Bool :=
  levelHd vm mm I n VG root m r PT PO PA LB SM SIM TM TIM &&
    allN m (edgeM vm VG m r PT PA LB ED SM)

@[expose] noncomputable def stepsM (vm : ℕ → ℕ → ℕ) (VG MS : ℕ → ℕ) (kS : ℕ) (BS : ℕ → ℕ)
    (i c : ℕ) (IX : ℕ → ℕ) : Bool :=
  ((List.range kS).filter fun j => allN i fun t => Nat.beq (vm (VG (BS t)) (MS j)) (VG (BS t))) ==
    (List.range c).map IX

theorem levelM_inv {d : ℕ} (hd : 0 < d) {V : Array ℕ} (hVd : ∀ v ∈ V, v < 2 ^ d)
    {vm mm : ℕ → ℕ → ℕ} (hmm : ∀ A B, mm A B = mmul d A B) {I : ℕ} (hI : I = idM d)
    {n : ℕ} {VG : ℕ → ℕ} {root m r : ℕ} {PT PO PA LB : ℕ → ℕ} {ED : ℕ → ℕ → ℕ}
    {SM SIM TM TIM : ℕ → ℕ} (hSM : ∀ j < r, Inv d V (SM j) (SIM j))
    (h : levelM vm mm I n VG root m r PT PO PA LB ED SM SIM TM TIM = true) :
    ∀ k < m, Inv d V (TM k) (TIM k) := by
  simp only [levelM, levelHd, Bool.and_eq_true, Nat.beq_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, -⟩, -⟩, h0⟩, h0'⟩, -⟩, -⟩, hpar⟩, -⟩, -⟩ := h
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · rw [h0, h0', hI]
      exact inv_idM hd hVd
    · have hp := allN_spec hpar k hk
      simp only [Bool.or_eq_true, Nat.beq_eq, Bool.and_eq_true, Nat.blt_eq] at hp
      rcases hp with hp | ⟨⟨⟨⟨hpa, hlb⟩, -⟩, ht⟩, hti⟩
      · omega
      · rw [ht, hti, hmm, hmm]
        exact (ih _ hpa (by omega)).mul hd (hSM _ hlb)

theorem levelM_pts {vm mm : ℕ → ℕ → ℕ} {I n : ℕ} {VG : ℕ → ℕ} {root m r : ℕ}
    {PT PO PA LB : ℕ → ℕ} {ED : ℕ → ℕ → ℕ} {SM SIM TM TIM : ℕ → ℕ}
    (h : levelM vm mm I n VG root m r PT PO PA LB ED SM SIM TM TIM = true) :
    ∀ k < m, PT k < n ∧ PO (PT k) = k := by
  simp only [levelM, levelHd, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, hp⟩, -⟩, -⟩, -⟩, -⟩ := h
  intro k hk
  have := allN_spec hp k hk
  simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at this
  exact this

end CFSG.RankThree.Native.F2

end
