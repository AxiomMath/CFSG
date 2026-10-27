module

public import Mathlib
public import CFSG.Sporadic.Th.TableSpec
public import Certificates.Data.CFSGNative.J4.Cert
public import CFSG.Sporadic.J4.ParSpec
import Certificates.Data.CFSGNative.J4.Store
import Certificates.Data.CFSGNative.J4.Orbit
import Certificates.Data.CFSGNative.J4.Tables
import Certificates.Data.CFSGNative.J4.Global

public section

namespace CFSG.Sporadic.J4

open Native CFSG.Sporadic.Th

variable {G : Type*} [Group G] {n : ℕ} [MulAction G (Fin n)]

@[expose] def RepT (n : ℕ) [MulAction G (Fin n)] (t : ByteArray) (g : G) : Prop :=
  ∀ i < n, rdU32 t i = idx n g i

@[expose] def TupRep (n : ℕ) [MulAction G (Fin n)] (q0 q : Array ℕ) (g : G) : Prop :=
  q.size = q0.size ∧ ∀ j < q0.size, q[j]! = idx n g q0[j]!

theorem TupRep.one {q0 : Array ℕ} : TupRep n q0 q0 (1 : G) :=
  ⟨rfl, fun j _ => by rw [idx_one]⟩

theorem TupRep.lt {q0 q : Array ℕ} {g : G} (h : TupRep n q0 q g) (hq0 : ∀ j < q0.size, q0[j]! < n) :
    ∀ j < q.size, q[j]! < n := by
  intro j hj
  rw [h.1] at hj
  rw [h.2 j hj]
  exact idx_lt g (hq0 j hj)

private theorem apLoop_spec (t : ByteArray) (q : Array ℕ) (k : ℕ) :
    (apLoop t q k).size = q.size ∧
      ∀ j < q.size, (apLoop t q k)[j]! = if k ≤ j then rdU32 t q[j]! else q[j]! := by
  induction h : q.size - k generalizing q k with
  | zero =>
    rw [apLoop, dite_eq_right (by omega)]
    exact ⟨rfl, fun j hj => by rw [ite_eq_right (by omega)]⟩
  | succ d ih =>
    rw [apLoop, dite_eq_left (by omega)]
    have hk : k < q.size := by omega
    have hs : (q.set k (rdU32 t q[k]) hk).size = q.size := Array.size_set ..
    obtain ⟨h1, h2⟩ := ih (q.set k (rdU32 t q[k]) hk) (k + 1) (by omega)
    refine ⟨h1.trans hs, fun j hj => ?_⟩
    rw [h2 j (by omega)]
    have e : (q.set k (rdU32 t q[k]) hk)[j]! = if k = j then rdU32 t q[k] else q[j]! := by
      rw [getElem!_pos _ j (by omega), Array.getElem_set, getElem!_pos q j hj]
    rw [e]
    by_cases hkj : k = j
    · subst hkj
      rw [ite_eq_right (by omega), ite_eq_left rfl, ite_eq_left le_rfl, getElem!_pos q k hk]
    · rw [ite_eq_right hkj]
      by_cases hlt : k < j
      · rw [ite_eq_left (by omega), ite_eq_left (by omega)]
      · rw [ite_eq_right (by omega), ite_eq_right (by omega)]

theorem apTab_size (t : ByteArray) (q : Array ℕ) : (apTab t q).size = q.size :=
  (apLoop_spec t q 0).1

theorem apTab_get (t : ByteArray) (q : Array ℕ) {j : ℕ} (hj : j < q.size) :
    (apTab t q)[j]! = rdU32 t q[j]! := by
  rw [apTab, (apLoop_spec t q 0).2 j hj, ite_eq_left (Nat.zero_le _)]

theorem TupRep.apTab {q0 q : Array ℕ} {g h : G} {t : ByteArray} (hq : TupRep n q0 q g)
    (hq0 : ∀ j < q0.size, q0[j]! < n) (ht : RepT n t h) : TupRep n q0 (apTab t q) (h * g) := by
  refine ⟨by rw [apTab_size, hq.1], fun j hj => ?_⟩
  rw [apTab_get _ _ (by rw [hq.1]; exact hj), hq.2 j hj, ht _ (idx_lt g (hq0 j hj)), idx_mul]

@[expose] def letterG (L1 L2 L3 : G) (l : ℕ) : G := if l = 1 then L1 else if l = 2 then L2 else L3

theorem RepT.letter3 {t1 t2 t3 : ByteArray} {L1 L2 L3 : G} (h1 : RepT n t1 L1) (h2 : RepT n t2 L2)
    (h3 : RepT n t3 L3) (l : ℕ) : RepT n (letter3 t1 t2 t3 l) (letterG L1 L2 L3 l) := by
  unfold Native.letter3 letterG
  split_ifs
  · exact h1
  · exact h2
  · exact h3

@[expose] def treeElt (par : ByteArray) (L1 L2 L3 : G) : ℕ → ℕ → G
  | 0, _ => 1
  | f + 1, j => if j = 0 then 1 else
      letterG L1 L2 L3 (rdU32 par j >>> 30) * treeElt par L1 L2 L3 f (rdU32 par j &&& 0x3FFFFFFF)

theorem fwd_spec {par t1 t2 t3 : ByteArray} {L1 L2 L3 : G} (h1 : RepT n t1 L1) (h2 : RepT n t2 L2)
    (h3 : RepT n t3 L3) {q0 : Array ℕ} (hq0 : ∀ j < q0.size, q0[j]! < n) (f j : ℕ) {q : Array ℕ}
    {g : G} (hq : TupRep n q0 q g) :
    TupRep n q0 (fwd par t1 t2 t3 f j q) (treeElt par L1 L2 L3 f j * g) := by
  induction f generalizing j with
  | zero => simpa [fwd, treeElt] using hq
  | succ f ih =>
    rw [fwd, treeElt]
    by_cases hj : j = 0
    · simp only [hj, beq_self_eq_true, ite_true, one_mul]; exact hq
    · simp only [beq_iff_eq, hj, ite_false]
      rw [mul_assoc]
      exact (ih _).apTab hq0 (RepT.letter3 h1 h2 h3 _)

theorem bwd_spec {par t1 t2 t3 : ByteArray} {L1 L2 L3 : G} (h1 : RepT n t1 L1⁻¹)
    (h2 : RepT n t2 L2⁻¹) (h3 : RepT n t3 L3⁻¹) {q0 : Array ℕ} (hq0 : ∀ j < q0.size, q0[j]! < n)
    (f j : ℕ) {q : Array ℕ} {g : G} (hq : TupRep n q0 q g) :
    TupRep n q0 (bwd par t1 t2 t3 f j q) ((treeElt par L1 L2 L3 f j)⁻¹ * g) := by
  induction f generalizing j q g with
  | zero => simpa [bwd, treeElt] using hq
  | succ f ih =>
    rw [bwd, treeElt]
    by_cases hj : j = 0
    · simp only [hj, beq_self_eq_true, ite_true, inv_one, one_mul]; exact hq
    · simp only [beq_iff_eq, hj, ite_false]
      have hl : RepT n (letter3 t1 t2 t3 (rdU32 par j >>> 30))
          (letterG L1 L2 L3 (rdU32 par j >>> 30))⁻¹ := by
        have := RepT.letter3 h1 h2 h3 (rdU32 par j >>> 30)
        convert this using 2
        unfold letterG; split_ifs <;> rfl
      have := ih (rdU32 par j &&& 0x3FFFFFFF) (hq.apTab hq0 hl)
      rwa [mul_inv_rev, mul_assoc]

@[expose] def climbElt (L : Level) (Y : ℕ → G) : ℕ → ℕ → G
  | 0, _ => 1
  | f + 1, k => if k = 0 then 1 else climbElt L Y f (L.par[k]?.getD 0) * Y (min (L.lab[k]?.getD 0) 2)

theorem climb_spec {L : Level} {Y : ℕ → G} (hY : ∀ s ≤ 2, RepT n (L.tabs[s]?.getD .empty) (Y s))
    {q0 : Array ℕ} (hq0 : ∀ j < q0.size, q0[j]! < n) (f k : ℕ) {q : Array ℕ} {g : G}
    (hq : TupRep n q0 q g) : TupRep n q0 (climb L f k q) (climbElt L Y f k * g) := by
  induction f generalizing k q g with
  | zero => simpa [climb, climbElt] using hq
  | succ f ih =>
    rw [climb, climbElt]
    by_cases hk : k = 0
    · simp only [hk, beq_self_eq_true, ite_true, one_mul]; exact hq
    · simp only [beq_iff_eq, hk, ite_false]
      rw [mul_assoc]
      exact ih _ (hq.apTab hq0 (hY _ (Nat.min_le_right _ _)))

theorem RepT.comp {c p q : ByteArray} {gp gq : G} (hp : RepT n p gp) (hq : RepT n q gq)
    {chunks : ℕ} (h : compOK n c p q chunks = true) : RepT n c (gp * gq) := by
  intro i hi
  have := parAllS_eq_true h i hi
  rw [beq_iff_eq] at this
  rw [this, hq i hi, hp _ (idx_lt gq hi), idx_mul]

theorem RepT.inv_of_self {t : ByteArray} {g : G} (h : RepT n t g) (hg : g * g = 1) :
    RepT n t g⁻¹ := by
  rwa [inv_eq_of_mul_eq_one_right hg]

end CFSG.Sporadic.J4
