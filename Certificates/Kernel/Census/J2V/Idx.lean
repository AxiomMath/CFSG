module

public import Certificates.Kernel.Census.J2V.Data
public import Certificates.Data.Kernel.J2V
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option maxHeartbeats 0

namespace CertificateChecks.KernelJ2V

open CFSG.KC.J2V CFSG.ComponentClassification.HarrisLit.EndB

theorem comm_ok : commCheck (tabT vTt) (tabI vIt) vCommL = true := by quickRfl

@[expose] def cmOK (T : ℕ → ℕ → ℕ) (I : ℕ → ℕ) (o z : ℕ) (b : Bool) (x y : ℕ) : Bool :=
  ci T I x y == if b then z else o

@[expose] def sqOK (T : ℕ → ℕ → ℕ) (o z : ℕ) (b : Bool) (x : ℕ) : Bool :=
  T x x == if b then z else o

@[expose] def sigPats : List ((Fin 4 → Bool) × Bool) :=
  (List.product [false, true] (List.product [false, true] (List.product [false, true]
    (List.product [false, true] [false, true])))).map fun p =>
      (![p.1, p.2.1, p.2.2.1, p.2.2.2.1], p.2.2.2.2)

theorem mem_sigPats (p : (Fin 4 → Bool) × Bool) : p ∈ sigPats := by
  obtain ⟨f, e⟩ := p
  have hf : f = ![f 0, f 1, f 2, f 3] := by
    funext k
    match k with
    | ⟨0, _⟩ | ⟨1, _⟩ | ⟨2, _⟩ | ⟨3, _⟩ => rfl
  rw [hf]
  unfold sigPats
  rw [List.mem_map]
  exact ⟨(f 0, f 1, f 2, f 3, e), by simp, rfl⟩

theorem sigPats_nodup : sigPats.Nodup := by decide

@[expose] def stepL (T : ℕ → ℕ → ℕ) (o : ℕ) (L : List ℕ) (c : ℕ) : List ℕ :=
  L.flatMap fun x => [T x o, T x c]

@[expose] def pre3 (T : ℕ → ℕ → ℕ) (o a₀ a₁ a₂ : ℕ) : List ℕ :=
  stepL T o (stepL T o [o, a₀] a₁) a₂

theorem sigPats_map (T : ℕ → ℕ → ℕ) (o z a₀ a₁ a₂ a₃ : ℕ) :
    sigPats.map (sigProdIdx T o z (a₀, a₁, a₂, a₃)) =
      stepL T o (stepL T o (pre3 T o a₀ a₁ a₂) a₃) z := rfl

@[expose] def nodupMask : ℕ → List ℕ → Bool
  | _, [] => true
  | m, x :: xs => !(m.testBit x) && nodupMask (m ||| 1 <<< x) xs

theorem nodupMask_iff (m : ℕ) (l : List ℕ) :
    nodupMask m l = true ↔ l.Nodup ∧ ∀ x ∈ l, m.testBit x = false := by
  induction l generalizing m with
  | nil => simp [nodupMask]
  | cons x xs ih =>
    simp only [nodupMask, Bool.and_eq_true, Bool.not_eq_true', ih, Nat.testBit_or,
      Nat.one_shiftLeft, Nat.testBit_two_pow, Bool.or_eq_false_iff, decide_eq_false_iff_not,
      List.nodup_cons, List.mem_cons, forall_eq_or_imp]
    constructor
    · rintro ⟨hx, hn, hxs⟩
      exact ⟨⟨fun h => (hxs x h).2 rfl, hn⟩, hx, fun y hy => (hxs y hy).1⟩
    · rintro ⟨⟨hx, hn⟩, hm, hxs⟩
      exact ⟨hm, hn, fun y hy => ⟨hxs y hy, fun h => hx (h ▸ hy)⟩⟩

theorem decide_nodup_eq (l : List ℕ) : decide l.Nodup = nodupMask 0 l := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff, nodupMask_iff]
  simp

@[expose] def sig01 (T : ℕ → ℕ → ℕ) (I : ℕ → ℕ) (o z : ℕ) (sq : Fin 4 → Bool)
    (cm : Fin 4 → Fin 4 → Bool) (a₀ a₁ : ℕ) : Bool :=
  sqOK T o z (sq 0) a₀ && sqOK T o z (sq 1) a₁ && cmOK T I o z (cm 0 0) a₀ a₀ &&
    cmOK T I o z (cm 0 1) a₀ a₁ && cmOK T I o z (cm 1 0) a₁ a₀ && cmOK T I o z (cm 1 1) a₁ a₁

@[expose] def sig2 (T : ℕ → ℕ → ℕ) (I : ℕ → ℕ) (o z : ℕ) (sq : Fin 4 → Bool)
    (cm : Fin 4 → Fin 4 → Bool) (a₀ a₁ a₂ : ℕ) : Bool :=
  sqOK T o z (sq 2) a₂ && cmOK T I o z (cm 0 2) a₀ a₂ && cmOK T I o z (cm 2 0) a₂ a₀ &&
    cmOK T I o z (cm 1 2) a₁ a₂ && cmOK T I o z (cm 2 1) a₂ a₁ && cmOK T I o z (cm 2 2) a₂ a₂

@[expose] def sig3 (T : ℕ → ℕ → ℕ) (I : ℕ → ℕ) (o z : ℕ) (sq : Fin 4 → Bool)
    (cm : Fin 4 → Fin 4 → Bool) (a₀ a₁ a₂ : ℕ) (P : List ℕ) (a₃ : ℕ) : Bool :=
  sqOK T o z (sq 3) a₃ && cmOK T I o z (cm 0 3) a₀ a₃ && cmOK T I o z (cm 3 0) a₃ a₀ &&
    cmOK T I o z (cm 1 3) a₁ a₃ && cmOK T I o z (cm 3 1) a₃ a₁ && cmOK T I o z (cm 2 3) a₂ a₃ &&
    cmOK T I o z (cm 3 2) a₃ a₂ && cmOK T I o z (cm 3 3) a₃ a₃ &&
    nodupMask 0 (stepL T o (stepL T o P a₃) z)

theorem sigIdx_eq (T : ℕ → ℕ → ℕ) (I : ℕ → ℕ) (o z : ℕ) (sq : Fin 4 → Bool)
    (cm : Fin 4 → Fin 4 → Bool) (a₀ a₁ a₂ a₃ : ℕ) :
    sigIdx T I o z sq cm (a₀, a₁, a₂, a₃) =
      (sig01 T I o z sq cm a₀ a₁ && (sig2 T I o z sq cm a₀ a₁ a₂ &&
        sig3 T I o z sq cm a₀ a₁ a₂ (pre3 T o a₀ a₁ a₂) a₃)) := by
  have hinj : Function.Injective (sigProdIdx T o z (a₀, a₁, a₂, a₃)) ↔
      (sigPats.map (sigProdIdx T o z (a₀, a₁, a₂, a₃))).Nodup := by
    rw [List.nodup_map_iff_inj_on sigPats_nodup]
    exact ⟨fun h x _ y _ hxy => h hxy, fun h x y hxy => h x (mem_sigPats x) y (mem_sigPats y) hxy⟩
  rw [Bool.eq_iff_iff]
  simp only [sigIdx, sig01, sig2, sig3, sqOK, cmOK, ← sigPats_map, ← decide_nodup_eq,
    decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq, Fin.forall_fin_succ, hinj, quadFun, IsEmpty.forall_iff, and_true,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.succ_zero_eq_one, Fin.succ_one_eq_two,
    and_assoc]
  tauto

@[expose] def sigCount (T : ℕ → ℕ → ℕ) (I : ℕ → ℕ) (o z : ℕ) (sq : Fin 4 → Bool)
    (cm : Fin 4 → Fin 4 → Bool) (L₀ L₁ L₂ L₃ : List ℕ) : ℕ :=
  (L₀.map fun a₀ => (L₁.map fun a₁ => bif sig01 T I o z sq cm a₀ a₁ then
    (L₂.map fun a₂ => bif sig2 T I o z sq cm a₀ a₁ a₂ then
      L₃.countP (sig3 T I o z sq cm a₀ a₁ a₂ (pre3 T o a₀ a₁ a₂)) else 0).sum else 0).sum).sum

theorem countP_sprod {α β : Type} (L : List α) (M : List β) (p : α × β → Bool) :
    (L ×ˢ M).countP p = (L.map fun a => M.countP fun b => p (a, b)).sum := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    have h : (a :: L) ×ˢ M = M.map (fun b => (a, b)) ++ L ×ˢ M := rfl
    rw [h, List.countP_append, List.countP_map, ih, List.map_cons, List.sum_cons]
    rfl

theorem countP_and {β : Type} (M : List β) (c : Bool) (q : β → Bool) :
    M.countP (fun b => c && q b) = bif c then M.countP q else 0 := by
  cases c <;> simp

theorem sum_map_cond {β : Type} (M : List β) (c : Bool) (f : β → ℕ) :
    (M.map fun b => bif c then f b else 0).sum = bif c then (M.map f).sum else 0 := by
  cases c <;> simp

theorem quads_countP (T : ℕ → ℕ → ℕ) (I : ℕ → ℕ) (o z : ℕ) (sq : Fin 4 → Bool)
    (cm : Fin 4 → Fin 4 → Bool) (L₀ L₁ L₂ L₃ : List ℕ) :
    (quads L₀ L₁ L₂ L₃).countP (sigIdx T I o z sq cm) = sigCount T I o z sq cm L₀ L₁ L₂ L₃ := by
  simp only [quads, sigCount, countP_sprod, sigIdx_eq, countP_and, sum_map_cond]

@[expose] def subIndexFast (T : ℕ → ℕ → ℕ) (I Cu : ℕ → ℕ) (usq : ℕ) (C : List ℕ) : Bool :=
  (List.range 128).all (fun i => T i (I i) == 0) &&
  (List.range 128).all (fun i => !((List.range 128).all fun j => T i j == T j i) ||
    i == 0 || i == 1) && (List.range 128).all (fun j => T 1 j == T j 1) &&
    C.all (fun c => C.all fun c' => C.contains (T c c')) &&
    (List.range 128).all (fun i => ivList.contains i ==
      C.all fun c => ci T I i c == 0 || ci T I i c == 1) &&
    ivList.all (· < 128) && ivList.Nodup &&
    (List.range 128).all (fun i => !(ivList.all fun l => T i l == T l i) || i == 0 || i == 1) &&
    sigCount T I 0 1 sqPat cmPat (ivSqOf T 0) (ivSqOf T 1) (ivSqOf T 2) (ivSqOf T 3) == 1920 &&
    ci T I 7 8 == 1 &&
    (List.range 128).all fun v =>
      !(T v (T (Cu v) usq) == 0 && 16 ≤ (List.range 128).countP fun d => acOf T I Cu v d == d) ||
      (List.range 128).any fun w => acOf T I Cu v w == T w 1 && (T w w == 0 || T w w == 1) &&
        (List.range 128).all fun d => !(acOf T I Cu v d == d) || ci T I w d == 0 ||
          ci T I w d == 1

theorem subIndexCheckWith_eq_fast (T : ℕ → ℕ → ℕ) (I Cu : ℕ → ℕ) (usq : ℕ) (C : List ℕ) :
    subIndexCheckWith T I Cu usq C = subIndexFast T I Cu usq C := by
  rw [subIndexCheckWith, subIndexFast, quads_countP]

theorem idx_fast : subIndexFast (tabT vTt) (tabI vIt) (tabI vCut) vUsqt vCommL = true := by
  quickRfl

theorem idx_ok : subIndexCheckWith (tabT vTt) (tabI vIt) (tabI vCut) vUsqt vCommL = true :=
  (subIndexCheckWith_eq_fast _ _ _ _ _).trans idx_fast

end CertificateChecks.KernelJ2V
