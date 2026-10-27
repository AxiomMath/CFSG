module

public import CFSG.Timmesfeld.ARS.ExclNSClassical

public section

namespace CFSG.Timmesfeld.ARS.ExclNS

open CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.LieType.Steinberg

variable {n : ℕ} {A : Matrix (Fin n) (Fin n) ℤ} (hA : TauCeti.IsFiniteType A) (P : EpsCoords A)
  {m : ℕ}

@[expose] def Reach (vs es : Fin m → Fin n → ℤ) : Prop :=
  ∃ w : (coxeterMatrix hA).Group, ∀ i, P.E (weylAction hA w (vs i)) = es i

variable {hA P}

namespace Reach

variable {vs : Fin m → Fin n → ℤ}

theorem refl (vs : Fin m → Fin n → ℤ) : Reach hA P vs fun i => P.E (vs i) :=
  ⟨1, fun i => by simp⟩

theorem step {es : Fin m → Fin n → ℤ} (h : Reach hA P vs es) (k : Fin n) :
    Reach hA P vs fun i => Spin.stdReflB n k (es i) := by
  obtain ⟨w, hw⟩ := h
  refine ⟨(coxeterMatrix hA).toCoxeterSystem.simple k * w, fun i => ?_⟩
  rw [weylAction_mul_apply, weylAction_simple, P.refl, hw i]

variable {x y : Fin m → ℤ} {a b : ℕ}

theorem swap (h : Reach hA P vs fun i => x i • ev n a + y i • ev n b) {k : ℕ} (hk : k + 1 < n) :
    Reach hA P vs fun i => x i • ev n (swapN k a) + y i • ev n (swapN k b) := by
  have h1 := h.step ⟨k, by omega⟩
  simp only [stdReflB_add, stdReflB_smul, stdReflB_ev_of_lt (k := ⟨k, by omega⟩) hk] at h1
  exact h1

theorem negLast (h : Reach hA P vs fun i => x i • ev n a + y i • ev n b) (hb : b + 1 = n)
    (hab : a ≠ b) : Reach hA P vs fun i => x i • ev n a + (-y i) • ev n b := by
  have h1 := h.step ⟨b, by omega⟩
  have hnot : ¬ (⟨b, by omega⟩ : Fin n).val + 1 < n := by simp; omega
  simp only [stdReflB_add, stdReflB_smul, stdReflB_ev_of_not_lt hnot, hab, ite_true, ite_false,
    smul_neg, ← neg_smul] at h1
  exact h1

theorem comm (h : Reach hA P vs fun i => x i • ev n a + y i • ev n b) :
    Reach hA P vs fun i => y i • ev n b + x i • ev n a := by
  obtain ⟨w, hw⟩ := h
  refine ⟨w, fun i => ?_⟩
  simp only at hw ⊢
  rw [hw i, add_comm]

theorem moveDown_fst {a' : ℕ} (d : ℕ)
    (h : Reach hA P vs fun i => x i • ev n (a' + d) + y i • ev n b) (hab : a' + d < b)
    (hb : b < n) : Reach hA P vs fun i => x i • ev n a' + y i • ev n b := by
  induction d with
  | zero => simpa using h
  | succ d ih =>
    refine ih ?_ (by omega)
    have h1 := h.swap (k := a' + d) (by omega)
    have e1 : swapN (a' + d) (a' + (d + 1)) = a' + d := by
      simp only [swapN]
      split_ifs <;> omega
    have e2 : swapN (a' + d) b = b := by
      simp only [swapN]
      split_ifs <;> omega
    rwa [e1, e2] at h1

theorem moveDown_snd {b' : ℕ} (d : ℕ)
    (h : Reach hA P vs fun i => x i • ev n a + y i • ev n (b' + d)) (hab : a < b')
    (hb : b' + d < n) : Reach hA P vs fun i => x i • ev n a + y i • ev n b' := by
  induction d with
  | zero => simpa using h
  | succ d ih =>
    refine ih ?_ (by omega)
    have h1 := h.swap (k := b' + d) (by omega)
    have e1 : swapN (b' + d) a = a := by
      simp only [swapN]
      split_ifs <;> omega
    have e2 : swapN (b' + d) (b' + (d + 1)) = b' + d := by
      simp only [swapN]
      split_ifs <;> omega
    rwa [e1, e2] at h1

theorem moveUp_snd (d : ℕ) (h : Reach hA P vs fun i => x i • ev n a + y i • ev n b)
    (hab : a < b) (hb : b + d < n) :
    Reach hA P vs fun i => x i • ev n a + y i • ev n (b + d) := by
  induction d with
  | zero => simpa using h
  | succ d ih =>
    have h1 := (ih (by omega)).swap (k := b + d) (by omega)
    have e1 : swapN (b + d) a = a := by
      simp only [swapN]
      split_ifs <;> omega
    have e2 : swapN (b + d) (b + d) = b + (d + 1) := by
      simp only [swapN]
      split_ifs <;> omega
    rwa [e1, e2] at h1

theorem neg_snd (h : Reach hA P vs fun i => x i • ev n a + y i • ev n b) (hab : a < b)
    (hb : b < n) : Reach hA P vs fun i => x i • ev n a + (-y i) • ev n b := by
  have h1 := h.moveUp_snd (n - 1 - b) hab (by omega)
  have e : b + (n - 1 - b) = n - 1 := by omega
  rw [e] at h1
  have h2 := h1.negLast (by omega) (by omega)
  have e' : n - 1 = b + (n - 1 - b) := by omega
  rw [e'] at h2
  exact h2.moveDown_snd (n - 1 - b) hab (by omega)

theorem swap_fst_snd (h : Reach hA P vs fun i => x i • ev n a + y i • ev n (a + 1))
    (ha : a + 1 < n) : Reach hA P vs fun i => y i • ev n a + x i • ev n (a + 1) := by
  have h1 := h.swap (k := a) ha
  have e1 : swapN a a = a + 1 := by
    simp only [swapN]
    split_ifs <;> omega
  have e2 : swapN a (a + 1) = a := by
    simp only [swapN]
    split_ifs <;> omega
  rw [e1, e2] at h1
  exact h1.comm

end Reach

end CFSG.Timmesfeld.ARS.ExclNS
