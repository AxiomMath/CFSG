module

public import Certificates.Data.Kernel.PermCent.ForceCV
public import CFSG.GH74.GLS.C3.Layer2.FinModelDefs
public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.GroupTheory.Perm.Centralizer
public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.Certificates.Kernel.PkCV

open CFSG.Certificates.Kernel.PkEnum CFSG.KC.Enum

variable {n : Nat}

@[expose] def forceB {β : Sort _} (b : Bool) (k : Bool → β) : β :=
  Bool.rec (motive := fun _ => β) (k false) (k true) b

@[expose] def forcePL {β : Sort _} : List (CV n × Bool) → (List (CV n × Bool) → β) → β
  | [], k => k []
  | a :: l, k => forceC a.1 fun c => forceB a.2 fun b => forcePL l fun l => k ((c, b) :: l)

@[expose] noncomputable def ofFnC [hs : Small n] (f : Nat → Nat) (σ : Equiv.Perm (Fin n))
    (h : ∀ i (hi : i < n), f i = σ ⟨i, hi⟩) : CV n :=
  ⟨pmk n (wC n) f, canon_pmk hs.lt (fun x hx => h x hx ▸ (σ _).2) (fun a ha b hb e => by
    rw [h a ha, h b hb] at e
    exact congrArg Fin.val (σ.injective (Fin.ext e)))⟩

@[expose] noncomputable def liftF (m p e i : Nat) : Nat :=
  if i = 0 then p else if img m e (i - 1) + 1 = p then 0 else img m e (i - 1) + 1

theorem liftF_spec {m : Nat} [Small m] (p : Fin (m + 1)) (e : CV m) (i : Nat) (hi : i < m + 1) :
    liftF m p e.1 i = (Equiv.Perm.decomposeFin.symm (p, ev e) ⟨i, hi⟩ : Nat) := by
  cases i with
  | zero =>
    have h0 : (⟨0, hi⟩ : Fin (m + 1)) = 0 := rfl
    rw [h0, Equiv.Perm.decomposeFin_symm_apply_zero]
    simp [liftF]
  | succ i =>
    have hs : (⟨i + 1, hi⟩ : Fin (m + 1)) = Fin.succ ⟨i, by omega⟩ := rfl
    rw [hs, Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_apply_def]
    have hne : (ev e ⟨i, by omega⟩).succ ≠ 0 := Fin.succ_ne_zero _
    have hv : ((ev e ⟨i, by omega⟩).succ : Nat) = img m e.1 i + 1 := by
      rw [Fin.val_succ, ev_apply]
    rw [if_neg hne]
    simp only [liftF, Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel]
    by_cases hp : (ev e ⟨i, by omega⟩).succ = p
    · rw [if_pos hp, ← hv, hp, if_pos rfl]
      rfl
    · rw [if_neg hp, ← hv, if_neg (fun h => hp (Fin.ext h))]

@[expose] noncomputable def liftC {m : Nat} [Small m] [Small (m + 1)] (p : Fin (m + 1)) (e : CV m) :
    CV (m + 1) :=
  ofFnC (liftF m p e.1) (Equiv.Perm.decomposeFin.symm (p, ev e)) (liftF_spec p e)

theorem small_pred {m : Nat} (h : Small (m + 1)) : Small m := ⟨by have := h.lt; omega⟩

@[expose] noncomputable def allPermsP : (m : Nat) → Small m → List (CV m × Bool)
  | 0, _ => [(1, false)]
  | m + 1, hs =>
    have : Small m := small_pred hs
    forcePL (allPermsP m this) fun L => (List.finRange (m + 1)).flatMap fun p =>
      L.map fun x => (liftC p x.1, xor (p.1 != 0) x.2)

@[expose] noncomputable def DLP : List (CV 4 × Bool) :=
  (allPermsP 4 inferInstance).filter fun x =>
    decide (x.1 * cOf CFSG.GH74.GLS.C3.Layer2.Model.x4 = cOf CFSG.GH74.GLS.C3.Layer2.Model.x4 * x.1)

@[expose] noncomputable def F7C : List (CV 7 × CV 4) :=
  forcePL (allPermsP 7 inferInstance) fun L => forcePL DLP fun D =>
    L.flatMap fun x => (D.filter fun y => x.2 == y.2).map fun y => (x.1, y.1)

end CFSG.Certificates.Kernel.PkCV

end
