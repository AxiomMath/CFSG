module

public import Certificates.Data.Kernel.PermCent.CV
public import Mathlib.Tactic.Group

public section

namespace CFSG.Certificates.Kernel.PkCV

variable {n : Nat}

@[expose] noncomputable def cmEqC (u v d : CV n) : Bool :=
  CFSG.KC.Enum.allN n fun i => Nat.beq (img n u.1 (img n v.1 i)) (img n d.1 (img n v.1 (img n u.1 i)))

@[expose] noncomputable def cmAnyC (T : List (CV n)) (u v : CV n) (a b : Nat) : Bool :=
  T.any fun d => Bool.rec false (cmEqC u v d) (Nat.beq (img n d.1 a) b)

@[expose] noncomputable def commInC (T U : List (CV n)) : Bool :=
  U.all fun u => U.all fun v =>
    CFSG.KC.Enum.strictB (img n v.1 (img n u.1 0)) fun a =>
      CFSG.KC.Enum.strictB (img n u.1 (img n v.1 0)) fun b => cmAnyC T u v a b

theorem strictB_eqC(y : Nat) (k : Nat → Bool) : CFSG.KC.Enum.strictB y k = k y := by
  cases y <;> rfl

theorem cmAnyC_any (T : List (CV n)) (u v : CV n) (a b : Nat) (h : cmAnyC T u v a b = true) :
    ∃ d ∈ T, cmEqC u v d = true := by
  obtain ⟨d, hd, e⟩ := List.any_eq_true.mp h
  refine ⟨d, hd, ?_⟩
  cases hc : Nat.beq (img n d.1 a) b
  · rw [hc] at e
    exact absurd e Bool.false_ne_true
  · rw [hc] at e
    exact e

variable [Small n]

theorem cmEqC_eq (u v d : CV n) : cmEqC u v d = decide (u * v = d * (v * u)) := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff, cmEqC, CFSG.KS.PK.allN_iff]
  constructor
  · intro h
    apply ev_injective
    rw [ev_mul, ev_mul, ev_mul]
    ext i
    have := h i i.2
    rw [Nat.beq_eq] at this
    simp only [Equiv.Perm.mul_apply, ev_apply]
    exact this
  · intro h i hi
    have h' := congrArg (fun σ : CV n => (ev σ ⟨i, hi⟩ : Nat)) h
    simp only [ev_mul, Equiv.Perm.mul_apply, ev_apply] at h'
    exact Nat.beq_eq.mpr h'

theorem commInC_all (T U : List (CV n)) (P : CV n → Bool) (hT : T.all P = true)
    (h : commInC T U = true) : U.all (fun u => U.all fun v => P (u * v * u⁻¹ * v⁻¹)) = true := by
  rw [commInC, List.all_eq_true] at h
  rw [List.all_eq_true] at hT ⊢
  intro u hu
  have hu' := h u hu
  rw [List.all_eq_true] at hu' ⊢
  intro v hv
  have hv' := hu' v hv
  rw [strictB_eqC, strictB_eqC] at hv'
  obtain ⟨d, hd, e⟩ := cmAnyC_any T u v _ _ hv'
  rw [cmEqC_eq, decide_eq_true_iff] at e
  have e' : u * v * u⁻¹ * v⁻¹ = d := by
    rw [e]
    group
  rw [e']
  exact hT d hd

theorem commInC_conj (T L : List (CV n)) (g : CV n) (P : CV n → Bool) (hT : T.all P = true)
    (h : commInC T (L.map fun a => g * a * g⁻¹) = true) :
    L.all (fun a => L.all fun b => P (g * (a * b * a⁻¹ * b⁻¹) * g⁻¹)) = true := by
  have h' := commInC_all T _ P hT h
  rw [List.all_eq_true] at h' ⊢
  intro a ha
  have ha' := h' _ (List.mem_map_of_mem (f := fun a => g * a * g⁻¹) ha)
  rw [List.all_eq_true] at ha' ⊢
  intro b hb
  have hb' := ha' _ (List.mem_map_of_mem (f := fun a => g * a * g⁻¹) hb)
  have e : g * a * g⁻¹ * (g * b * g⁻¹) * (g * a * g⁻¹)⁻¹ * (g * b * g⁻¹)⁻¹ =
      g * (a * b * a⁻¹ * b⁻¹) * g⁻¹ := by
    group
  rw [e] at hb'
  exact hb'

end CFSG.Certificates.Kernel.PkCV

end
