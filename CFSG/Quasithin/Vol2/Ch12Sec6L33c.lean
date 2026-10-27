module

public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Group
public import Mathlib.Data.Finset.Attr

public section

namespace CFSG.Quasithin.H13.L1233

open scoped commutatorElement

variable {W : Type*} [Group W]

@[expose] def cmSet (X : Subgroup (MulAut W)) (S : Subgroup W) : Subgroup W :=
  Subgroup.closure {w | ∃ f ∈ X, ∃ s ∈ S, f s * s⁻¹ = w}

theorem cmSet_le {X : Subgroup (MulAut W)} {S R : Subgroup W}
    (h : ∀ f ∈ X, ∀ s ∈ S, f s * s⁻¹ ∈ R) : cmSet X S ≤ R :=
  (Subgroup.closure_le R).2 (by
    rintro _ ⟨f, hf, s, hs, rfl⟩
    exact h f hf s hs)

theorem mem_cmSet {X : Subgroup (MulAut W)} {S : Subgroup W} {f : MulAut W} (hf : f ∈ X)
    {s : W} (hs : s ∈ S) : f s * s⁻¹ ∈ cmSet X S :=
  Subgroup.subset_closure ⟨f, hf, s, hs, rfl⟩

theorem cmSet_mono {X : Subgroup (MulAut W)} {S S' : Subgroup W} (h : S ≤ S') :
    cmSet X S ≤ cmSet X S' :=
  cmSet_le fun _ hf _ hs => mem_cmSet hf (h hs)

theorem cmSet_invariant {X : Subgroup (MulAut W)} {S : Subgroup W} {g : MulAut W}
    (hgX : ∀ f ∈ X, g * f * g⁻¹ ∈ X) (hgS : ∀ s ∈ S, g s ∈ S) :
    ∀ c ∈ cmSet X S, g c ∈ cmSet X S := by
  have hle : cmSet X S ≤ (cmSet X S).comap g.toMonoidHom := by
    refine cmSet_le fun f hf s hs => ?_
    show g (f s * s⁻¹) ∈ cmSet X S
    have e : g (f s * s⁻¹) = (g * f * g⁻¹) (g s) * (g s)⁻¹ := by
      simp only [map_mul, map_inv, MulAut.mul_apply, MulAut.inv_apply_self]
    rw [e]
    exact mem_cmSet (hgX f hf) (hgS s hs)
  exact fun c hc => hle hc

theorem cmSet_invariant_self {X : Subgroup (MulAut W)} {S : Subgroup W}
    (hS : ∀ f ∈ X, ∀ s ∈ S, f s ∈ S) : ∀ g ∈ X, ∀ c ∈ cmSet X S, g c ∈ cmSet X S :=
  fun g hg => cmSet_invariant (fun _ hf => X.mul_mem (X.mul_mem hg hf) (X.inv_mem hg)) (hS g hg)

theorem cmSet_invariant_comm {X Y : Subgroup (MulAut W)} {S : Subgroup W}
    (hXY : ∀ f ∈ X, ∀ g ∈ Y, f * g = g * f) (hS : ∀ g ∈ Y, ∀ s ∈ S, g s ∈ S) :
    ∀ g ∈ Y, ∀ c ∈ cmSet X S, g c ∈ cmSet X S :=
  fun g hg => cmSet_invariant (fun f hf => by rw [← hXY f hf g hg, mul_inv_cancel_right]; exact hf)
    (hS g hg)

@[expose] def cmPre (hW : ∀ a b : W, a * b = b * a) (g : MulAut W) (R : Subgroup W) :
    Subgroup W where
  carrier := {c | g c * c⁻¹ ∈ R}
  mul_mem' := by
    intro a b ha hb
    show g (a * b) * (a * b)⁻¹ ∈ R
    have e : g (a * b) * (a * b)⁻¹ = (g a * a⁻¹) * (g b * b⁻¹) := by
      let _ : CommGroup W := { ‹Group W› with mul_comm := hW }
      rw [map_mul]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel
    rw [e]
    exact R.mul_mem ha hb
  one_mem' := by
    show g 1 * 1⁻¹ ∈ R
    simp
  inv_mem' := by
    intro a ha
    show g a⁻¹ * a⁻¹⁻¹ ∈ R
    have e : g a⁻¹ * a⁻¹⁻¹ = (g a * a⁻¹)⁻¹ := by
      let _ : CommGroup W := { ‹Group W› with mul_comm := hW }
      rw [map_inv]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel
    rw [e]
    exact R.inv_mem ha

theorem cmSet_comm_le (hW : ∀ a b : W, a * b = b * a) {X Y : Subgroup (MulAut W)}
    {S : Subgroup W} (hXY : ∀ f ∈ X, ∀ g ∈ Y, f * g = g * f) :
    cmSet Y (cmSet X S) ≤ cmSet X (cmSet Y S) := by
  refine cmSet_le fun g hg c hc => ?_
  have hle : cmSet X S ≤ cmPre hW g (cmSet X (cmSet Y S)) := by
    refine cmSet_le fun f hf s hs => ?_
    show g (f s * s⁻¹) * (f s * s⁻¹)⁻¹ ∈ cmSet X (cmSet Y S)
    have e : g (f s * s⁻¹) * (f s * s⁻¹)⁻¹ = f (g s * s⁻¹) * (g s * s⁻¹)⁻¹ := by
      have hfg : g (f s) = f (g s) := by
        rw [← MulAut.mul_apply _ g f, ← hXY f hf g hg, MulAut.mul_apply]
      let _ : CommGroup W := { ‹Group W› with mul_comm := hW }
      simp only [map_mul, map_inv, hfg]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel
    rw [e]
    exact mem_cmSet hf (mem_cmSet hg hs)
  exact hle hc

theorem cmSet_le_cmSet_cmSet (hW : ∀ a b : W, a * b = b * a) {X : Subgroup (MulAut W)}
    {S : Subgroup W} (hX : ⁅X, X⁆ = X) (hS : ∀ f ∈ X, ∀ s ∈ S, f s ∈ S) :
    cmSet X S ≤ cmSet X (cmSet X S) := by
  set B := cmSet X S with hB
  set A := cmSet X B with hA
  have hBi : ∀ f ∈ X, ∀ b ∈ B, f b ∈ B := cmSet_invariant_self hS
  have hAi : ∀ f ∈ X, ∀ a ∈ A, f a ∈ A := cmSet_invariant_self hBi
  have key : ∀ f ∈ ⁅X, X⁆, f ∈ X ∧ ∀ s ∈ S, f s * s⁻¹ ∈ A := by
    intro f hf
    rw [Subgroup.commutator_def] at hf
    induction hf using Subgroup.closure_induction with
    | mem g hg =>
      obtain ⟨a, ha, b, hb, rfl⟩ := hg
      refine ⟨hX ▸ Subgroup.commutator_mem_commutator ha hb, fun s hs => ?_⟩
      set s₃ := b⁻¹ s
      set s₂ := a⁻¹ s₃
      set s₁ := b s₂
      have hs₃ : s₃ ∈ S := hS _ (X.inv_mem hb) s hs
      have hs₂ : s₂ ∈ S := hS _ (X.inv_mem ha) s₃ hs₃
      have e1 : ⁅a, b⁆ s = a s₁ := by
        simp only [commutatorElement_def, MulAut.mul_apply, s₁, s₂, s₃]
      have e2 : a s₂ = s₃ := by simp [s₂]
      have e3 : b s₃ = s := by simp [s₃]
      have hx : s₁ * s₂⁻¹ ∈ B := mem_cmSet hb hs₂
      have hy : s₂ * s₃⁻¹ ∈ B := by
        have := B.inv_mem (mem_cmSet ha hs₂ (X := X))
        rwa [e2, mul_inv_rev, inv_inv] at this
      have h1 := mem_cmSet ha hx (X := X) (S := B)
      have h2 := mem_cmSet hb hy (X := X) (S := B)
      have f : ⁅a, b⁆ s * s⁻¹ = (a (s₁ * s₂⁻¹) * (s₁ * s₂⁻¹)⁻¹) *
          (b (s₂ * s₃⁻¹) * (s₂ * s₃⁻¹)⁻¹) := by
        rw [e1]
        simp only [map_mul, map_inv, e2, e3, show b s₂ = s₁ from rfl]
        let _ : CommGroup W := { ‹Group W› with mul_comm := hW }
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_inv]
        abel
      rw [f]
      exact A.mul_mem h1 h2
    | one => exact ⟨X.one_mem, fun s _ => by simp⟩
    | mul f g _ _ hf hg =>
      refine ⟨X.mul_mem hf.1 hg.1, fun s hs => ?_⟩
      have e : (f * g) s * s⁻¹ = f (g s * s⁻¹) * (f s * s⁻¹) := by
        simp only [MulAut.mul_apply, map_mul, map_inv]
        group
      rw [e]
      exact A.mul_mem (hAi f hf.1 _ (hg.2 s hs)) (hf.2 s hs)
    | inv f _ hf =>
      refine ⟨X.inv_mem hf.1, fun s hs => ?_⟩
      have hs' : f⁻¹ s ∈ S := hS _ (X.inv_mem hf.1) s hs
      have h1 := hf.2 _ hs'
      rw [MulAut.apply_inv_self] at h1
      have e : f⁻¹ s * s⁻¹ = (s * (f⁻¹ s)⁻¹)⁻¹ := by group
      rw [e]
      exact A.inv_mem h1
  exact cmSet_le fun f hf s hs => (key f (by rw [hX]; exact hf)).2 s hs

theorem cmSet_eq_bot (hW : ∀ a b : W, a * b = b * a) {X₁ X₂ : Subgroup (MulAut W)}
    (h₁ : ⁅X₁, X₁⁆ = X₁) (h₂ : ⁅X₂, X₂⁆ = X₂) (hc : ∀ f ∈ X₁, ∀ g ∈ X₂, f * g = g * f)
    {I : Subgroup W} (ha1 : cmSet X₂ (cmSet X₁ ⊤) ≤ I) (ha2 : cmSet X₂ (cmSet X₁ I) = ⊥) :
    cmSet X₂ (cmSet X₁ ⊤) = ⊥ := by
  set U₁ := cmSet X₁ (⊤ : Subgroup W)
  have hU₂ : ∀ g ∈ X₂, ∀ u ∈ U₁, g u ∈ U₁ :=
    cmSet_invariant_comm hc fun _ _ _ _ => Subgroup.mem_top _
  have hle : cmSet X₂ U₁ ≤ cmSet X₁ I := by
    calc cmSet X₂ U₁ ≤ cmSet X₂ (cmSet X₁ U₁) :=
          cmSet_mono (cmSet_le_cmSet_cmSet hW h₁ fun _ _ _ _ => Subgroup.mem_top _)
      _ ≤ cmSet X₁ (cmSet X₂ U₁) := cmSet_comm_le hW hc
      _ ≤ cmSet X₁ I := cmSet_mono ha1
  have h1 : cmSet X₂ (cmSet X₂ U₁) = ⊥ :=
    le_bot_iff.1 ((cmSet_mono hle).trans ha2.le)
  exact le_bot_iff.1 ((cmSet_le_cmSet_cmSet hW h₂ hU₂).trans h1.le)

end CFSG.Quasithin.H13.L1233
