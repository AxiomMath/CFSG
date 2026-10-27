module

public import CFSG.Quasithin.Background.ConjTransportRk
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.Quasithin.H11

variable {V : Type*} [CommGroup V] [Finite V]

@[expose] def conjSub (φ : MulAut V) (A : Subgroup (MulAut V)) : Subgroup (MulAut V) :=
  A.map (MulAut.conj φ).toMonoidHom

omit [Finite V] in
theorem mem_conjSub {φ x : MulAut V} {A : Subgroup (MulAut V)} :
    x ∈ conjSub φ A ↔ φ⁻¹ * x * φ ∈ A := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hy
  · intro hx
    exact ⟨φ⁻¹ * x * φ, hx, by simp [MulAut.conj_apply, mul_assoc]⟩

omit [Finite V] in
theorem mem_conjSub_iff {φ x : MulAut V} {A : Subgroup (MulAut V)} :
    φ * x * φ⁻¹ ∈ conjSub φ A ↔ x ∈ A := by
  rw [mem_conjSub]; simp [mul_assoc]

omit [Finite V] in
theorem conjSub_le {φ : MulAut V} {A L : Subgroup (MulAut V)} (hφ : φ ∈ L) (h : A ≤ L) :
    conjSub φ A ≤ L := by
  intro x hx
  rw [mem_conjSub] at hx
  have := L.mul_mem (L.mul_mem hφ (h hx)) (L.inv_mem hφ)
  simpa [mul_assoc] using this

theorem rkIdx_fixV_conjSub (φ : MulAut V) (A : Subgroup (MulAut V)) :
    rkIdx (fixV (conjSub φ A)) = rkIdx (fixV A) :=
  CFSG.Quasithin.ConjTransport.rkIdx_fixV_map_conj A φ

omit [Finite V] in
theorem rk_conjSub (φ : MulAut V) (A : Subgroup (MulAut V)) : rk (conjSub φ A) = rk A := by
  unfold rk
  rw [conjSub, Subgroup.card_map_of_injective (MulAut.conj φ).injective]

omit [Finite V] in
theorem conjSub_ne_bot {φ : MulAut V} {A : Subgroup (MulAut V)} (h : A ≠ ⊥) :
    conjSub φ A ≠ ⊥ := by
  intro h0
  apply h
  rw [Subgroup.eq_bot_iff_forall] at h0 ⊢
  intro x hx
  have := h0 (φ * x * φ⁻¹) (mem_conjSub_iff.mpr hx)
  simpa using this

omit [Finite V] in
theorem isElemAbelian2_conjSub {φ : MulAut V} {A : Subgroup (MulAut V)} (h : IsElemAbelian2 A) :
    IsElemAbelian2 (conjSub φ A) := by
  refine ⟨fun x hx y hy => ?_, fun x hx => ?_⟩
  · rw [mem_conjSub] at hx hy
    have := h.1 _ hx _ hy
    have h' := congrArg (fun z => φ * z * φ⁻¹) this
    simpa [mul_assoc] using h'
  · rw [mem_conjSub] at hx
    have := h.2 _ hx
    have h' := congrArg (fun z => φ * z * φ⁻¹) this
    simpa [pow_two, mul_assoc] using h'

omit [Finite V] in
theorem conjSub_zpowers (φ : MulAut V) (t : MulAut V) :
    conjSub φ (Subgroup.zpowers t) = Subgroup.zpowers (φ * t * φ⁻¹) := by
  rw [conjSub, MonoidHom.map_zpowers]
  rfl

@[expose] def H11Concl (a : ℕ) (L A : Subgroup (MulAut V)) : Prop :=
  rk A + a ≤ rkIdx (fixV A) + 1 ∧
    (rk A + 2 ≤ rkIdx (fixV A) ∨
      (a = 2 ∧ ∃ t ∈ A, rkIdx (fixV (Subgroup.zpowers t)) = a)) ∧
    (A ≤ L → rk A + a ≤ rkIdx (fixV A))

theorem H11Concl_of_conjSub {a : ℕ} {L A : Subgroup (MulAut V)} {φ : MulAut V} (hφ : φ ∈ L)
    (hc : H11Concl a L (conjSub φ A)) : H11Concl a L A := by
  obtain ⟨h1, h2, h3⟩ := hc
  rw [rk_conjSub, rkIdx_fixV_conjSub] at h1 h2 h3
  refine ⟨h1, ?_, fun hA => h3 (conjSub_le hφ hA)⟩
  rcases h2 with h2 | ⟨ha, t, ht, hrk⟩
  · exact Or.inl h2
  · refine Or.inr ⟨ha, φ⁻¹ * t * φ, mem_conjSub.mp ht, ?_⟩
    rw [← hrk, ← rkIdx_fixV_conjSub φ (Subgroup.zpowers (φ⁻¹ * t * φ)), conjSub_zpowers]
    simp [mul_assoc]

end CFSG.Quasithin.H11
