module

public import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Group
public import Mathlib.Algebra.Group.Subgroup.Lattice

public section

namespace CFSG.Sporadic.Recognition.LyonsSims

open Subgroup

section Transversal

variable {A A' : Type*} [Group A] [Group A']

theorem transversal_cover [Finite A] {P H : Subgroup A} {m n : ℕ} {g v : ℕ → A} {σ : ℕ → ℕ → ℕ}
    {hh : ℕ → ℕ → A} (hgen : P ≤ Subgroup.closure (g '' {k | k < m})) (hn : 0 < n)
    (hv0 : v 0 = 1) (hσ : ∀ i < n, ∀ k < m, σ k i < n)
    (hhH : ∀ i < n, ∀ k < m, hh k i ∈ H)
    (hsch : ∀ i < n, ∀ k < m, v i * g k = hh k i * v (σ k i)) :
    ∀ x ∈ P, ∃ h ∈ H, ∃ i < n, x = h * v i := by
  classical
  let S : Set A := {x | ∃ h ∈ H, ∃ i < n, x = h * v i}
  have hS_mul : ∀ k < m, ∀ x ∈ S, x * g k ∈ S := by
    rintro k hk _ ⟨h, hH, i, hi, rfl⟩
    refine ⟨h * hh k i, H.mul_mem hH (hhH i hi k hk), σ k i, hσ i hi k hk, ?_⟩
    calc h * v i * g k = h * (v i * g k) := by group
      _ = h * (hh k i * v (σ k i)) := by rw [hsch i hi k hk]
      _ = h * hh k i * v (σ k i) := by group
  have hS_fin : S.Finite := Set.toFinite S
  have key : ∀ y ∈ Subgroup.closure (g '' {k | k < m}), ∀ s ∈ S, s * y ∈ S := by
    intro y hy
    induction hy using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨k, hk, rfl⟩ := hx
      exact fun s hs => hS_mul k hk s hs
    | one => simp
    | mul x y hx hy ihx ihy =>
      intro s hs
      rw [← mul_assoc]
      exact ihy _ (ihx s hs)
    | inv x hx ihx =>
      intro s hs
      have hmaps : Set.MapsTo (fun z => z * x) S S := fun z hz => ihx z hz
      have hinj : Set.InjOn (fun z => z * x) S := fun a _ b _ e => mul_right_cancel e
      have hbij := (hS_fin.injOn_iff_bijOn_of_mapsTo hmaps).1 hinj
      obtain ⟨z, hz, ez⟩ := hbij.surjOn hs
      have : s * x⁻¹ = z := by
        rw [← ez]
        group
      rw [this]
      exact hz
  intro x hxP
  have := key x (hgen hxP) 1 ⟨1, H.one_mem, 0, hn, by rw [hv0, one_mul]⟩
  rwa [one_mul] at this


theorem exists_mulEquiv_of_transversal [Finite A] [Finite A']
    {P H : Subgroup A} {P' H' : Subgroup A'} (hHP : H ≤ P) (hHP' : H' ≤ P')
    (ι : ↥H ≃* ↥H') {m n : ℕ} {g v : ℕ → A} {g' v' : ℕ → A'} {σ : ℕ → ℕ → ℕ}
    {hh : ℕ → ℕ → A} {hh' : ℕ → ℕ → A'}
    (hgP : ∀ k < m, g k ∈ P) (hgP' : ∀ k < m, g' k ∈ P')
    (hgen : P ≤ Subgroup.closure (g '' {k | k < m}))
    (hgen' : P' ≤ Subgroup.closure (g' '' {k | k < m}))
    (hn : 0 < n) (hv0 : v 0 = 1) (hv0' : v' 0 = 1)
    (hvP : ∀ i < n, v i ∈ P) (hvP' : ∀ i < n, v' i ∈ P')
    (hσ : ∀ i < n, ∀ k < m, σ k i < n)
    (hhH : ∀ i < n, ∀ k < m, hh k i ∈ H) (hhH' : ∀ i < n, ∀ k < m, hh' k i ∈ H')
    (hιh : ∀ i < n, ∀ k < m, ∀ hmem : hh k i ∈ H, ((ι ⟨hh k i, hmem⟩ : ↥H') : A') = hh' k i)
    (hsch : ∀ i < n, ∀ k < m, v i * g k = hh k i * v (σ k i))
    (hsch' : ∀ i < n, ∀ k < m, v' i * g' k = hh' k i * v' (σ k i))
    (hdist : ∀ i < n, ∀ j < n, v i * (v j)⁻¹ ∈ H → i = j)
    (hdist' : ∀ i < n, ∀ j < n, v' i * (v' j)⁻¹ ∈ H' → i = j) :
    ∃ Φ : ↥P ≃* ↥P',
      (∀ (h : A) (hH : h ∈ H) (i : ℕ) (hi : i < n),
        ((Φ ⟨h * v i, P.mul_mem (hHP hH) (hvP i hi)⟩ : ↥P') : A') =
          ((ι ⟨h, hH⟩ : ↥H') : A') * v' i) ∧
      (∀ (k : ℕ) (hk : k < m), ((Φ ⟨g k, hgP k hk⟩ : ↥P') : A') = g' k) ∧
      Nat.card ↥P = Nat.card ↥H * n := by
  classical
  have huniq : ∀ h₁ ∈ H, ∀ i < n, ∀ h₂ ∈ H, ∀ j < n, h₁ * v i = h₂ * v j → h₁ = h₂ ∧ i = j := by
    intro h₁ h₁H i hi h₂ h₂H j hj e
    have hij : v i * (v j)⁻¹ ∈ H := by
      have e2 : v i * (v j)⁻¹ = h₁⁻¹ * h₂ := by
        calc v i * (v j)⁻¹ = h₁⁻¹ * (h₁ * v i) * (v j)⁻¹ := by group
          _ = h₁⁻¹ * (h₂ * v j) * (v j)⁻¹ := by rw [e]
          _ = h₁⁻¹ * h₂ := by group
      rw [e2]
      exact H.mul_mem (H.inv_mem h₁H) h₂H
    have hij' := hdist i hi j hj hij
    subst hij'
    exact ⟨mul_right_cancel e, rfl⟩
  have huniq' : ∀ h₁ ∈ H', ∀ i < n, ∀ h₂ ∈ H', ∀ j < n, h₁ * v' i = h₂ * v' j →
      h₁ = h₂ ∧ i = j := by
    intro h₁ h₁H i hi h₂ h₂H j hj e
    have hij : v' i * (v' j)⁻¹ ∈ H' := by
      have e2 : v' i * (v' j)⁻¹ = h₁⁻¹ * h₂ := by
        calc v' i * (v' j)⁻¹ = h₁⁻¹ * (h₁ * v' i) * (v' j)⁻¹ := by group
          _ = h₁⁻¹ * (h₂ * v' j) * (v' j)⁻¹ := by rw [e]
          _ = h₁⁻¹ * h₂ := by group
      rw [e2]
      exact H'.mul_mem (H'.inv_mem h₁H) h₂H
    have hij' := hdist' i hi j hj hij
    subst hij'
    exact ⟨mul_right_cancel e, rfl⟩
  have hcov := transversal_cover hgen hn hv0 hσ hhH hsch
  have hcov' := transversal_cover hgen' hn hv0' hσ hhH' hsch'
  let f : ↥H × Fin n → ↥P := fun p =>
    ⟨(p.1 : A) * v p.2.val, P.mul_mem (hHP p.1.2) (hvP p.2.val p.2.2)⟩
  let f' : ↥H' × Fin n → ↥P' := fun p =>
    ⟨(p.1 : A') * v' p.2.val, P'.mul_mem (hHP' p.1.2) (hvP' p.2.val p.2.2)⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨h₁, i₁⟩ ⟨h₂, i₂⟩ e
      have e' : (h₁ : A) * v i₁.val = (h₂ : A) * v i₂.val := congrArg Subtype.val e
      obtain ⟨e1, e2⟩ := huniq _ h₁.2 i₁.val i₁.2 _ h₂.2 i₂.val i₂.2 e'
      exact Prod.ext (Subtype.ext e1) (Fin.ext e2)
    · intro x
      obtain ⟨h, hH, i, hi, hx⟩ := hcov x x.2
      exact ⟨(⟨h, hH⟩, ⟨i, hi⟩), Subtype.ext hx.symm⟩
  have hf' : Function.Bijective f' := by
    constructor
    · rintro ⟨h₁, i₁⟩ ⟨h₂, i₂⟩ e
      have e' : (h₁ : A') * v' i₁.val = (h₂ : A') * v' i₂.val := congrArg Subtype.val e
      obtain ⟨e1, e2⟩ := huniq' _ h₁.2 i₁.val i₁.2 _ h₂.2 i₂.val i₂.2 e'
      exact Prod.ext (Subtype.ext e1) (Fin.ext e2)
    · intro x
      obtain ⟨h, hH, i, hi, hx⟩ := hcov' x x.2
      exact ⟨(⟨h, hH⟩, ⟨i, hi⟩), Subtype.ext hx.symm⟩
  let ef : ↥H × Fin n ≃ ↥P := Equiv.ofBijective f hf
  let ef' : ↥H' × Fin n ≃ ↥P' := Equiv.ofBijective f' hf'
  let e : ↥P ≃ ↥P' :=
    ef.symm.trans ((ι.toEquiv.prodCongr (Equiv.refl (Fin n))).trans ef')
  have he_f : ∀ p : ↥H × Fin n, e (f p) = f' (ι p.1, p.2) := by
    intro p
    have h1 : ef.symm (f p) = p := ef.symm_apply_apply p
    show ef' ((ι.toEquiv.prodCongr (Equiv.refl (Fin n))) (ef.symm (f p))) = _
    rw [h1]
    rfl
  have he1 : e 1 = 1 := by
    have h1 : (1 : ↥P) = f (1, ⟨0, hn⟩) := by
      apply Subtype.ext
      show (1 : A) = ((1 : ↥H) : A) * v 0
      rw [hv0]
      simp
    have h2 := he_f (1, ⟨0, hn⟩)
    rw [h1, h2]
    apply Subtype.ext
    show ((ι 1 : ↥H') : A') * v' 0 = 1
    rw [map_one, hv0']
    simp
  have hstep : ∀ (x : ↥P) (k : ℕ) (hk : k < m),
      e (x * ⟨g k, hgP k hk⟩) = e x * ⟨g' k, hgP' k hk⟩ := by
    intro x k hk
    obtain ⟨⟨h, i⟩, rfl⟩ := ef.surjective x
    have hi := i.2
    have hef : ef (h, i) = f (h, i) := rfl
    rw [hef]
    let h2 : ↥H := h * ⟨hh k i.val, hhH i.val hi k hk⟩
    let i2 : Fin n := ⟨σ k i.val, hσ i.val hi k hk⟩
    have hmul : f (h, i) * ⟨g k, hgP k hk⟩ = f (h2, i2) := by
      apply Subtype.ext
      show (h : A) * v i.val * g k = ((h2 : ↥H) : A) * v (σ k i.val)
      calc (h : A) * v i.val * g k = (h : A) * (v i.val * g k) := by group
        _ = (h : A) * (hh k i.val * v (σ k i.val)) := by rw [hsch i.val hi k hk]
        _ = ((h2 : ↥H) : A) * v (σ k i.val) := by
          show _ = ((h : A) * hh k i.val) * v (σ k i.val)
          group
    rw [hmul, he_f, he_f]
    apply Subtype.ext
    show ((ι h2 : ↥H') : A') * v' (σ k i.val) = ((ι h : ↥H') : A') * v' i.val * g' k
    have hι2 : ((ι h2 : ↥H') : A') = ((ι h : ↥H') : A') * hh' k i.val := by
      show ((ι (h * ⟨hh k i.val, hhH i.val hi k hk⟩) : ↥H') : A') = _
      rw [map_mul, Subgroup.coe_mul, hιh i.val hi k hk (hhH i.val hi k hk)]
    rw [hι2, mul_assoc, ← hsch' i.val hi k hk]
    group
  have hcl : Subgroup.closure (g '' {k | k < m}) ≤ P :=
    (Subgroup.closure_le _).2 (by
      rintro _ ⟨k, hk, rfl⟩
      exact hgP k hk)
  have hmulc : ∀ y : A, y ∈ Subgroup.closure (g '' {k | k < m}) → ∀ (hy : y ∈ P) (x : ↥P),
      e (x * ⟨y, hy⟩) = e x * e ⟨y, hy⟩ := by
    intro y hyc
    induction hyc using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨k, hk, rfl⟩ := hy
      intro hyP x
      have hgk : e ⟨g k, hyP⟩ = ⟨g' k, hgP' k hk⟩ := by
        have := hstep 1 k hk
        rw [one_mul, he1, one_mul] at this
        exact this
      rw [hgk]
      exact hstep x k hk
    | one =>
      intro hyP x
      have : (⟨1, hyP⟩ : ↥P) = 1 := rfl
      rw [this, mul_one, he1, mul_one]
    | mul y₁ y₂ hy₁c hy₂c ih₁ ih₂ =>
      intro hyP x
      have hy₁P : y₁ ∈ P := hcl hy₁c
      have hy₂P : y₂ ∈ P := hcl hy₂c
      have e1 : (⟨y₁ * y₂, hyP⟩ : ↥P) = ⟨y₁, hy₁P⟩ * ⟨y₂, hy₂P⟩ := rfl
      rw [e1, ← mul_assoc, ih₂ hy₂P (x * ⟨y₁, hy₁P⟩), ih₁ hy₁P x, mul_assoc,
        ← ih₂ hy₂P ⟨y₁, hy₁P⟩]
    | inv y₁ hy₁c ih =>
      intro hyP x
      have hy₁P : y₁ ∈ P := hcl hy₁c
      have e1 : (⟨y₁⁻¹, hyP⟩ : ↥P) = (⟨y₁, hy₁P⟩ : ↥P)⁻¹ := rfl
      have h1 : e (x * (⟨y₁, hy₁P⟩ : ↥P)⁻¹) * e ⟨y₁, hy₁P⟩ = e x := by
        rw [← ih hy₁P (x * (⟨y₁, hy₁P⟩ : ↥P)⁻¹)]
        simp
      have h2 : e ((⟨y₁, hy₁P⟩ : ↥P)⁻¹) * e ⟨y₁, hy₁P⟩ = 1 := by
        have := ih hy₁P ((⟨y₁, hy₁P⟩ : ↥P)⁻¹)
        rw [inv_mul_cancel, he1] at this
        exact this.symm
      rw [e1]
      have h3 : e (x * (⟨y₁, hy₁P⟩ : ↥P)⁻¹) = e x * (e ⟨y₁, hy₁P⟩)⁻¹ :=
        eq_mul_inv_of_mul_eq h1
      have h4 : e ((⟨y₁, hy₁P⟩ : ↥P)⁻¹) = (e ⟨y₁, hy₁P⟩)⁻¹ := eq_inv_of_mul_eq_one_left h2
      rw [h3, h4]
  let Φ : ↥P ≃* ↥P' :=
    { e with
      map_mul' := fun x y => hmulc y.1 (hgen y.2) y.2 x }
  refine ⟨Φ, fun h hH i hi => ?_, fun k hk => ?_, ?_⟩
  · have := he_f (⟨h, hH⟩, ⟨i, hi⟩)
    show ((e (f (⟨h, hH⟩, ⟨i, hi⟩)) : ↥P') : A') = _
    rw [this]
  · have := hstep 1 k hk
    rw [one_mul, he1, one_mul] at this
    exact congrArg Subtype.val this
  · rw [← Nat.card_congr ef, Nat.card_prod, Nat.card_eq_fintype_card (α := Fin n),
      Fintype.card_fin]

end Transversal

end CFSG.Sporadic.Recognition.LyonsSims
