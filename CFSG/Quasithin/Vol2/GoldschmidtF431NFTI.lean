module

public import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.Tactic.Group
public import Mathlib.Algebra.Group.Subgroup.Finite

public section

namespace CFSG.Quasithin.H13.F431.NF

variable {M : Type*} [Group M]

@[expose] def cj (c : M) (H : Subgroup M) : Subgroup M := H.map (MulAut.conj c).toMonoidHom

theorem mem_cj {c x : M} {H : Subgroup M} : x ∈ cj c H ↔ c⁻¹ * x * c ∈ H := by
  unfold cj
  rw [Subgroup.mem_map_equiv]
  simp

theorem cj_mul (c d : M) (H : Subgroup M) : cj (c * d) H = cj c (cj d H) := by
  ext x
  simp only [mem_cj]
  have : d⁻¹ * (c⁻¹ * x * c) * d = (c * d)⁻¹ * x * (c * d) := by group
  rw [this]

theorem card_cj (c : M) (H : Subgroup M) : Nat.card (cj c H) = Nat.card H :=
  (Nat.card_congr (Subgroup.equivMapOfInjective H (MulAut.conj c).toMonoidHom
    (MulAut.conj c).injective).toEquiv).symm

@[expose] def IsTI (Z : Subgroup M) : Prop := ∀ c : M, Z ⊓ cj c Z ≠ ⊥ → cj c Z = Z

theorem isTI_of_cent_le {Z M₁ : Subgroup M} (hnorm : ∀ y ∈ M₁, ∀ x ∈ Z, y * x * y⁻¹ ∈ Z)
    (hcent : ∀ x ∈ Z, x ≠ 1 → Subgroup.centralizer ({x} : Set M) ≤ M₁)
    (htrans : ∀ x ∈ Z, ∀ y ∈ Z, x ≠ 1 → y ≠ 1 → ∃ m ∈ M₁, m * x * m⁻¹ = y) : IsTI Z := by
  intro c hc
  obtain ⟨⟨u, hu⟩, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hc
  have huZ : u ∈ Z := (Subgroup.mem_inf.mp hu).1
  have hucj : c⁻¹ * u * c ∈ Z := mem_cj.mp (Subgroup.mem_inf.mp hu).2
  have hu1' : u ≠ 1 := fun h => hu1 (Subtype.ext h)
  set x := c⁻¹ * u * c with hx
  have hx1 : x ≠ 1 := by
    intro h
    apply hu1'
    have : u = c * x * c⁻¹ := by rw [hx]; group
    rw [this, h]; group
  obtain ⟨m, hmM, hm⟩ := htrans x hucj u huZ hx1 hu1'
  have hxu : c * x * c⁻¹ = u := by rw [hx]; group
  have hcm : c⁻¹ * m ∈ Subgroup.centralizer ({x} : Set M) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
    have h2 : m * x * m⁻¹ = c * x * c⁻¹ := hm.trans hxu.symm
    calc x * (c⁻¹ * m) = c⁻¹ * (c * x * c⁻¹) * m := by group
      _ = c⁻¹ * (m * x * m⁻¹) * m := by rw [h2]
      _ = c⁻¹ * m * x := by group
  have hcM : c ∈ M₁ := by
    have h1 : c⁻¹ * m ∈ M₁ := hcent x hucj hx1 hcm
    have h2 : c = m * (c⁻¹ * m)⁻¹ := by group
    rw [h2]
    exact M₁.mul_mem hmM (M₁.inv_mem h1)
  ext y
  rw [mem_cj]
  constructor
  · intro hy
    have := hnorm c hcM _ hy
    simpa [mul_assoc] using this
  · intro hy
    have := hnorm c⁻¹ (M₁.inv_mem hcM) _ hy
    simpa [mul_assoc] using this

theorem cj_eq_of_mem {Z : Subgroup M} (hTI : IsTI Z) {a b t : M} (ha : t ∈ cj a Z)
    (hb : t ∈ cj b Z) (ht : t ≠ 1) : cj a Z = cj b Z := by
  have hc : Z ⊓ cj (b⁻¹ * a) Z ≠ ⊥ := by
    intro h
    have hmem : b⁻¹ * t * b ∈ Z ⊓ cj (b⁻¹ * a) Z := by
      refine Subgroup.mem_inf.mpr ⟨mem_cj.mp hb, mem_cj.mpr ?_⟩
      have : (b⁻¹ * a)⁻¹ * (b⁻¹ * t * b) * (b⁻¹ * a) = a⁻¹ * t * a := by group
      rw [this]
      exact mem_cj.mp ha
    rw [h, Subgroup.mem_bot] at hmem
    apply ht
    have : t = b * (b⁻¹ * t * b) * b⁻¹ := by group
    rw [this, hmem]; group
  have h := hTI _ hc
  have : cj a Z = cj b (cj (b⁻¹ * a) Z) := by rw [← cj_mul]; congr 1; group
  rw [this, h]

theorem exp_of_mem_cj {Z : Subgroup M} (hexp : ∀ x ∈ Z, x * x = 1) {c x : M} (hx : x ∈ cj c Z) :
    x * x = 1 := by
  have h := hexp _ (mem_cj.mp hx)
  have : x * x = c * ((c⁻¹ * x * c) * (c⁻¹ * x * c)) * c⁻¹ := by group
  rw [this, h]
  group

theorem comm_of_mem_cj {Z : Subgroup M} (hcomm : ∀ x ∈ Z, ∀ y ∈ Z, x * y = y * x) {c x y : M}
    (hx : x ∈ cj c Z) (hy : y ∈ cj c Z) : x * y = y * x := by
  have h := hcomm _ (mem_cj.mp hx) _ (mem_cj.mp hy)
  have e1 : x * y = c * ((c⁻¹ * x * c) * (c⁻¹ * y * c)) * c⁻¹ := by group
  have e2 : y * x = c * ((c⁻¹ * y * c) * (c⁻¹ * x * c)) * c⁻¹ := by group
  rw [e1, e2, h]

theorem commute_of_isTI [Finite M] {Z : Subgroup M} (hTI : IsTI Z)
    (hexp : ∀ x ∈ Z, x * x = 1) (hcomm : ∀ x ∈ Z, ∀ y ∈ Z, x * y = y * x)
    {a b v : M} (hv : v ∈ cj b Z) (hv1 : v ≠ 1) (hva : ∀ x ∈ cj a Z, x * v = v * x) :
    ∀ x ∈ cj a Z, ∀ y ∈ cj b Z, x * y = y * x := by
  by_cases hAV : cj a Z = cj b Z
  · intro x hx y hy
    rw [hAV] at hx
    exact comm_of_mem_cj hcomm hx hy
  have hdisj : ∀ t ∈ cj a Z, t ∈ cj b Z → t = 1 := by
    intro t htA htV
    by_contra ht
    exact hAV (cj_eq_of_mem hTI htA htV ht)
  have hnormV : ∀ x ∈ cj a Z, ∀ y ∈ cj b Z, x * y * x⁻¹ ∈ cj b Z := by
    intro x hx y hy
    have hxv : v ∈ cj (x * b) Z := by
      rw [cj_mul, mem_cj]
      have : x⁻¹ * v * x = v := by
        have h1 := hva x hx
        calc x⁻¹ * v * x = x⁻¹ * (v * x) := by group
          _ = x⁻¹ * (x * v) := by rw [h1]
          _ = v := by group
      rw [this]
      exact hv
    have h := cj_eq_of_mem hTI hxv hv hv1
    rw [cj_mul] at h
    have hy' : x * y * x⁻¹ ∈ cj x (cj b Z) := by
      rw [mem_cj]
      have : x⁻¹ * (x * y * x⁻¹) * x = y := by group
      rw [this]
      exact hy
    rw [h] at hy'
    exact hy'
  have hkey : ∀ y ∈ cj b Z, ∀ x ∈ cj a Z, x ≠ 1 → x * y = y * x →
      ∀ x' ∈ cj a Z, x' * y = y * x' := by
    intro y hy x hx hx1 hxy x' hx'
    have hcjA : cj y (cj a Z) = cj a Z := by
      have hxy' : x ∈ cj (y * a) Z := by
        rw [cj_mul, mem_cj]
        have : y⁻¹ * x * y = x := by
          calc y⁻¹ * x * y = y⁻¹ * (x * y) := by group
            _ = y⁻¹ * (y * x) := by rw [hxy]
            _ = x := by group
        rw [this]
        exact hx
      have h := cj_eq_of_mem hTI hxy' hx hx1
      rw [cj_mul] at h
      exact h
    have h1 : y * x'⁻¹ * y⁻¹ ∈ cj a Z := by
      have : y * x'⁻¹ * y⁻¹ ∈ cj y (cj a Z) := by
        rw [mem_cj]
        have e : y⁻¹ * (y * x'⁻¹ * y⁻¹) * y = x'⁻¹ := by group
        rw [e]
        exact (cj a Z).inv_mem hx'
      rwa [hcjA] at this
    have h2 : x' * y * x'⁻¹ * y⁻¹ ∈ cj b Z :=
      (cj b Z).mul_mem (hnormV x' hx' y hy) ((cj b Z).inv_mem hy)
    have h3 : x' * y * x'⁻¹ * y⁻¹ ∈ cj a Z := by
      have : x' * y * x'⁻¹ * y⁻¹ = x' * (y * x'⁻¹ * y⁻¹) := by group
      rw [this]
      exact (cj a Z).mul_mem hx' h1
    have h4 := hdisj _ h3 h2
    calc x' * y = (x' * y * x'⁻¹ * y⁻¹) * (y * x') := by group
      _ = y * x' := by rw [h4]; group
  by_contra hcon
  push Not at hcon
  obtain ⟨x0, hx0, y0, hy0, hne⟩ := hcon
  set V0 : Subgroup M := cj b Z ⊓ Subgroup.centralizer (cj a Z : Set M) with hV0
  have hy0V0 : y0 ∉ V0 := by
    intro h
    exact hne (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp h).2 x0 hx0)
  have hφ : ∀ x ∈ cj a Z, x * y0 * x⁻¹ * y0⁻¹ ∈ V0 := by
    intro x hx
    have hφV : x * y0 * x⁻¹ * y0⁻¹ ∈ cj b Z :=
      (cj b Z).mul_mem (hnormV x hx y0 hy0) ((cj b Z).inv_mem hy0)
    refine Subgroup.mem_inf.mpr ⟨hφV, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    by_cases hx1 : x = 1
    · subst hx1
      intro x' _
      simp
    · have hxx : x * x = 1 := exp_of_mem_cj hexp hx
      have hinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hxx
      have hφφ : (x * y0 * x⁻¹ * y0⁻¹) * (x * y0 * x⁻¹ * y0⁻¹) = 1 :=
        exp_of_mem_cj hexp hφV
      have hφinv : (x * y0 * x⁻¹ * y0⁻¹)⁻¹ = x * y0 * x⁻¹ * y0⁻¹ :=
        inv_eq_of_mul_eq_one_right hφφ
      have hconj : x * (x * y0 * x⁻¹ * y0⁻¹) * x⁻¹ = (x * y0 * x⁻¹ * y0⁻¹)⁻¹ := by
        rw [hinv]
        calc x * (x * y0 * x * y0⁻¹) * x = (x * x) * y0 * x * y0⁻¹ * x := by group
          _ = y0 * x * y0⁻¹ * x := by rw [hxx]; group
          _ = (x * y0 * x * y0⁻¹)⁻¹ := by
            rw [mul_inv_rev, mul_inv_rev, mul_inv_rev, hinv]
            group
      have hxφ : x * (x * y0 * x⁻¹ * y0⁻¹) = (x * y0 * x⁻¹ * y0⁻¹) * x := by
        have h1 : x * (x * y0 * x⁻¹ * y0⁻¹) * x⁻¹ = x * y0 * x⁻¹ * y0⁻¹ := by
          rw [hconj, hφinv]
        calc x * (x * y0 * x⁻¹ * y0⁻¹) = (x * (x * y0 * x⁻¹ * y0⁻¹) * x⁻¹) * x := by group
          _ = (x * y0 * x⁻¹ * y0⁻¹) * x := by rw [h1]
      exact hkey _ hφV x hx hx1 hxφ
  have hinj : Function.Injective
      (fun x : cj a Z => (⟨x * y0 * x⁻¹ * y0⁻¹, hφ x x.2⟩ : V0)) := by
    intro x x' h
    have h' : (x : M) * y0 * (x : M)⁻¹ * y0⁻¹ = (x' : M) * y0 * (x' : M)⁻¹ * y0⁻¹ :=
      congrArg Subtype.val h
    have h2 : (x : M) * y0 * (x : M)⁻¹ = (x' : M) * y0 * (x' : M)⁻¹ := mul_right_cancel h'
    have hc : ((x' : M)⁻¹ * x) * y0 = y0 * ((x' : M)⁻¹ * x) := by
      have h3 : (x' : M)⁻¹ * ((x : M) * y0 * (x : M)⁻¹) * x' = y0 := by rw [h2]; group
      calc ((x' : M)⁻¹ * x) * y0
          = ((x' : M)⁻¹ * ((x : M) * y0 * (x : M)⁻¹) * x') * ((x' : M)⁻¹ * x) := by group
        _ = y0 * ((x' : M)⁻¹ * x) := by rw [h3]
    by_contra hxx'
    have hne1 : (x' : M)⁻¹ * x ≠ 1 := by
      intro h1
      apply hxx'
      apply Subtype.ext
      exact (inv_mul_eq_one.mp h1).symm
    have hmem : (x' : M)⁻¹ * x ∈ cj a Z := (cj a Z).mul_mem ((cj a Z).inv_mem x'.2) x.2
    exact hne (hkey y0 hy0 _ hmem hne1 hc x0 hx0)
  have hcardA : Nat.card (cj a Z) = Nat.card (cj b Z) := by rw [card_cj, card_cj]
  have hle : Nat.card (cj a Z) ≤ Nat.card V0 := Nat.card_le_card_of_injective _ hinj
  have hEq : V0 = cj b Z := Subgroup.eq_of_le_of_card_ge inf_le_left (hcardA ▸ hle)
  exact hy0V0 (hEq ▸ hy0)

end CFSG.Quasithin.H13.F431.NF
