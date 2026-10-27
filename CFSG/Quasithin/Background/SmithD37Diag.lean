module

public import CFSG.Quasithin.Background.SmithD37Core

public section

namespace CFSG.Quasithin.SmithD37

variable {U : Type} [CommGroup U] {L₁ L₂ : Subgroup (MulAut U)}

@[expose] def diag (t l : MulAut U) : MulAut U := l * (t * l * t⁻¹)

section Diag

variable {t : MulAut U} (ht : t * t = 1) (hcomm : ∀ x ∈ L₁, ∀ y ∈ L₂, x * y = y * x)
  (hsw : ∀ l ∈ L₁, t * l * t⁻¹ ∈ L₂)
include ht hcomm hsw

omit ht in
theorem diag_mul {x y : MulAut U} (hx : x ∈ L₁) (hy : y ∈ L₁) :
    diag t (x * y) = diag t x * diag t y := by
  have h := hcomm y hy _ (hsw x hx)
  simp only [diag]
  calc x * y * (t * (x * y) * t⁻¹) = x * (y * (t * x * t⁻¹)) * (t * y * t⁻¹) := by group
    _ = x * ((t * x * t⁻¹) * y) * (t * y * t⁻¹) := by rw [h]
    _ = x * (t * x * t⁻¹) * (y * (t * y * t⁻¹)) := by group

omit hcomm hsw in
theorem inv_eq_self : t⁻¹ = t := by
  rw [inv_eq_iff_mul_eq_one]
  exact ht

theorem diag_comm_t {l : MulAut U} (hl : l ∈ L₁) : t * diag t l = diag t l * t := by
  have h := hcomm l hl _ (hsw l hl)
  have hti : t⁻¹ = t := inv_eq_self ht
  simp only [diag]
  calc t * (l * (t * l * t⁻¹)) = (t * l * t⁻¹) * l * t := by rw [hti]; group
    _ = l * (t * l * t⁻¹) * t := by rw [← h]

theorem diag_apply_t {l : MulAut U} (hl : l ∈ L₁) (u : U) : diag t l (t u) = t (diag t l u) := by
  have h := congrArg (fun φ : MulAut U => φ u) (diag_comm_t ht hcomm hsw hl)
  simpa [MulAut.mul_apply] using h.symm

omit ht hcomm in
theorem diag_eq_one {g : MulAut U} (hg : g ∈ L₁) (hinf : L₁ ⊓ L₂ = ⊥) (h : diag t g = 1) :
    g = 1 := by
  have h1 : g⁻¹ = t * g * t⁻¹ := inv_eq_of_mul_eq_one_right h
  have h2 : g⁻¹ ∈ L₁ ⊓ L₂ := ⟨L₁.inv_mem hg, h1 ▸ hsw g hg⟩
  rw [hinf, Subgroup.mem_bot, inv_eq_one] at h2
  exact h2

theorem diag_mul_self (hexp : ∀ u : U, u ^ 2 = 1) {g : MulAut U} (hg : g ∈ L₁)
    (hfix : ∀ u, t u = u → diag t g u = u) : diag t g * diag t g = 1 := by
  have htt : ∀ u, t (t u) = u := fun u => by
    rw [← MulAut.mul_apply, ht, MulAut.one_apply]
  have hinv : ∀ w : U, w⁻¹ = w := fun w => by
    rw [inv_eq_iff_mul_eq_one, ← pow_two, hexp]
  ext u
  set δ := diag t g
  have hv : t (u * t u) = u * t u := by rw [map_mul, htt, mul_comm]
  have h1 : δ u * t (δ u) = u * t u := by
    have := hfix _ hv
    rwa [map_mul, diag_apply_t ht hcomm hsw hg] at this
  set w := δ u * u⁻¹ with hw
  have hwt : t w = w := by
    have h3 : t (δ u) = (δ u)⁻¹ * (u * t u) := eq_inv_mul_of_mul_eq h1
    rw [hw, map_mul, map_inv, h3, ← mul_assoc, mul_inv_cancel_right, hinv (δ u), hinv u]
  have hδw : δ w = w := hfix w hwt
  have hδu : δ u = w * u := by rw [hw, inv_mul_cancel_right]
  show δ (δ u) = u
  rw [hδu, map_mul, hδw, hδu, ← mul_assoc, ← pow_two, hexp, one_mul]


omit ht hcomm hsw in
theorem diag_one : diag t (1 : MulAut U) = 1 := by
  simp [diag]

omit ht in
theorem diag_inv {x : MulAut U} (hx : x ∈ L₁) : diag t x⁻¹ = (diag t x)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← diag_mul hcomm hsw (L₁.inv_mem hx) hx, inv_mul_cancel]
  exact diag_one

omit ht hcomm hsw in
theorem diag_conj {a l : MulAut U} (hat : a * t = t * a) :
    diag t (a * l * a⁻¹) = a * diag t l * a⁻¹ := by
  have hta : t⁻¹ * a⁻¹ = a⁻¹ * t⁻¹ := by
    rw [← mul_inv_rev, ← mul_inv_rev, hat]
  simp only [diag]
  calc a * l * a⁻¹ * (t * (a * l * a⁻¹) * t⁻¹)
      = a * l * a⁻¹ * ((t * a) * l * (a⁻¹ * t⁻¹)) := by group
    _ = a * l * a⁻¹ * ((a * t) * l * (t⁻¹ * a⁻¹)) := by rw [hat, hta]
    _ = a * (l * (t * l * t⁻¹)) * a⁻¹ := by group

theorem diag_inv_apply_t {l : MulAut U} (hl : l ∈ L₁) {u : U} (hu : t u = u) :
    t ((diag t l)⁻¹ u) = (diag t l)⁻¹ u := by
  have h := diag_apply_t ht hcomm hsw hl ((diag t l)⁻¹ u)
  rw [MulAut.inv_apply, MulEquiv.apply_symm_apply, hu] at h
  rw [MulAut.inv_apply]
  exact (MulEquiv.eq_symm_apply _).mpr h

theorem commute_of_fix_t (hexp : ∀ u : U, u ^ 2 = 1) (hinf : L₁ ⊓ L₂ = ⊥)
    [IsSimpleGroup ↥L₁] (hnc : ∃ x y : ↥L₁, x * y ≠ y * x) {a : MulAut U}
    (hat : a * t = t * a) (haN : ∀ l ∈ L₁, a * l * a⁻¹ ∈ L₁)
    (hfix : ∀ u, t u = u → a u = u) : ∀ l ∈ L₁, a * l = l * a := by
  let K : Subgroup ↥L₁ :=
    { carrier := {g | ∀ u, t u = u → diag t g u = u}
      one_mem' := fun u _ => by
        show diag t (1 : MulAut U) u = u
        rw [diag_one, MulAut.one_apply]
      mul_mem' := fun {x y} hx hy u hu => by
        show diag t ((x : MulAut U) * y) u = u
        rw [diag_mul hcomm hsw x.2 y.2, MulAut.mul_apply, hy u hu, hx u hu]
      inv_mem' := fun {x} hx u hu => by
        show diag t ((x : MulAut U)⁻¹) u = u
        rw [diag_inv hcomm hsw x.2, MulAut.inv_apply, MulEquiv.symm_apply_eq]
        exact (hx u hu).symm }
  have hK : K.Normal := by
    refine ⟨fun g hg h u hu => ?_⟩
    show diag t ((h : MulAut U) * g * (h : MulAut U)⁻¹) u = u
    rw [diag_mul hcomm hsw (L₁.mul_mem h.2 g.2) (L₁.inv_mem h.2),
      diag_mul hcomm hsw h.2 g.2, diag_inv hcomm hsw h.2, MulAut.mul_apply,
      MulAut.mul_apply, hg _ (diag_inv_apply_t ht hcomm hsw h.2 hu), MulAut.inv_apply,
      MulEquiv.apply_symm_apply]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal K with hK | hK
  · intro l hl
    have hm := haN l hl
    have hmem : (⟨a * l * a⁻¹ * l⁻¹, L₁.mul_mem hm (L₁.inv_mem hl)⟩ : ↥L₁) ∈ K := by
      intro u hu
      have hu' := diag_inv_apply_t ht hcomm hsw hl hu
      have ha' : a⁻¹ ((diag t l)⁻¹ u) = (diag t l)⁻¹ u := by
        rw [MulAut.inv_apply, MulEquiv.symm_apply_eq]
        exact (hfix _ hu').symm
      show diag t (a * l * a⁻¹ * l⁻¹) u = u
      rw [diag_mul hcomm hsw hm (L₁.inv_mem hl), diag_conj hat, diag_inv hcomm hsw hl,
        MulAut.mul_apply, MulAut.mul_apply, MulAut.mul_apply, ha',
        show diag t l ((diag t l)⁻¹ u) = u from by
          rw [MulAut.inv_apply, MulEquiv.apply_symm_apply], hfix u hu]
    rw [hK, Subgroup.mem_bot] at hmem
    have h1 : a * l * a⁻¹ * l⁻¹ = 1 := congrArg Subtype.val hmem
    rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h1
    exact h1
  · exfalso
    have hsq : ∀ g : ↥L₁, g * g = 1 := by
      intro g
      have hg : g ∈ K := hK ▸ Subgroup.mem_top g
      have h1 := diag_mul_self ht hcomm hsw hexp g.2 hg
      rw [← diag_mul hcomm hsw g.2 g.2] at h1
      exact Subtype.ext (diag_eq_one hsw (L₁.mul_mem g.2 g.2) hinf h1)
    obtain ⟨x, y, hxy⟩ := hnc
    apply hxy
    have h1 := hsq (x * y)
    calc x * y = (x * y) * (y * x) * (y * x) := by
          rw [mul_assoc (x * y), hsq (y * x), mul_one]
      _ = y * x := by
          rw [show (x * y) * (y * x) = 1 by
            rw [mul_assoc, ← mul_assoc y y, hsq y, one_mul, hsq x], one_mul]

end Diag

end CFSG.Quasithin.SmithD37
