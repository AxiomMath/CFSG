module

public import CFSG.Quasithin.Vol2.Ch10SecKL7o
public import CFSG.Quasithin.Vol2.Ch10SecKL7n

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.KL7

open CFSG.Quasithin CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

variable {W : Type} [CommGroup W]

namespace Coord

variable {L : Subgroup (MulAut W)} {U : Subgroup W} (c : Coord L U)

@[expose] noncomputable def phi : SL32 →* MulAut W := L.subtype.comp c.π.toMonoidHom

theorem phi_injective : Function.Injective c.phi :=
  Subtype.val_injective.comp c.π.injective

theorem phi_mem (γ : SL32) : c.phi γ ∈ L := (c.π γ).2

theorem range_phi : c.phi.range = L := by
  ext x
  constructor
  · rintro ⟨γ, rfl⟩
    exact c.phi_mem γ
  · intro hx
    obtain ⟨γ, hγ⟩ := c.π.surjective ⟨x, hx⟩
    exact ⟨γ, congrArg Subtype.val hγ⟩

theorem eq_P_of_le {X : Subgroup (MulAut W)} (hXL : X ≤ L) (hX : IsPGroup 2 X)
    (hPX : U3.map c.phi ≤ X) : X = U3.map c.phi := by
  have hcomap : (X.comap c.phi).map c.phi = X := by
    rw [Subgroup.map_comap_eq, c.range_phi, inf_eq_right.2 hXL]
  have hpX : IsPGroup 2 ↥(X.comap c.phi) := hX.comap_of_injective c.phi c.phi_injective
  obtain ⟨j, hj3, hj⟩ := exists_card_of_isPGroup _ hpX
  have hcX : Nat.card X = 2 ^ j := by
    rw [← hcomap, Subgroup.card_map_of_injective c.phi_injective, hj]
  have hcP : Nat.card (U3.map c.phi) = 8 := by
    rw [Subgroup.card_map_of_injective c.phi_injective, card_U3]
  have : Finite ↥X := Nat.finite_of_card_ne_zero (by rw [hcX]; positivity)
  refine (Subgroup.eq_of_le_of_card_ge hPX ?_).symm
  rw [hcX, hcP]
  calc 2 ^ j ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) hj3
    _ = 8 := by norm_num

end Coord

namespace Hyp

variable {Mb L₁ L₂ R : Subgroup (MulAut W)} {W₁ W₂ : Subgroup W} {τ : MulAut W}

theorem comm_L₂_C : ∀ (b : ↥L₂) (c : ↥(CM Mb L₁ L₂)),
    Commute (L₂.subtype b) ((CM Mb L₁ L₂).subtype c) :=
  fun b c => (Hyp.mem_C_iff.1 c.2).2.2 b b.2

theorem mem_normalizer_of_comm {L : Subgroup (MulAut W)} {y : MulAut W}
    (hy : ∀ l ∈ L, l * y = y * l) : y ∈ Subgroup.normalizer (L : Set (MulAut W)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro l
  constructor
  · intro hl
    rw [← hy l hl, mul_inv_cancel_right]
    exact hl
  · intro hl
    have h1 := hy _ hl
    have : l = y * l * y⁻¹ := by
      calc l = y⁻¹ * (y * l * y⁻¹) * y := by group
        _ = y⁻¹ * (y * (y * l * y⁻¹)) := by rw [mul_assoc, ← h1]
        _ = y * l * y⁻¹ := by group
    rw [this]
    exact hl

variable (h : Hyp Mb L₁ L₂ W₁ W₂ τ)
include h

theorem conj_mem_K {g x : MulAut W} (hg : g ∈ Mb) (hx : x ∈ Mb)
    (hxK : x ∈ Subgroup.normalizer (L₁ : Set (MulAut W))) :
    g * x * g⁻¹ ∈ Subgroup.normalizer (L₁ : Set (MulAut W)) := by
  have hg' := Mb.inv_mem hg
  have h1 : g * g⁻¹ ∈ Subgroup.normalizer (L₁ : Set (MulAut W)) := by
    rw [mul_inv_cancel]
    exact one_mem _
  rw [h.mul_mem_K hg hg'] at h1
  rw [h.mul_mem_K (mul_mem hg hx) hg', h.mul_mem_K hg hx]
  simp only [hxK, iff_true]
  exact h1

theorem comm_L₁_L₂C : ∀ (a : ↥L₁) (bc : ↥L₂ × ↥(CM Mb L₁ L₂)),
    Commute (L₁.subtype a)
      ((L₂.subtype.noncommCoprod (CM Mb L₁ L₂).subtype comm_L₂_C) bc) := by
  rintro a ⟨b, c⟩
  show (a : MulAut W) * ((b : MulAut W) * c) = ((b : MulAut W) * c) * a
  have e1 : (a : MulAut W) * b = b * a := h.comm' a.2 b.2
  have e2 : (a : MulAut W) * c = c * a := (Hyp.mem_C_iff.1 c.2).2.1 a a.2
  calc (a : MulAut W) * ((b : MulAut W) * c) = a * b * c := by group
    _ = b * a * c := by rw [e1]
    _ = b * (a * c) := by group
    _ = b * (c * a) := by rw [e2]
    _ = (b : MulAut W) * c * a := by group

@[expose] noncomputable def mul3 : ↥L₁ × (↥L₂ × ↥(CM Mb L₁ L₂)) →* MulAut W :=
  L₁.subtype.noncommCoprod (L₂.subtype.noncommCoprod (CM Mb L₁ L₂).subtype comm_L₂_C)
    h.comm_L₁_L₂C

theorem mul3_apply (p : ↥L₁ × (↥L₂ × ↥(CM Mb L₁ L₂))) :
    h.mul3 p = (p.1 : MulAut W) * ((p.2.1 : MulAut W) * p.2.2) := rfl

theorem injective_mul3 : Function.Injective h.mul3 := by
  rw [injective_iff_map_eq_one]
  rintro ⟨a, b, c⟩ habc
  rw [mul3_apply, ← mul_assoc] at habc
  obtain ⟨ha, hb, hc⟩ := h.decomp_eq_one a.2 b.2 c.2 habc
  exact Prod.ext (Subtype.ext ha) (Prod.ext (Subtype.ext hb) (Subtype.ext hc))

theorem range_mul3 : h.mul3.range = Mb ⊓ Subgroup.normalizer (L₁ : Set (MulAut W)) := by
  ext x
  constructor
  · rintro ⟨⟨a, b, c⟩, rfl⟩
    rw [mul3_apply]
    refine ⟨mul_mem (h.le₁ a.2) (mul_mem (h.le₂ b.2) c.2.1), ?_⟩
    refine mul_mem (Subgroup.le_normalizer a.2) (mul_mem ?_ ?_)
    · exact mem_normalizer_of_comm fun l hl => h.comm' hl b.2
    · exact mem_normalizer_of_comm fun l hl => (Hyp.mem_C_iff.1 c.2).2.1 l hl
  · rintro ⟨hx, hxK⟩
    obtain ⟨a, ha, b, hb, c, hc, rfl⟩ := h.exists_decomp hx (mem_normalizer_iff_map.1 hxK)
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩), by rw [mul3_apply, mul_assoc]⟩

@[expose] noncomputable def pr₁ :
    ↥(Mb ⊓ Subgroup.normalizer (L₁ : Set (MulAut W))) →* ↥L₁ :=
  (MonoidHom.fst _ _).comp ((MonoidHom.ofInjective h.injective_mul3).symm.toMonoidHom.comp
    (Subgroup.inclusion h.range_mul3.ge))

theorem pr₁_spec (x : ↥(Mb ⊓ Subgroup.normalizer (L₁ : Set (MulAut W)))) :
    ∃ y ∈ Subgroup.centralizer (L₁ : Set (MulAut W)),
      (x : MulAut W) = (h.pr₁ x : MulAut W) * y := by
  set p := (MonoidHom.ofInjective h.injective_mul3).symm (Subgroup.inclusion h.range_mul3.ge x)
    with hpdef
  have hp : h.mul3 p = x := by
    have := congrArg Subtype.val
      ((MonoidHom.ofInjective h.injective_mul3).apply_symm_apply (Subgroup.inclusion
        h.range_mul3.ge x))
    rw [← hpdef] at this
    exact this
  refine ⟨(p.2.1 : MulAut W) * p.2.2, Subgroup.mem_centralizer_iff.2 fun l hl => ?_, ?_⟩
  · have e1 : l * (p.2.1 : MulAut W) = p.2.1 * l := h.comm' hl p.2.1.2
    have e2 : l * (p.2.2 : MulAut W) = p.2.2 * l := (Hyp.mem_C_iff.1 p.2.2.2).2.1 l hl
    calc l * ((p.2.1 : MulAut W) * p.2.2) = l * p.2.1 * p.2.2 := by group
      _ = p.2.1 * l * p.2.2 := by rw [e1]
      _ = p.2.1 * (l * p.2.2) := by group
      _ = p.2.1 * (p.2.2 * l) := by rw [e2]
      _ = (p.2.1 : MulAut W) * p.2.2 * l := by group
  · rw [← hp, mul3_apply]
    rfl

theorem pr₁_of_mem (x : ↥(Mb ⊓ Subgroup.normalizer (L₁ : Set (MulAut W))))
    (hx : (x : MulAut W) ∈ L₁) : h.pr₁ x = ⟨x, hx⟩ := by
  have h1 : (MonoidHom.ofInjective h.injective_mul3).symm (Subgroup.inclusion h.range_mul3.ge x) =
      (⟨x, hx⟩, 1, 1) := by
    rw [MulEquiv.symm_apply_eq]
    apply Subtype.ext
    show (x : MulAut W) = h.mul3 (⟨x, hx⟩, 1, 1)
    rw [mul3_apply]
    simp
  show ((MonoidHom.ofInjective h.injective_mul3).symm (Subgroup.inclusion h.range_mul3.ge x)).1 = _
  rw [h1]

end Hyp

end CFSG.Quasithin.Vol2.Ch10.SecB.KL7
