module

public import CFSG.RankThree.PartOne.SEITZ12.CaseBBasic

public section

namespace CFSG.RankThree.PartOne.SEITZ12

open Subgroup

variable {G : Type*} [Group G]

namespace phi4B_Core

variable {X₂ S₂ Z₂ : Subgroup G} {t : G} {q : ℕ}

theorem card_Om (h : phi4B_Core X₂ S₂ Z₂ t q) : Nat.card (phi4B_Om Z₂ t) = q ^ 2 := by
  let f : ↥(conjSub Z₂ t) × ↥Z₂ → ↥(phi4B_Om Z₂ t) := fun p =>
    ⟨p.1.1 * p.2.1, mul_mem (mem_sup_left p.1.2) (mem_sup_right p.2.2)⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ ⟨⟨a', ha'⟩, ⟨b', hb'⟩⟩ hab
      have hab' : a * b = a' * b' := congrArg Subtype.val hab
      obtain ⟨h1, h2⟩ := h.mul_inj (h.S₁_le (h.Z₁_le ha)) (h.S₁_le (h.Z₁_le ha'))
        (h.S₂_le (h.suz.Z_le hb)) (h.S₂_le (h.suz.Z_le hb')) hab'
      subst h1
      subst h2
      rfl
    · rintro ⟨x, hx⟩
      obtain ⟨a, ha, b, hb, rfl⟩ := h.mem_Om.1 hx
      exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩
  rw [← Nat.card_eq_of_bijective f hf, Nat.card_prod, h.suz₁.card_Z, h.suz.card_Z, sq]

theorem cent_S (h : phi4B_Core X₂ S₂ Z₂ t q) {y : G} (hy : y ∈ phi4B_S h) (hy2 : y * y = 1)
    (hyt : t * y * t = y) :
    ∃ z ∈ conjSub Z₂ t, y = z * (t * z * t) ∨ y = z * (t * z * t) * t := by
  rcases hy with hy | ⟨b, hb, rfl⟩
  · obtain ⟨z, hz, e⟩ := h.cent_B0 hy hy2 hyt
    exact ⟨z, hz, Or.inl e⟩
  · have hbt : t * b * t = b := by
      have e1 : (t * b * t) * t = b * t := by
        calc (t * b * t) * t = t * (b * t) * t := by simp only [mul_assoc]
          _ = b * t := hyt
      exact mul_right_cancel e1
    have hb2 : b * b = 1 := by
      calc b * b = b * (t * b * t) := by rw [hbt]
        _ = b * t * (b * t) := by simp only [mul_assoc]
        _ = 1 := hy2
    obtain ⟨z, hz, e⟩ := h.cent_B0 hb hb2 hbt
    exact ⟨z, hz, Or.inr (by rw [e])⟩

theorem card_le_of_conj (h : phi4B_Core X₂ S₂ Z₂ t q) {s : G} (hs : s ∈ conjSub S₂ t)
    {E : Subgroup G} (hES : E ≤ phi4B_S h) (hE : ∀ x ∈ E, x * x = 1)
    (hu : s * t * s⁻¹ ∈ E) : Nat.card E ≤ 2 * q := by
  have : Finite ↥(conjSub Z₂ t) :=
    Nat.finite_of_card_ne_zero (by rw [h.suz₁.card_Z]; have := h.q_ge; omega)
  let f : ↥(conjSub Z₂ t) × Bool → G := fun p =>
    s * (p.1.1 * (t * p.1.1 * t) * (if p.2 then t else 1)) * s⁻¹
  have hsS : s ∈ phi4B_S h := h.B0_le_S (h.S₁_le_B0 hs)
  have hsub : (E : Set G) ⊆ Set.range f := by
    intro x hx
    have hxE : x ∈ E := hx
    have hxu : x * (s * t * s⁻¹) = (s * t * s⁻¹) * x := by
      apply phi4B_comm_of_sq (hE x hxE) (hE _ hu)
      exact hE _ (mul_mem hxE hu)
    set y := s⁻¹ * x * s with hy
    have hyS : y ∈ phi4B_S h := mul_mem (mul_mem (inv_mem hsS) (hES hxE)) hsS
    have hy2 : y * y = 1 := by
      have e : y * y = s⁻¹ * (x * x) * s := by rw [hy]; group
      rw [e, hE x hxE]
      group
    have hyt : t * y * t = y := by
      have e1 : y * t = t * y := by
        calc y * t = s⁻¹ * (x * (s * t * s⁻¹)) * s := by rw [hy]; group
          _ = s⁻¹ * ((s * t * s⁻¹) * x) * s := by rw [hxu]
          _ = t * y := by rw [hy]; group
      calc t * y * t = y * t * t := by rw [e1]
        _ = y := by rw [mul_assoc, h.t_sq, mul_one]
    obtain ⟨z, hz, hzy⟩ := h.cent_S hyS hy2 hyt
    have hx' : x = s * y * s⁻¹ := by rw [hy]; group
    rcases hzy with e | e
    · refine ⟨(⟨z, hz⟩, false), ?_⟩
      simp only [f, Bool.false_eq_true, ite_false, mul_one]
      rw [hx', e]
    · refine ⟨(⟨z, hz⟩, true), ?_⟩
      simp only [f, ite_true]
      rw [hx', e]
  have hfin : (Set.range f).Finite := Set.finite_range f
  calc Nat.card E = Nat.card (E : Set G) := rfl
    _ ≤ Nat.card (Set.range f) := Nat.card_mono hfin hsub
    _ ≤ Nat.card (↥(conjSub Z₂ t) × Bool) :=
        Nat.card_le_card_of_surjective _ Set.rangeFactorization_surjective
    _ = 2 * q := by
        rw [Nat.card_prod, h.suz₁.card_Z, Nat.card_eq_fintype_card, Fintype.card_bool, mul_comm]

theorem B1 (h : phi4B_Core X₂ S₂ Z₂ t q) {E : Subgroup G} (hES : E ≤ phi4B_S h)
    (hE : ∀ x ∈ E, x * x = 1) (hcard : q ^ 2 ≤ Nat.card E) : E ≤ phi4B_Om Z₂ t := by
  intro x hx
  by_cases hxB : x ∈ phi4B_B0 S₂ t
  · exact h.inv_mem_Om hxB (hE x hx)
  · exfalso
    rcases hES hx with hx' | ⟨b, hb, rfl⟩
    · exact hxB hx'
    · obtain ⟨s, hs, hsu⟩ := h.inv_B0t hb (hE _ hx)
      have hle := h.card_le_of_conj hs hES hE (hsu ▸ hx)
      have hq := h.q_ge
      nlinarith [hle, hcard, hq]

theorem conj_Om_le (h : phi4B_Core X₂ S₂ Z₂ t q) {n : G}
    (hn : ∀ s ∈ phi4B_S h, n * s * n⁻¹ ∈ phi4B_S h) {z : G} (hz : z ∈ phi4B_Om Z₂ t) :
    n * z * n⁻¹ ∈ phi4B_Om Z₂ t := by
  let E : Subgroup G := (phi4B_Om Z₂ t).map (MulAut.conj n).toMonoidHom
  have hE_le : E ≤ phi4B_S h := by
    rintro _ ⟨w, hw, rfl⟩
    exact hn w (h.B0_le_S (h.Om_le_B0 hw))
  have hEsq : ∀ x ∈ E, x * x = 1 := by
    rintro _ ⟨w, hw, rfl⟩
    have e : (n * w * n⁻¹) * (n * w * n⁻¹) = n * (w * w) * n⁻¹ := by group
    show (n * w * n⁻¹) * (n * w * n⁻¹) = 1
    rw [e, h.Om_sq hw]
    group
  have hEcard : q ^ 2 ≤ Nat.card E := by
    rw [Subgroup.card_map_of_injective (MulAut.conj n).injective, h.card_Om]
  exact h.B1 hE_le hEsq hEcard ⟨z, hz, rfl⟩

end phi4B_Core

end CFSG.RankThree.PartOne.SEITZ12
