module

public import Mathlib.Tactic.Group
public import Mathlib.Algebra.Group.Subgroup.Lattice

public section

namespace CFSG.Quasithin

namespace F53.Stellmacher.S42Gt

variable {G : Type} [Group G]

structure ElemNorm (E : Subgroup G) (d : G) : Prop where
  comm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x
  sq : ∀ x ∈ E, x * x = 1
  norm : ∀ x ∈ E, d * x * d⁻¹ ∈ E
  cube : d * d * d = 1

namespace ElemNorm

variable {E : Subgroup G} {d : G}

theorem norm_inv (h : ElemNorm E d) {x : G} (hx : x ∈ E) : d⁻¹ * x * d ∈ E := by
  have hinv : d * d = d⁻¹ := eq_inv_of_mul_eq_one_left h.cube
  have e : d⁻¹ * x * d = d * (d * x * d⁻¹) * d⁻¹ := by
    have : d * (d * x * d⁻¹) * d⁻¹ = (d * d) * x * (d * d)⁻¹ := by group
    rw [this, hinv]
    group
  rw [e]
  exact h.norm _ (h.norm _ hx)

end ElemNorm

def dCom (E : Subgroup G) (d : G) (h : ElemNorm E d) : Subgroup G where
  carrier := {u | ∃ e ∈ E, u = e * (d * e * d⁻¹)}
  one_mem' := ⟨1, E.one_mem, by group⟩
  mul_mem' := by
    rintro _ _ ⟨e, he, rfl⟩ ⟨f, hf, rfl⟩
    refine ⟨e * f, E.mul_mem he hf, ?_⟩
    have h1 : d * e * d⁻¹ ∈ E := h.norm e he
    have c1 : (d * e * d⁻¹) * f = f * (d * e * d⁻¹) := h.comm _ h1 _ hf
    calc e * (d * e * d⁻¹) * (f * (d * f * d⁻¹))
        = e * ((d * e * d⁻¹) * f) * (d * f * d⁻¹) := by group
      _ = e * (f * (d * e * d⁻¹)) * (d * f * d⁻¹) := by rw [c1]
      _ = e * f * (d * (e * f) * d⁻¹) := by group
  inv_mem' := by
    rintro _ ⟨e, he, rfl⟩
    refine ⟨e⁻¹, E.inv_mem he, ?_⟩
    have h2 : d * e⁻¹ * d⁻¹ ∈ E := h.norm _ (E.inv_mem he)
    have c2 : (d * e⁻¹ * d⁻¹) * e⁻¹ = e⁻¹ * (d * e⁻¹ * d⁻¹) := h.comm _ h2 _ (E.inv_mem he)
    calc (e * (d * e * d⁻¹))⁻¹ = (d * e⁻¹ * d⁻¹) * e⁻¹ := by group
      _ = e⁻¹ * (d * e⁻¹ * d⁻¹) := c2

variable {E : Subgroup G} {d : G}

theorem mem_dCom {h : ElemNorm E d} {e : G} (he : e ∈ E) : e * (d * e * d⁻¹) ∈ dCom E d h :=
  ⟨e, he, rfl⟩

theorem dCom_le (h : ElemNorm E d) : dCom E d h ≤ E := by
  rintro _ ⟨e, he, rfl⟩
  exact E.mul_mem he (h.norm e he)

theorem dCom_eq_bot_iff (h : ElemNorm E d) : dCom E d h = ⊥ ↔ ∀ e ∈ E, d * e * d⁻¹ = e := by
  constructor
  · intro hb e he
    have hm : e * (d * e * d⁻¹) ∈ dCom E d h := mem_dCom he
    rw [hb, Subgroup.mem_bot] at hm
    have h1 : e⁻¹ = e := inv_eq_of_mul_eq_one_right (h.sq e he)
    have h2 : d * e * d⁻¹ = e⁻¹ := eq_inv_of_mul_eq_one_right hm
    rw [h2, h1]
  · intro hf
    rw [eq_bot_iff]
    rintro _ ⟨e, he, rfl⟩
    rw [Subgroup.mem_bot, hf e he]
    exact h.sq e he

theorem eq_one_of_fix (h : ElemNorm E d) {u : G} (hu : u ∈ dCom E d h)
    (hfix : d * u * d⁻¹ = u) : u = 1 := by
  obtain ⟨e, he, rfl⟩ := hu
  have he1 : d * e * d⁻¹ ∈ E := h.norm e he
  have h1 : (d * e * d⁻¹) * (d * (d * e * d⁻¹) * d⁻¹) = e * (d * e * d⁻¹) := by
    calc (d * e * d⁻¹) * (d * (d * e * d⁻¹) * d⁻¹) = d * (e * (d * e * d⁻¹)) * d⁻¹ := by group
      _ = e * (d * e * d⁻¹) := hfix
  have h2 : d * (d * e * d⁻¹) * d⁻¹ = e := by
    refine mul_left_cancel (a := d * e * d⁻¹) ?_
    rw [h1]
    exact h.comm e he _ he1
  have h3 : d * (d * (d * e * d⁻¹) * d⁻¹) * d⁻¹ = e := by
    have : d * (d * (d * e * d⁻¹) * d⁻¹) * d⁻¹ = (d * d * d) * e * (d * d * d)⁻¹ := by group
    rw [this, h.cube]
    group
  have h4 : d * e * d⁻¹ = e := by
    rw [← h2] at h3
    simpa [h2] using h3
  rw [h4]
  exact h.sq e he

theorem dCom_conj_of_commute (h : ElemNorm E d) {q : G} (hq : ∀ x ∈ E, q * x * q⁻¹ ∈ E)
    (hqd : ∀ x ∈ E, (d⁻¹ * q * d) * x * (d⁻¹ * q * d)⁻¹ = q * x * q⁻¹) :
    ∀ u ∈ dCom E d h, q * u * q⁻¹ ∈ dCom E d h := by
  rintro _ ⟨e, he, rfl⟩
  refine ⟨q * e * q⁻¹, hq e he, ?_⟩
  calc q * (e * (d * e * d⁻¹)) * q⁻¹
      = (q * e * q⁻¹) * (d * ((d⁻¹ * q * d) * e * (d⁻¹ * q * d)⁻¹) * d⁻¹) := by group
    _ = (q * e * q⁻¹) * (d * (q * e * q⁻¹) * d⁻¹) := by rw [hqd e he]

theorem dCom_conj_of_mem (h : ElemNorm E d) {t q' : G} (ht : ∀ x ∈ E, t * x * t⁻¹ ∈ E)
    (hq' : ∀ x ∈ E, q' * x * q'⁻¹ = x)
    (hd : t * d * t⁻¹ = d * q' ∨ t * d * t⁻¹ = d⁻¹ * q') :
    ∀ u ∈ dCom E d h, t * u * t⁻¹ ∈ dCom E d h := by
  rintro _ ⟨e, he, rfl⟩
  have he' : t * e * t⁻¹ ∈ E := ht e he
  have key : t * (e * (d * e * d⁻¹)) * t⁻¹ =
      (t * e * t⁻¹) * ((t * d * t⁻¹) * (t * e * t⁻¹) * (t * d * t⁻¹)⁻¹) := by group
  rw [key]
  rcases hd with hd | hd
  · refine ⟨t * e * t⁻¹, he', ?_⟩
    rw [hd]
    have : (d * q') * (t * e * t⁻¹) * (d * q')⁻¹ =
        d * (q' * (t * e * t⁻¹) * q'⁻¹) * d⁻¹ := by group
    rw [this, hq' _ he']
  · have ha : d⁻¹ * (t * e * t⁻¹) * d ∈ E := h.norm_inv he'
    refine ⟨d⁻¹ * (t * e * t⁻¹) * d, ha, ?_⟩
    rw [hd]
    have e1 : (d⁻¹ * q') * (t * e * t⁻¹) * (d⁻¹ * q')⁻¹ =
        d⁻¹ * (q' * (t * e * t⁻¹) * q'⁻¹) * d := by group
    have e2 : d * (d⁻¹ * (t * e * t⁻¹) * d) * d⁻¹ = t * e * t⁻¹ := by group
    rw [e1, hq' _ he', e2]
    exact h.comm _ he' _ ha

end F53.Stellmacher.S42Gt

end CFSG.Quasithin
