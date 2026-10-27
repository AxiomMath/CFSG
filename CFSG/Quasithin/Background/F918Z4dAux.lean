module

public import CFSG.Quasithin.Background.FixVZPowersMem
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.Quasithin

namespace Z4d

section Fix

variable {V : Type} [CommGroup V]

theorem mem_fixV_zpowers_iff {t : MulAut V} {v : V} :
    v ∈ fixV (Subgroup.zpowers t) ↔ t v = v :=
  CFSG.Quasithin.mem_fixV_zpowers_iff_apply

theorem mem_fixV_zpowers_of_comm {t g : MulAut V} (h : t * g = g * t) {v : V}
    (hv : v ∈ fixV (Subgroup.zpowers t)) : g v ∈ fixV (Subgroup.zpowers t) := by
  rw [mem_fixV_zpowers_iff] at hv ⊢
  calc t (g v) = (t * g) v := rfl
    _ = (g * t) v := by rw [h]
    _ = g v := by rw [MulAut.mul_apply, hv]

theorem mul_inv_mem_fixV_zpowers {t g : MulAut V} (hV : ∀ v : V, v ^ 2 = 1) (ht : t * t = 1)
    (hgt : t * g = g * t) (hg : ∀ v ∈ fixV (Subgroup.zpowers t), g v = v) (v : V) :
    g v * v⁻¹ ∈ fixV (Subgroup.zpowers t) := by
  rw [mem_fixV_zpowers_iff]
  have htt : ∀ w : V, t (t w) = w := fun w => by
    have := congrArg (fun f : MulAut V => f w) ht
    simpa using this
  have hn : v * t v ∈ fixV (Subgroup.zpowers t) := by
    rw [mem_fixV_zpowers_iff, map_mul, htt, mul_comm]
  have hgn : g (v * t v) = v * t v := hg _ hn
  have hgt' : t (g v) = g (t v) := by
    have := congrArg (fun f : MulAut V => f v) hgt
    simpa using this
  have hxy : (g v * v⁻¹) * (g (t v) * (t v)⁻¹) = 1 := by
    calc (g v * v⁻¹) * (g (t v) * (t v)⁻¹) = g (v * t v) * (v * t v)⁻¹ := by
          rw [map_mul, mul_inv]; ac_rfl
      _ = 1 := by rw [hgn, mul_inv_cancel]
  have hx2 : (g v * v⁻¹) * (g v * v⁻¹) = 1 := by
    have := hV (g v * v⁻¹)
    rwa [pow_two] at this
  rw [map_mul, map_inv, hgt']
  exact mul_left_cancel (hxy.trans hx2.symm)

theorem comm_of_fixing {t g h : MulAut V} (hV : ∀ v : V, v ^ 2 = 1) (ht : t * t = 1)
    (hgt : t * g = g * t) (hht : t * h = h * t)
    (hg : ∀ v ∈ fixV (Subgroup.zpowers t), g v = v)
    (hh : ∀ v ∈ fixV (Subgroup.zpowers t), h v = v) : g * h = h * g := by
  ext v
  have h1 : g (h v * v⁻¹) = h v * v⁻¹ := hg _ (mul_inv_mem_fixV_zpowers hV ht hht hh v)
  have h2 : h (g v * v⁻¹) = g v * v⁻¹ := hh _ (mul_inv_mem_fixV_zpowers hV ht hgt hg v)
  rw [map_mul, map_inv, mul_inv_eq_iff_eq_mul] at h1 h2
  show g (h v) = h (g v)
  rw [h1, h2]
  ac_rfl

end Fix

section Conj

variable {V : Type} [CommGroup V]

theorem map_conj_mul (D : Subgroup (MulAut V)) (g s : MulAut V) :
    D.map (MulAut.conj (g * s)).toMonoidHom =
      (D.map (MulAut.conj s).toMonoidHom).map (MulAut.conj g).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1

theorem map_conj_one (D : Subgroup (MulAut V)) :
    D.map (MulAut.conj (1 : MulAut V)).toMonoidHom = D := by
  ext x
  simp [Subgroup.mem_map]

end Conj

section Diag

variable {V : Type} [CommGroup V] {D X : Subgroup (MulAut V)} {t : MulAut V}

@[expose] def diagHom (D X : Subgroup (MulAut V)) (t : MulAut V)
    (hX : ∀ y ∈ D, t * y * t⁻¹ ∈ X) (hc : ∀ g ∈ D, ∀ x ∈ X, g * x = x * g) :
    ↥D →* MulAut V where
  toFun y := (y : MulAut V) * (t * (y : MulAut V) * t⁻¹)
  map_one' := by simp
  map_mul' y z := by
    have h := hc z z.2 (t * y * t⁻¹) (hX y y.2)
    have e1 : t * ((y : MulAut V) * (z : MulAut V)) * t⁻¹ =
        (t * (y : MulAut V) * t⁻¹) * (t * (z : MulAut V) * t⁻¹) := by group
    show (y : MulAut V) * z * (t * ((y : MulAut V) * z) * t⁻¹) = _
    rw [e1, mul_assoc (y : MulAut V) (z : MulAut V), ← mul_assoc (z : MulAut V), h]
    group

variable {hX : ∀ y ∈ D, t * y * t⁻¹ ∈ X} {hc : ∀ g ∈ D, ∀ x ∈ X, g * x = x * g}

theorem diagHom_apply (y : ↥D) :
    diagHom D X t hX hc y = (y : MulAut V) * (t * (y : MulAut V) * t⁻¹) := rfl

theorem diagHom_comm (ht : t * t = 1) (y : ↥D) :
    t * diagHom D X t hX hc y = diagHom D X t hX hc y * t := by
  have h := hc y y.2 (t * y * t⁻¹) (hX y y.2)
  have h1 : t * (t * (y : MulAut V) * t⁻¹) * t⁻¹ = (y : MulAut V) := by
    have : t * (t * (y : MulAut V) * t⁻¹) * t⁻¹ = (t * t) * y * (t * t)⁻¹ := by group
    rw [this, ht]
    simp
  have h2 : t * diagHom D X t hX hc y * t⁻¹ = diagHom D X t hX hc y := by
    rw [diagHom_apply]
    calc t * ((y : MulAut V) * (t * (y : MulAut V) * t⁻¹)) * t⁻¹
        = (t * (y : MulAut V) * t⁻¹) * (t * (t * (y : MulAut V) * t⁻¹) * t⁻¹) := by group
      _ = (t * (y : MulAut V) * t⁻¹) * (y : MulAut V) := by rw [h1]
      _ = (y : MulAut V) * (t * (y : MulAut V) * t⁻¹) := h.symm
  calc t * diagHom D X t hX hc y = t * diagHom D X t hX hc y * t⁻¹ * t := by group
    _ = diagHom D X t hX hc y * t := by rw [h2]

theorem diagHom_conj (a : MulAut V) (hat : a * t = t * a) (haD : ∀ y ∈ D, a * y * a⁻¹ ∈ D)
    (y : ↥D) :
    diagHom D X t hX hc ⟨a * y * a⁻¹, haD y y.2⟩ = a * diagHom D X t hX hc y * a⁻¹ := by
  have h1 : a * t * a⁻¹ = t := by rw [mul_inv_eq_iff_eq_mul]; exact hat
  have h2 : a * (t * (y : MulAut V) * t⁻¹) * a⁻¹ = t * (a * y * a⁻¹) * t⁻¹ := by
    calc a * (t * (y : MulAut V) * t⁻¹) * a⁻¹
        = (a * t * a⁻¹) * (a * y * a⁻¹) * (a * t * a⁻¹)⁻¹ := by group
      _ = t * (a * y * a⁻¹) * t⁻¹ := by rw [h1]
  rw [diagHom_apply, diagHom_apply]
  calc (a * (y : MulAut V) * a⁻¹) * (t * (a * (y : MulAut V) * a⁻¹) * t⁻¹)
      = (a * (y : MulAut V) * a⁻¹) * (a * (t * (y : MulAut V) * t⁻¹) * a⁻¹) := by rw [h2]
    _ = a * ((y : MulAut V) * (t * (y : MulAut V) * t⁻¹)) * a⁻¹ := by group

theorem diagHom_injective [IsSimpleGroup ↥D]
    (hnonab : ∃ a ∈ D, ∃ b ∈ D, a * b ≠ b * a) :
    Function.Injective (diagHom D X t hX hc) := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (diagHom D X t hX hc).ker with h | h
  · exact (MonoidHom.ker_eq_bot_iff _).1 h
  · exfalso
    obtain ⟨a, ha, b, hb, hab⟩ := hnonab
    have hDX : ∀ y ∈ D, y ∈ X := by
      intro y hy
      have h1 : diagHom D X t hX hc ⟨y, hy⟩ = 1 := by
        have : (⟨y, hy⟩ : ↥D) ∈ (diagHom D X t hX hc).ker := by rw [h]; trivial
        exact this
      have h2 : y * (t * y * t⁻¹) = 1 := h1
      rw [eq_inv_of_mul_eq_one_left h2]
      exact X.inv_mem (hX y hy)
    exact hab (hc a ha b (hDX b hb))

end Diag

end Z4d

end CFSG.Quasithin
