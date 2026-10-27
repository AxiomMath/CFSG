module

public import CFSG.Quasithin.EmptyFaithful.S153PDef

public section

namespace CFSG.Quasithin

namespace S153P

namespace PB

variable {G : Type} [Group G] {z zp u₀ u₀' : G}

theorem z_mul_zzp (hP : Pts z zp u₀ u₀') : z * (z * zp) = zp := by
  rw [← mul_assoc, hP.z_sq, one_mul]

theorem zp_mul_zzp (hP : Pts z zp u₀ u₀') : zp * (z * zp) = z := by
  rw [← mul_assoc, ← hP.comm, mul_assoc, hP.zp_sq, mul_one]

theorem zzp_mul_z (hP : Pts z zp u₀ u₀') : z * zp * z = zp := by
  rw [mul_assoc, ← hP.comm, ← mul_assoc, hP.z_sq, one_mul]

theorem zzp_mul_zp (hP : Pts z zp u₀ u₀') : z * zp * zp = z := by
  rw [mul_assoc, hP.zp_sq, mul_one]

theorem zzp_mul_zzp (hP : Pts z zp u₀ u₀') : z * zp * (z * zp) = 1 := by
  rw [mul_assoc, zp_mul_zzp hP, hP.z_sq]

theorem z_inv (hP : Pts z zp u₀ u₀') : z⁻¹ = z := inv_eq_of_mul_eq_one_right hP.z_sq

theorem zp_inv (hP : Pts z zp u₀ u₀') : zp⁻¹ = zp := inv_eq_of_mul_eq_one_right hP.zp_sq

theorem conj_mul (g a b : G) : g * (a * b) * g⁻¹ = g * a * g⁻¹ * (g * b * g⁻¹) := by
  group

def V4 (hP : Pts z zp u₀ u₀') : Subgroup G where
  carrier := {x | x = 1 ∨ x = z ∨ x = zp ∨ x = z * zp}
  one_mem' := Or.inl rfl
  mul_mem' := by
    intro a b ha hb
    change a = 1 ∨ a = z ∨ a = zp ∨ a = z * zp at ha
    change b = 1 ∨ b = z ∨ b = zp ∨ b = z * zp at hb
    change a * b = 1 ∨ a * b = z ∨ a * b = zp ∨ a * b = z * zp
    rcases ha with ha | ha | ha | ha <;> rcases hb with hb | hb | hb | hb <;>
      simp [ha, hb, hP.z_sq, hP.zp_sq, z_mul_zzp hP, zp_mul_zzp hP, zzp_mul_z hP, zzp_mul_zp hP,
        zzp_mul_zzp hP, ← hP.comm]
  inv_mem' := by
    intro a ha
    change a = 1 ∨ a = z ∨ a = zp ∨ a = z * zp at ha
    change a⁻¹ = 1 ∨ a⁻¹ = z ∨ a⁻¹ = zp ∨ a⁻¹ = z * zp
    rcases ha with ha | ha | ha | ha <;>
      simp [ha, z_inv hP, zp_inv hP, mul_inv_rev, ← hP.comm]

theorem mem_V4 (hP : Pts z zp u₀ u₀') {x : G} :
    x ∈ V4 hP ↔ x = 1 ∨ x = z ∨ x = zp ∨ x = z * zp := Iff.rfl

theorem mem_z : z ∈ V0of z zp :=
  Subgroup.mem_sup_left (Subgroup.mem_zpowers z)

theorem mem_zp : zp ∈ V0of z zp :=
  Subgroup.mem_sup_right (Subgroup.mem_zpowers zp)

theorem mem_zzp : z * zp ∈ V0of z zp :=
  mul_mem mem_z mem_zp

theorem mem_V0of (hP : Pts z zp u₀ u₀') {x : G} :
    x ∈ V0of z zp ↔ x = 1 ∨ x = z ∨ x = zp ∨ x = z * zp := by
  constructor
  · intro hx
    have hle : V0of z zp ≤ V4 hP :=
      sup_le (Subgroup.zpowers_le.2 ((mem_V4 hP).2 (Or.inr (Or.inl rfl))))
        (Subgroup.zpowers_le.2 ((mem_V4 hP).2 (Or.inr (Or.inr (Or.inl rfl)))))
    exact (mem_V4 hP).1 (hle hx)
  · rintro (hx | hx | hx | hx) <;> rw [hx]
    · exact one_mem _
    · exact mem_z
    · exact mem_zp
    · exact mem_zzp

theorem mem_centralizer_V0 (hP : Pts z zp u₀ u₀') {g : G} :
    g ∈ Subgroup.centralizer ((V0of z zp : Subgroup G) : Set G) ↔
      g * z * g⁻¹ = z ∧ g * zp * g⁻¹ = zp := by
  rw [Subgroup.mem_centralizer_iff]
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · rw [← h z mem_z, mul_inv_cancel_right]
    · rw [← h zp mem_zp, mul_inv_cancel_right]
  · rintro ⟨h1, h2⟩ x hx
    have e1 : Commute z g := (mul_inv_eq_iff_eq_mul.1 h1).symm
    have e2 : Commute zp g := (mul_inv_eq_iff_eq_mul.1 h2).symm
    rcases (mem_V0of hP).1 hx with hx | hx | hx | hx <;> rw [hx]
    · rw [one_mul, mul_one]
    · exact e1
    · exact e2
    · exact e1.mul_left e2

theorem mem_normalizer_V0 (hP : Pts z zp u₀ u₀') {g : G}
    (h1 : g * z * g⁻¹ ∈ V0of z zp) (h2 : g * zp * g⁻¹ ∈ V0of z zp) :
    g ∈ Subgroup.normalizer ((V0of z zp : Subgroup G) : Set G) := by
  have hmaps : ∀ x ∈ V0of z zp, g * x * g⁻¹ ∈ V0of z zp := by
    intro x hx
    rcases (mem_V0of hP).1 hx with hx | hx | hx | hx <;> rw [hx]
    · simp only [mul_one, mul_inv_cancel]
      exact one_mem _
    · exact h1
    · exact h2
    · rw [conj_mul]
      exact mul_mem h1 h2
  have hfin : ((V0of z zp : Subgroup G) : Set G).Finite := by
    have hsub : ((V0of z zp : Subgroup G) : Set G) ⊆ {1, z, zp, z * zp} := by
      intro x hx
      simpa using (mem_V0of hP).1 hx
    exact (Set.toFinite _).subset hsub
  have hinj : Set.InjOn (fun x => g * x * g⁻¹) ((V0of z zp : Subgroup G) : Set G) := by
    intro a _ b _ hab
    simpa using hab
  have hbij := (hfin.injOn_iff_bijOn_of_mapsTo hmaps).1 hinj
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨hmaps x, fun hx => ?_⟩
  obtain ⟨y, hy, hyx⟩ := hbij.surjOn hx
  have hyx' : y = x := by simpa using hyx
  rw [← hyx']
  exact hy

end PB

section Facts

variable {G : Type} [Group G]

theorem Pts.u₀_not_cent {z zp u₀ u₀' : G} (hP : Pts z zp u₀ u₀') :
    u₀ ∉ Subgroup.centralizer ((V0of z zp : Subgroup G) : Set G) := by
  intro hc
  have h2 := ((PB.mem_centralizer_V0 hP).1 hc).2
  rw [hP.u₀_zp] at h2
  exact hP.z_ne_one (by simpa using h2)

theorem Pts.u₀_sq_cent {z zp u₀ u₀' : G} (hP : Pts z zp u₀ u₀') :
    u₀ * u₀ ∈ Subgroup.centralizer ((V0of z zp : Subgroup G) : Set G) := by
  have e : ∀ x : G, u₀ * u₀ * x * (u₀ * u₀)⁻¹ = u₀ * (u₀ * x * u₀⁻¹) * u₀⁻¹ := by
    intro x
    group
  rw [PB.mem_centralizer_V0 hP]
  refine ⟨?_, ?_⟩
  · rw [e, hP.u₀_z, hP.u₀_z]
  · rw [e, hP.u₀_zp, PB.conj_mul, hP.u₀_z, hP.u₀_zp, PB.z_mul_zzp hP]

theorem Pts.j_not_cent {z zp u₀ u₀' : G} (hP : Pts z zp u₀ u₀') :
    (u₀' * u₀) ∉ Subgroup.centralizer ((V0of z zp : Subgroup G) : Set G) := by
  intro hc
  have h2 := ((PB.mem_centralizer_V0 hP).1 hc).2
  have e : u₀' * u₀ * zp * (u₀' * u₀)⁻¹ = u₀' * (u₀ * zp * u₀⁻¹) * u₀'⁻¹ := by
    group
  rw [e, hP.u₀_zp, PB.conj_mul, hP.u₀'_z, hP.u₀'_zp, PB.zzp_mul_zp hP] at h2
  exact hP.z_ne_zp h2

theorem Pts.j_cube_cent {z zp u₀ u₀' : G} (hP : Pts z zp u₀ u₀') :
    (u₀' * u₀) ^ 3 ∈ Subgroup.centralizer ((V0of z zp : Subgroup G) : Set G) := by
  have hz : u₀' * u₀ * z * (u₀' * u₀)⁻¹ = z * zp := by
    have e : u₀' * u₀ * z * (u₀' * u₀)⁻¹ = u₀' * (u₀ * z * u₀⁻¹) * u₀'⁻¹ := by
      group
    rw [e, hP.u₀_z, hP.u₀'_z]
  have hzp : u₀' * u₀ * zp * (u₀' * u₀)⁻¹ = z := by
    have e : u₀' * u₀ * zp * (u₀' * u₀)⁻¹ = u₀' * (u₀ * zp * u₀⁻¹) * u₀'⁻¹ := by
      group
    rw [e, hP.u₀_zp, PB.conj_mul, hP.u₀'_z, hP.u₀'_zp, PB.zzp_mul_zp hP]
  have hzzp : u₀' * u₀ * (z * zp) * (u₀' * u₀)⁻¹ = zp := by
    rw [PB.conj_mul, hz, hzp, PB.zzp_mul_z hP]
  have e : ∀ x : G, (u₀' * u₀) ^ 3 * x * ((u₀' * u₀) ^ 3)⁻¹ =
      (u₀' * u₀) * ((u₀' * u₀) * ((u₀' * u₀) * x * (u₀' * u₀)⁻¹) * (u₀' * u₀)⁻¹) * (u₀' * u₀)⁻¹ := by
    intro x
    rw [pow_three']
    group
  rw [PB.mem_centralizer_V0 hP]
  refine ⟨?_, ?_⟩
  · rw [e, hz, hzzp, hzp]
  · rw [e, hzp, hz, hzzp]

end Facts

end S153P

end CFSG.Quasithin
