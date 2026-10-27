module

public import CFSG.Quasithin.H13.GoldschmidtU43BPhi2
public import CFSG.Quasithin.H13.GoldschmidtU43Swap

public section

namespace CFSG.Quasithin.H13.U43

open CFSG.Quasithin CFSG.Open CFSG.Quasithin.H13.A5.Orth CFSG.Quasithin.H13.A6

variable {G : Type} [Group G]

theorem z_comm_H {z : G} (x : ↥(Hz z)) : (x : G) * z = z * (x : G) :=
  Subgroup.mem_centralizer_singleton_iff.mp x.2

namespace Hyp

variable {z : G} (h : Hyp z)

@[expose] noncomputable def tv (u : ↥(Uz z)) : V4 := Multiplicative.toAdd (h.θ u)

theorem tv_mul (u v : ↥(Uz z)) : h.tv (u * v) = h.tv u + h.tv v := by
  unfold tv
  rw [map_mul, toAdd_mul]

theorem tv_one : h.tv 1 = 0 := by
  unfold tv
  rw [map_one, toAdd_one]

theorem tv_conj (x : ↥(Hz z)) (u : ↥(Uz z)) : h.tv (conjU x u) = vapp (h.act x) (h.tv u) := by
  unfold tv vapp
  rw [ofAdd_toAdd, h.act_θ]

theorem tv_eq_zero_iff (u : ↥(Uz z)) : h.tv u = 0 ↔ (u : G) = 1 ∨ (u : G) = z := by
  rw [← h.θ_eq_one_iff]
  unfold tv
  constructor
  · intro e
    exact Multiplicative.toAdd.injective (by simpa using e)
  · intro e
    rw [e]
    rfl

theorem eq_of_tv_eq {u v : ↥(Uz z)} (e : h.tv u = h.tv v) : (u : G) = v ∨ (u : G) = z * v := by
  exact h.eq_of_θ_eq u.2 v.2 (Multiplicative.toAdd.injective e)

theorem tv_surj (ξ : V4) : ∃ u : ↥(Uz z), h.tv u = ξ := by
  obtain ⟨u, hu⟩ := h.θ_surj (Multiplicative.ofAdd ξ)
  exact ⟨u, by unfold tv; rw [hu]; rfl⟩

theorem comm_tv (u v : ↥(Uz z)) :
    (u : G) * v * (u : G)⁻¹ * (v : G)⁻¹ = zp z (bq (h.tv u) (h.tv v)) :=
  h.comm_eq u v

theorem sq_tv (u : ↥(Uz z)) : (u : G) ^ 2 = zp z (q (h.tv u)) :=
  h.sq_eq u

@[expose] def zU : ↥(Uz z) := ⟨z, h.z_mem⟩

theorem tv_zU : h.tv h.zU = 0 := (h.tv_eq_zero_iff _).2 (Or.inr rfl)

theorem eq_of_tv_eq' {u v : ↥(Uz z)} (e : h.tv u = h.tv v) : u = v ∨ u = h.zU * v := by
  rcases h.eq_of_tv_eq e with h1 | h1
  · exact Or.inl (Subtype.ext h1)
  · exact Or.inr (Subtype.ext h1)

theorem conjU_zU (x : ↥(Hz z)) : conjU x h.zU = h.zU := by
  apply Subtype.ext
  rw [coe_conjU]
  show (x : G) * z * (x : G)⁻¹ = z
  calc (x : G) * z * (x : G)⁻¹ = (z * (x : G)) * (x : G)⁻¹ := by rw [z_comm_H x]
    _ = z := by group

theorem conjU_mul_right (x : ↥(Hz z)) (u v : ↥(Uz z)) :
    conjU x (u * v) = conjU x u * conjU x v := by
  apply Subtype.ext
  simp only [coe_conjU, Subgroup.coe_mul]
  group

theorem conjU_mul_left (x y : ↥(Hz z)) (u : ↥(Uz z)) : conjU (x * y) u = conjU x (conjU y u) := by
  apply Subtype.ext
  simp only [coe_conjU, Subgroup.coe_mul]
  group

theorem conjU_one (u : ↥(Uz z)) : conjU (1 : ↥(Hz z)) u = u := by
  apply Subtype.ext
  simp only [coe_conjU, OneMemClass.coe_one]
  group

end Hyp

end CFSG.Quasithin.H13.U43
