module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec7P72Key

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph

namespace P72

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}
variable {F : FanTree Γ G} {L : ZLab Γ G}

theorem pair_eq {l x4 : V} (hl : valence Γ l = 5) (hx4 : valence Γ x4 = 5) :
    L.z l * L.z (L.z x4 • l) = L.z (L.z l • x4) * L.z x4 := by
  rw [L.equivariant (L.z x4) l hl, L.equivariant (L.z l) x4 hx4, L.z_inv hl, L.z_inv hx4]
  simp only [mul_assoc]

theorem v_cases (h : Fan71c F L) (hlab : Lab3 F L) {α ν₁ ν₂ l₁ l₂ x1 x2 x3 x4 : V}
    (hα : valence Γ α = 5) (A : Arc4 Γ α x1 x2 x3 x4) (b₁ : Br Γ α ν₁ l₁) (b₂ : Br Γ α ν₂ l₂)
    (h1 : ν₁ ≠ x1) (h2 : ν₂ ≠ x1) :
    L.z l₁ * L.z (L.z x4 • l₁) * L.z l₂ * L.z (L.z x4 • l₂) = 1 ∨
      L.z l₁ * L.z (L.z x4 • l₁) * L.z l₂ * L.z (L.z x4 • l₂) = L.z x2 := by
  obtain ⟨vx1, vx2, vx3, vx4⟩ := val_arc4 F A.a01 A.a12 A.a23 A.a34 hα
  have hl1 := (b₁.valence F hα).2
  have hl2 := (b₂.valence F hα).2
  obtain ⟨he, hne, hadj⟩ := x3_eq h hα b₁ b₂ A h1 h2
  obtain ⟨m1a, m1n, m1v, m1d⟩ := mu_facts h hα b₁ A h1 rfl hne hadj
  obtain ⟨m2a, m2n, m2v, m2d⟩ := mu_facts h hα b₂ A h2 he hne hadj
  have e1 := pair_eq (L := L) hl1 vx4
  have e2 := pair_eq (L := L) hl2 vx4
  have hc2 : L.z (L.z l₂ • x4) * L.z x4 = L.z x4 * L.z (L.z l₂ • x4) :=
    Fan71c.z_comm_of_dist_le h m2v vx4 (by rw [SimpleGraph.dist_comm]; omega)
  have hv : L.z l₁ * L.z (L.z x4 • l₁) * L.z l₂ * L.z (L.z x4 • l₂) =
      L.z (L.z l₁ • x4) * L.z (L.z l₂ • x4) := by
    have hss := L.z_mul_self vx4
    calc L.z l₁ * L.z (L.z x4 • l₁) * L.z l₂ * L.z (L.z x4 • l₂)
        = (L.z l₁ * L.z (L.z x4 • l₁)) * (L.z l₂ * L.z (L.z x4 • l₂)) := by simp only [mul_assoc]
      _ = (L.z (L.z l₁ • x4) * L.z x4) * (L.z (L.z l₂ • x4) * L.z x4) := by rw [e1, e2]
      _ = L.z (L.z l₁ • x4) * ((L.z x4 * L.z (L.z l₂ • x4)) * L.z x4) := by simp only [mul_assoc]
      _ = L.z (L.z l₁ • x4) * L.z (L.z l₂ • x4) := by
        rw [← hc2, mul_assoc (L.z (L.z l₂ • x4)), hss, mul_one]
  rw [hv]
  by_cases hm : L.z l₁ • x4 = L.z l₂ • x4
  · left
    rw [hm]
    exact L.z_mul_self m2v
  · right
    have hx3v : valence Γ (L.z l₁ • x3) = 3 := by rw [valence_smul F]; exact vx3
    have hset := nbrSet_eq_three hx3v hadj.symm m1a m2a (fun hh => m1n hh.symm)
      (fun hh => m2n hh.symm) hm
    have h3 := hlab (L.z l₁ • x3) x2 _ _ hx3v hset (fun hh => m1n hh.symm)
      (fun hh => m2n hh.symm) hm
    have h4 : L.z (L.z l₁ • x4) * L.z (L.z l₂ • x4) = (L.z x2)⁻¹ := by
      apply eq_inv_of_mul_eq_one_right
      rw [← mul_assoc]
      exact h3
    rw [h4, L.z_inv vx2]

end P72

end CFSG.Quasithin.Fan86
