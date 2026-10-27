module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec7P72Key2

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph

namespace P72

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}
variable {F : FanTree Γ G} {L : ZLab Γ G}

theorem br_smul_s (h : Fan71c F L) {α ν l x1 x2 x3 x4 : V} (hα : valence Γ α = 5)
    (A : Arc4 Γ α x1 x2 x3 x4) (b : Br Γ α ν l) : Br Γ α (L.z x4 • ν) (L.z x4 • l) := by
  obtain ⟨sα, -, -⟩ := s_facts h A.a01 A.a12 A.a23 A.a34 A.n02 A.n13 A.n24 hα
  refine ⟨?_, (F.adj_smul _ _ _).2 b.a2, fun hh =>
    b.ne (MulAction.injective (L.z x4) (hh.trans sα.symm))⟩
  have := (F.adj_smul (L.z x4) α ν).2 b.a1
  rwa [sα] at this

theorem v_ne_one (h : Fan71c F L) {α ν₁ ν₂ l₁ l₂ x1 x2 x3 x4 : V} (hα : valence Γ α = 5)
    (A : Arc4 Γ α x1 x2 x3 x4) (b₁ : Br Γ α ν₁ l₁) (b₂ : Br Γ α ν₂ l₂) (h1 : ν₁ ≠ x1)
    (h12 : ν₁ ≠ ν₂) (h2s : ν₂ ≠ L.z x4 • ν₁) :
    L.z l₁ * L.z (L.z x4 • l₁) * L.z l₂ * L.z (L.z x4 • l₂) ≠ 1 := by
  obtain ⟨-, -, -, vx4⟩ := val_arc4 F A.a01 A.a12 A.a23 A.a34 hα
  have hl1 := (b₁.valence F hα).2
  have hl2 := (b₂.valence F hα).2
  obtain ⟨-, -, smove⟩ := s_facts h A.a01 A.a12 A.a23 A.a34 A.n02 A.n13 A.n24 hα
  have bs1 := br_smul_s h hα A b₁
  have bs2 := br_smul_s h hα A b₂
  have hsl1 : valence Γ (L.z x4 • l₁) = 5 := by rw [valence_smul F]; exact hl1
  have hsl2 : valence Γ (L.z x4 • l₂) = 5 := by rw [valence_smul F]; exact hl2
  have hsn1 : L.z x4 • ν₁ ≠ ν₁ := smove ν₁ b₁.a1 h1.symm
  have hsn2 : L.z x4 • ν₂ ≠ ν₁ := fun hh => h2s (by
    rw [← hh, smul_smul, L.z_mul_self vx4, one_smul])
  obtain ⟨x1a, x1b⟩ := dist_branch F.isTree bs1.a1 bs1.a2 bs1.ne b₁.a1 b₁.a2 b₁.ne hsn1
  obtain ⟨x2a, x2b⟩ := dist_branch F.isTree b₂.a1 b₂.a2 b₂.ne b₁.a1 b₁.a2 b₁.ne h12.symm
  obtain ⟨x3a, x3b⟩ := dist_branch F.isTree bs2.a1 bs2.a2 bs2.ne b₁.a1 b₁.a2 b₁.ne hsn2
  obtain ⟨w, hw, hwn⟩ := F.exists_adj_ne l₁ ν₁
  have d1 : Γ.dist (L.z x4 • l₁) w = 5 := by
    have := IsTree.dist_succ_of_ne F.isTree (w := L.z x4 • l₁) b₁.a2.symm hw hwn.symm (by omega)
    omega
  have d2 : Γ.dist l₂ w = 5 := by
    have := IsTree.dist_succ_of_ne F.isTree (w := l₂) b₁.a2.symm hw hwn.symm (by omega)
    omega
  have d3 : Γ.dist (L.z x4 • l₂) w = 5 := by
    have := IsTree.dist_succ_of_ne F.isTree (w := L.z x4 • l₂) b₁.a2.symm hw hwn.symm (by omega)
    omega
  have hK : L.z (L.z x4 • l₁) * L.z l₂ ∈ nbrStab Γ G l₁ :=
    mul_mem_nbrStab h b₁.a2.symm hsl1 hl2 (by omega) (by omega) (by omega) (by omega) hw
      (by omega) hw (by omega)
  have hz1 : L.z l₁ ∈ nbrStab Γ G l₁ :=
    z_mem_nbrStab h hl1 (by rw [SimpleGraph.dist_self]; omega)
  have hzn : L.z (L.z x4 • l₂) ∉ nbrStab Γ G l₁ := z_not_mem_nbrStab h hsl2 hw (by omega)
  intro hv1
  have hv2 : (L.z l₁ * (L.z (L.z x4 • l₁) * L.z l₂)) * L.z (L.z x4 • l₂) = 1 := by
    simpa only [mul_assoc] using hv1
  have hD := eq_inv_of_mul_eq_one_right hv2
  rw [hD] at hzn
  exact hzn (inv_mem (mul_mem hz1 hK))

theorem key (h : Fan71c F L) (hlab : Lab3 F L) {α ν₁ ν₂ l₁ l₂ x1 x2 x3 x4 : V}
    (hα : valence Γ α = 5) (A : Arc4 Γ α x1 x2 x3 x4) (b₁ : Br Γ α ν₁ l₁) (b₂ : Br Γ α ν₂ l₂)
    (h1 : ν₁ ≠ x1) (h2 : ν₂ ≠ x1) (h12 : ν₁ ≠ ν₂) (h2s : ν₂ ≠ L.z x4 • ν₁) :
    L.z l₁ * L.z (L.z x4 • l₁) * L.z l₂ * L.z (L.z x4 • l₂) = L.z x2 :=
  (v_cases h hlab hα A b₁ b₂ h1 h2).resolve_left (v_ne_one h hα A b₁ b₂ h1 h12 h2s)

end P72

end CFSG.Quasithin.Fan86
