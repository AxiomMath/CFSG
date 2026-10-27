module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3SFano

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL

namespace F6

namespace GoldAmL3

structure Walk4 {D : Type*} [Group D] (A B : Subgroup D) (s₀ s₁ s₂ s₃ s₄ : CosetGeom (A ⊔ B) A B) :
    Prop where
  type_one : vtype s₀ = true
  adj01 : (graph (A ⊔ B) A B).Adj s₀ s₁
  adj12 : (graph (A ⊔ B) A B).Adj s₁ s₂
  adj23 : (graph (A ⊔ B) A B).Adj s₂ s₃
  adj34 : (graph (A ⊔ B) A B).Adj s₃ s₄
  ne02 : s₀ ≠ s₂
  ne13 : s₁ ≠ s₃
  ne24 : s₂ ≠ s₄

variable {D : Type*} [Group D] [Finite D] {A B : Subgroup D} {z : D} {V : Subgroup D}

namespace GoldHyp3

variable (h : GoldHyp3 A B z V)

include h

theorem exists_mem_smul_eq {w u x x' : CosetGeom (A ⊔ B) A B}
    (hu : (graph (A ⊔ B) A B).Adj w u) (hx : (graph (A ⊔ B) A B).Adj w x)
    (hx' : (graph (A ⊔ B) A B).Adj w x') (hux : u ≠ x) (hux' : u ≠ x') {H : Subgroup D}
    (hHw : H ≤ stab w) (hHu : H ≤ stab u) (hH : ¬ H ≤ ballStab 1 w) :
    ∃ k : ↥(A ⊔ B), (k : D) ∈ H ∧ k • x = x' := by
  by_cases hxx' : x = x'
  · exact ⟨1, H.one_mem, by simp [hxx']⟩
  · exact h.exists_smul_of_not_le hu hx hx' hux hux' hxx' hHw hHu hH

end GoldHyp3

theorem Walk4.exists_smul (h : GoldHyp3 A B z V)
    (hF : ∀ s₁ s₂ s₃ : CosetGeom (A ⊔ B) A B, vtype s₂ = true →
      (graph (A ⊔ B) A B).Adj s₁ s₂ → (graph (A ⊔ B) A B).Adj s₂ s₃ → s₁ ≠ s₃ →
        ¬ ballStab 1 s₁ ⊓ ballStab 1 s₂ ≤ ballStab 1 s₃)
    {s₀ s₁ s₂ s₃ s₄ t₀ t₁ t₂ t₃ t₄ : CosetGeom (A ⊔ B) A B}
    (hs : Walk4 A B s₀ s₁ s₂ s₃ s₄) (ht : Walk4 A B t₀ t₁ t₂ t₃ t₄) :
    ∃ g : ↥(A ⊔ B), g • s₀ = t₀ ∧ g • s₁ = t₁ ∧ g • s₂ = t₂ ∧ g • s₃ = t₃ ∧ g • s₄ = t₄ := by
  have ht1 : vtype t₁ = false := vtype_eq_false_of_adj ht.adj01 ht.type_one
  have ht2 : vtype t₂ = true := vtype_eq_true_of_adj ht.adj12 ht1
  have hd01 : CosetGeom.dist t₁ t₀ ≤ 1 := (dist_eq_one_iff_adj.mpr ht.adj01.symm).le
  have hd12 : CosetGeom.dist t₁ t₂ ≤ 1 := (dist_eq_one_iff_adj.mpr ht.adj12).le
  have hd23 : CosetGeom.dist t₂ t₃ ≤ 1 := (dist_eq_one_iff_adj.mpr ht.adj23).le
  obtain ⟨a₀, ha₀⟩ := exists_smul_eq_γ₁ hs.type_one
  obtain ⟨b₀, hb₀⟩ := exists_smul_eq_γ₁ ht.type_one
  have hg₀ : (b₀ * a₀⁻¹) • s₀ = t₀ := by
    rw [ha₀, hb₀, ← mul_smul, mul_assoc, inv_mul_cancel, mul_one]
  have hadj1 : (graph (A ⊔ B) A B).Adj t₀ ((b₀ * a₀⁻¹) • s₁) := by
    have := (smul_adj (b₀ * a₀⁻¹)).mpr hs.adj01
    rwa [hg₀] at this
  obtain ⟨k₁, hk₁0, hk₁1⟩ := exists_stab_smul_eq hadj1 ht.adj01
  have hg₁0 : (k₁ * (b₀ * a₀⁻¹)) • s₀ = t₀ := by rw [mul_smul, hg₀, hk₁0]
  have hg₁1 : (k₁ * (b₀ * a₀⁻¹)) • s₁ = t₁ := by rw [mul_smul, hk₁1]
  generalize k₁ * (b₀ * a₀⁻¹) = g₁ at hg₁0 hg₁1
  have hx2 : (graph (A ⊔ B) A B).Adj t₁ (g₁ • s₂) := by
    have := (smul_adj g₁).mpr hs.adj12
    rwa [hg₁1] at this
  have hu2 : t₀ ≠ g₁ • s₂ := fun e => hs.ne02 (smul_left_cancel g₁ (hg₁0.trans e))
  obtain ⟨k₂, hk₂H, hk₂⟩ := h.exists_mem_smul_eq ht.adj01.symm hx2 ht.adj12 hu2 ht.ne02
    (H := stab t₁ ⊓ stab t₀) inf_le_left inf_le_right
    (h.not_stab_inf_le_ballStab_one ht.adj01.symm ht1)
  have hk₂1 : k₂ • t₁ = t₁ := smul_eq_of_mem_stab hk₂H.1
  have hk₂0 : k₂ • t₀ = t₀ := smul_eq_of_mem_stab hk₂H.2
  have hg₂0 : (k₂ * g₁) • s₀ = t₀ := by rw [mul_smul, hg₁0, hk₂0]
  have hg₂1 : (k₂ * g₁) • s₁ = t₁ := by rw [mul_smul, hg₁1, hk₂1]
  have hg₂2 : (k₂ * g₁) • s₂ = t₂ := by rw [mul_smul, hk₂]
  generalize k₂ * g₁ = g₂ at hg₂0 hg₂1 hg₂2
  have hx3 : (graph (A ⊔ B) A B).Adj t₂ (g₂ • s₃) := by
    have := (smul_adj g₂).mpr hs.adj23
    rwa [hg₂2] at this
  have hu3 : t₁ ≠ g₂ • s₃ := fun e => hs.ne13 (smul_left_cancel g₂ (hg₂1.trans e))
  obtain ⟨k₃, hk₃H, hk₃⟩ := h.exists_mem_smul_eq ht.adj12.symm hx3 ht.adj23 hu3 ht.ne13
    (H := ballStab 1 t₁) (ballStab_le_stab_of_dist_le (n := 1) hd12) (ballStab_le_stab 1 _)
    (h.not_ballStab_le_of_left ht.adj12 ht1)
  have hk₃0 : k₃ • t₀ = t₀ := smul_eq_of_mem_stab (ballStab_le_stab_of_dist_le (n := 1) hd01 hk₃H)
  have hk₃1 : k₃ • t₁ = t₁ := smul_eq_of_mem_stab (ballStab_le_stab 1 _ hk₃H)
  have hk₃2 : k₃ • t₂ = t₂ := smul_eq_of_mem_stab (ballStab_le_stab_of_dist_le (n := 1) hd12 hk₃H)
  have hg₃0 : (k₃ * g₂) • s₀ = t₀ := by rw [mul_smul, hg₂0, hk₃0]
  have hg₃1 : (k₃ * g₂) • s₁ = t₁ := by rw [mul_smul, hg₂1, hk₃1]
  have hg₃2 : (k₃ * g₂) • s₂ = t₂ := by rw [mul_smul, hg₂2, hk₃2]
  have hg₃3 : (k₃ * g₂) • s₃ = t₃ := by rw [mul_smul, hk₃]
  generalize k₃ * g₂ = g₃ at hg₃0 hg₃1 hg₃2 hg₃3
  have hx4 : (graph (A ⊔ B) A B).Adj t₃ (g₃ • s₄) := by
    have := (smul_adj g₃).mpr hs.adj34
    rwa [hg₃3] at this
  have hu4 : t₂ ≠ g₃ • s₄ := fun e => hs.ne24 (smul_left_cancel g₃ (hg₃2.trans e))
  obtain ⟨k₄, hk₄H, hk₄⟩ := h.exists_mem_smul_eq ht.adj23.symm hx4 ht.adj34 hu4 ht.ne24
    (H := ballStab 1 t₁ ⊓ ballStab 1 t₂)
    ((inf_le_right : ballStab 1 t₁ ⊓ ballStab 1 t₂ ≤ ballStab 1 t₂).trans
      (ballStab_le_stab_of_dist_le (n := 1) hd23))
    (inf_le_right.trans (ballStab_le_stab 1 _))
    (hF t₁ t₂ t₃ ht2 ht.adj12 ht.adj23 ht.ne13)
  have hk₄0 : k₄ • t₀ = t₀ :=
    smul_eq_of_mem_stab (ballStab_le_stab_of_dist_le (n := 1) hd01 hk₄H.1)
  have hk₄1 : k₄ • t₁ = t₁ := smul_eq_of_mem_stab (ballStab_le_stab 1 _ hk₄H.1)
  have hk₄2 : k₄ • t₂ = t₂ := smul_eq_of_mem_stab (ballStab_le_stab_of_dist_le (n := 1) hd12 hk₄H.1)
  have hk₄3 : k₄ • t₃ = t₃ := smul_eq_of_mem_stab (ballStab_le_stab_of_dist_le (n := 1) hd23 hk₄H.2)
  exact ⟨k₄ * g₃, by rw [mul_smul, hg₃0, hk₄0], by rw [mul_smul, hg₃1, hk₄1],
    by rw [mul_smul, hg₃2, hk₄2], by rw [mul_smul, hg₃3, hk₄3], by rw [mul_smul, hk₄]⟩

theorem Walk4.exists_smul_of_card (h : GoldHyp3 A B z V) (hU : Nat.card (conjClosure V B) = 8)
    {s₀ s₁ s₂ s₃ s₄ t₀ t₁ t₂ t₃ t₄ : CosetGeom (A ⊔ B) A B}
    (hs : Walk4 A B s₀ s₁ s₂ s₃ s₄) (ht : Walk4 A B t₀ t₁ t₂ t₃ t₄) :
    ∃ g : ↥(A ⊔ B), g • s₀ = t₀ ∧ g • s₁ = t₁ ∧ g • s₂ = t₂ ∧ g • s₃ = t₃ ∧ g • s₄ = t₄ :=
  Walk4.exists_smul h (fun _ _ _ hs₂ h12 h23 n13 => h.not_ballStab_inf_le hU hs₂ h12 h23 n13) hs ht

end GoldAmL3

end F6

end CFSG.Quasithin
