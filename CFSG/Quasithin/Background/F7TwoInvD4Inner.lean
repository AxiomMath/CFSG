module

public import CFSG.Quasithin.Background.F7TwoInvD4Levi
public import CFSG.Quasithin.Background.F7TwoInvExcBasic

public section

namespace CFSG.Quasithin.F7Two

open CFSG.LocalAnalysis.EvenBN.TrialityD4 Subgroup

variable {X : Type*} [Group X] {q : ℕ} (d : TrialityD4Data X q)

theorem u_mul_w₀ : d.u * d.w₀ = d.w₀ * d.u := d.gen_mul_w₀ false

theorem v_mul_w₀ : d.v * d.w₀ = d.w₀ * d.v := d.gen_mul_w₀ true

theorem uv_mul_w₀ : d.u * d.v * d.w₀ = d.w₀ * (d.u * d.v) := by
  rw [mul_assoc, v_mul_w₀ d, ← mul_assoc, u_mul_w₀ d, mul_assoc]

theorem vu_mul_w₀ : d.v * d.u * d.w₀ = d.w₀ * (d.v * d.u) := by
  rw [mul_assoc, u_mul_w₀ d, ← mul_assoc, v_mul_w₀ d, mul_assoc]

theorem x₄_eq_conj (a : d.Γ) : d.x₄ a = MulAut.conj (d.u * d.v) (d.x₁ a) := by
  have h := d.u_conj_x₃_eq_x₄ a
  rw [← d.v_conj_x₁] at h
  rw [← h, MulAut.conj_apply]
  simp only [mul_inv_rev, d.u_inv, d.v_inv, mul_assoc]

theorem x₆_eq_conj (a : d.Γ₀) : d.x₆ a = MulAut.conj (d.v * d.u) (d.x₂ a) := by
  have h := d.v_conj_x₅ a
  rw [← d.u_conj_x₂] at h
  rw [← h, MulAut.conj_apply]
  simp only [mul_inv_rev, d.u_inv, d.v_inv, mul_assoc]

theorem comm_x₁_w₀ : d.x₁ 1 * d.w₀ * (d.x₁ 1)⁻¹ * d.w₀⁻¹ = d.x₁ 1 * (d.u * d.x₁ 1 * d.u⁻¹) := by
  have h := d.w₀_conj_x₁ 1
  calc d.x₁ 1 * d.w₀ * (d.x₁ 1)⁻¹ * d.w₀⁻¹ = d.x₁ 1 * (d.w₀ * d.x₁ 1 * d.w₀) := by
        simp only [d.x₁_inv, d.w₀_inv, mul_assoc]
    _ = d.x₁ 1 * (d.u * d.x₁ 1 * d.u⁻¹) := by rw [h, d.u_inv]

theorem comm_x₂_w₀ : d.x₂ 1 * d.w₀ * (d.x₂ 1)⁻¹ * d.w₀⁻¹ = d.x₂ 1 * (d.v * d.x₂ 1 * d.v⁻¹) := by
  have h := d.w₀_conj_x₂ 1
  calc d.x₂ 1 * d.w₀ * (d.x₂ 1)⁻¹ * d.w₀⁻¹ = d.x₂ 1 * (d.w₀ * d.x₂ 1 * d.w₀) := by
        simp only [d.x₂_inv, d.w₀_inv, mul_assoc]
    _ = d.x₂ 1 * (d.v * d.x₂ 1 * d.v⁻¹) := by rw [h, d.v_inv]

theorem w₀_mem_invXi_x₄ : d.w₀ ∈ invXiAut (MulAut.conj (d.x₄ 1)) := by
  rw [mem_invXiAut_conj_iff]
  have hfix : MulAut.conj (d.u * d.v) d.w₀ = d.w₀ := by
    rw [MulAut.conj_apply, uv_mul_w₀ d, mul_inv_cancel_right]
  have e : d.x₄ 1 * d.w₀ * (d.x₄ 1)⁻¹ * d.w₀⁻¹ =
      MulAut.conj (d.u * d.v) (d.x₁ 1 * (d.u * d.x₁ 1 * d.u⁻¹)) := by
    rw [← comm_x₁_w₀, map_mul, map_mul, map_mul, map_inv, map_inv, hfix, ← x₄_eq_conj d]
  rw [e]
  exact fun hP => not_isPGroup_x₁_mul_conj d
    ((isPGroup_zpowers_map_iff (MulAut.conj (d.u * d.v)).toMonoidHom
      (MulAut.conj (d.u * d.v)).injective _).1 hP)

theorem w₀_mem_invXi_x₆ : d.w₀ ∈ invXiAut (MulAut.conj (d.x₆ 1)) := by
  rw [mem_invXiAut_conj_iff]
  have hfix : MulAut.conj (d.v * d.u) d.w₀ = d.w₀ := by
    rw [MulAut.conj_apply, vu_mul_w₀ d, mul_inv_cancel_right]
  have e : d.x₆ 1 * d.w₀ * (d.x₆ 1)⁻¹ * d.w₀⁻¹ =
      MulAut.conj (d.v * d.u) (d.x₂ 1 * (d.v * d.x₂ 1 * d.v⁻¹)) := by
    rw [← comm_x₂_w₀, map_mul, map_mul, map_mul, map_inv, map_inv, hfix, ← x₆_eq_conj d]
  rw [e]
  exact fun hP => not_isPGroup_x₂_mul_conj d
    ((isPGroup_zpowers_map_iff (MulAut.conj (d.v * d.u)).toMonoidHom
      (MulAut.conj (d.v * d.u)).injective _).1 hP)

theorem S_le_of_root_groups {K : Subgroup X} (h₁ : ∀ a, d.x₁ a ∈ K) (h₂ : ∀ a, d.x₂ a ∈ K)
    (h₃ : ∀ a, d.x₃ a ∈ K) (h₄ : ∀ a, d.x₄ a ∈ K) (h₅ : ∀ a, d.x₅ a ∈ K)
    (h₆ : ∀ a, d.x₆ a ∈ K) : d.S ≤ K := by
  rw [TrialityD4Data.S, sixClosure, closure_le]
  rintro g (((((⟨a, rfl⟩ | ⟨a, rfl⟩) | ⟨a, rfl⟩) | ⟨a, rfl⟩) | ⟨a, rfl⟩) | ⟨a, rfl⟩)
  exacts [h₁ a, h₂ a, h₃ a, h₄ a, h₅ a, h₆ a]

theorem top_le_of_S_u_v {K : Subgroup X} (hS : d.S ≤ K) (hu : d.u ∈ K) (hv : d.v ∈ K) :
    K = ⊤ := by
  refine eq_top_iff.2 (d.sup_closure_eq_top ▸ sup_le hS ((closure_le K).2 ?_))
  rintro g (rfl | rfl)
  exacts [hu, hv]

theorem conj_mem {K : Subgroup X} {g y : X} (hg : g ∈ K) (hy : y ∈ K) :
    MulAut.conj g y ∈ K := by
  rw [MulAut.conj_apply]
  exact mul_mem (mul_mem hg hy) (inv_mem hg)

theorem conj_w₀_x₁ (a : d.Γ) : MulAut.conj d.w₀ (d.x₁ a) = MulAut.conj d.u (d.x₁ a) := by
  rw [MulAut.conj_apply, MulAut.conj_apply, d.w₀_inv, d.u_inv, d.w₀_conj_x₁]

theorem conj_w₀_x₂ (a : d.Γ₀) : MulAut.conj d.w₀ (d.x₂ a) = MulAut.conj d.v (d.x₂ a) := by
  rw [MulAut.conj_apply, MulAut.conj_apply, d.w₀_inv, d.v_inv, d.w₀_conj_x₂]

theorem conj_w₀_conj_u (y : X) :
    MulAut.conj d.w₀ (MulAut.conj d.u y) = MulAut.conj d.u (MulAut.conj d.w₀ y) := by
  rw [← MulAut.mul_apply, ← MulAut.mul_apply, ← map_mul, ← map_mul, u_mul_w₀ d]

theorem S_le_centralizer_x₆ : d.S ≤ Subgroup.centralizer {d.x₆ 1} := fun _ hs =>
  Subgroup.mem_centralizer_singleton_iff.2
    (Subgroup.mem_centralizer_iff.1 (d.S_le_centralizer_V hs) (d.x₆ 1) (d.x₆_mem_V 1)).symm

theorem U_sup_conj_le_S_sup_conj_w₀ {U : Subgroup X} (hU : U ≤ d.S) {g : X}
    (hg : ∀ y ∈ U, MulAut.conj g y = MulAut.conj d.w₀ y) :
    U ⊔ U.map (MulAut.conj g).toMonoidHom ≤ d.S ⊔ d.S.map (MulAut.conj d.w₀).toMonoidHom := by
  refine sup_le_sup hU ?_
  rintro _ ⟨y, hy, rfl⟩
  exact ⟨y, hU hy, (hg y hy).symm⟩

theorem S_sup_conj_w₀_eq_top : d.S ⊔ d.S.map (MulAut.conj d.w₀).toMonoidHom = ⊤ := by
  refine top_le_iff.1 (d.sup_closure_eq_top ▸ sup_le le_sup_left ?_)
  rw [closure_le]
  rintro g (rfl | rfl)
  · refine U_sup_conj_le_S_sup_conj_w₀ d d.U₁_le_S (g := d.u) ?_ (u_mem_U₁_sup_conj d)
    rintro _ ⟨a, rfl⟩
    exact (conj_w₀_x₁ d a).symm
  · refine U_sup_conj_le_S_sup_conj_w₀ d d.U₂_le_S (g := d.v) ?_ (v_mem_U₂_sup_conj d)
    rintro _ ⟨a, rfl⟩
    exact (conj_w₀_x₂ d a).symm

theorem invAutGen_conj_x₆ : InvAutGen X (MulAut.conj (d.x₆ 1)) :=
  invAutGen_conj_of_centralizing (S_le_centralizer_x₆ d) (w₀_mem_invXi_x₆ d)
    (S_sup_conj_w₀_eq_top d)

theorem u_x₄_u (a : d.Γ) : d.u * d.x₄ a * d.u = d.x₃ a := by
  simpa [d.u_inv] using d.u_conj_x₄_eq_x₃ a

theorem v_x₃_v (a : d.Γ) : d.v * d.x₃ a * d.v = d.x₁ a := by
  simpa [d.v_inv] using d.v_conj_x₃ a

theorem uvu_x₄ (a : d.Γ) : d.u * d.v * d.u * d.x₄ a * (d.u * d.v * d.u) = d.u * d.x₁ a * d.u := by
  calc d.u * d.v * d.u * d.x₄ a * (d.u * d.v * d.u)
      = d.u * (d.v * (d.u * d.x₄ a * d.u) * d.v) * d.u := by simp only [mul_assoc]
    _ = d.u * d.x₁ a * d.u := by rw [u_x₄_u d, v_x₃_v d]

theorem w₀_u_x₁_u (a : d.Γ) : d.w₀ * (d.u * d.x₁ a * d.u) * d.w₀ = d.x₁ a := by
  have h : d.w₀ * d.u = d.u * d.w₀ := (u_mul_w₀ d).symm
  have uu (y : X) : d.u * (d.u * y) = y := by rw [← mul_assoc, d.u_mul_self, one_mul]
  calc d.w₀ * (d.u * d.x₁ a * d.u) * d.w₀ = (d.w₀ * d.u) * d.x₁ a * (d.u * d.w₀) := by
        simp only [mul_assoc]
    _ = (d.u * d.w₀) * d.x₁ a * (d.w₀ * d.u) := by rw [h]
    _ = d.u * (d.w₀ * d.x₁ a * d.w₀) * d.u := by simp only [mul_assoc]
    _ = d.x₁ a := by
      rw [d.w₀_conj_x₁]
      simp only [mul_assoc, d.u_mul_self, mul_one, uu]

theorem invAutGen_conj_x₄ : InvAutGen X (MulAut.conj (d.x₄ 1)) := by
  set K := Subgroup.closure (invXiAut (MulAut.conj (d.x₄ 1))) with hK
  have hC : Subgroup.centralizer {d.x₄ 1} ≤ K :=
    centralizer_le_closure_invXiAut_conj ⟨d.w₀, w₀_mem_invXi_x₄ d⟩
  have hw₀ : d.w₀ ∈ K := Subgroup.subset_closure (w₀_mem_invXi_x₄ d)
  have h₂ : ∀ a, d.x₂ a ∈ K := fun a =>
    hC (Subgroup.mem_centralizer_singleton_iff.2 (d.commute₂₄ a 1).eq)
  have h₄ : ∀ a, d.x₄ a ∈ K := fun a =>
    hC (Subgroup.mem_centralizer_singleton_iff.2 (commute_of_add d.x₄_add a 1).eq)
  have h₅ : ∀ a, d.x₅ a ∈ K := fun a =>
    hC (Subgroup.mem_centralizer_singleton_iff.2 (d.commute₄₅ 1 a).eq.symm)
  have h₆ : ∀ a, d.x₆ a ∈ K := fun a =>
    hC (Subgroup.mem_centralizer_singleton_iff.2 (d.commute₄₆ 1 a).eq.symm)
  have hv : d.v ∈ K :=
    hC (Subgroup.mem_centralizer_singleton_iff.2 (mul_inv_eq_iff_eq_mul.1 (d.v_conj_x₄ 1)))
  have hx5 : ∀ a : d.Γ₀, MulAut.conj d.u (d.x₂ a) = d.x₅ a := fun a => by
    rw [MulAut.conj_apply]
    exact d.u_conj_x₂ a
  have hkey : ∀ a : d.Γ₀,
      MulAut.conj d.u (MulAut.conj d.v (d.x₂ a)) = MulAut.conj d.w₀ (d.x₅ a) := fun a => by
    rw [← hx5 a, conj_w₀_conj_u d, conj_w₀_x₂ d]
  have hM : (d.U₂ ⊔ d.U₂.map (MulAut.conj d.v).toMonoidHom).map
      (MulAut.conj d.u).toMonoidHom ≤ K := by
    rw [Subgroup.map_sup]
    refine sup_le ?_ ?_
    · rintro _ ⟨_, ⟨a, rfl⟩, rfl⟩
      show MulAut.conj d.u (d.x₂ a) ∈ K
      rw [hx5]
      exact h₅ a
    · rintro _ ⟨_, ⟨_, ⟨a, rfl⟩, rfl⟩, rfl⟩
      show MulAut.conj d.u (MulAut.conj d.v (d.x₂ a)) ∈ K
      rw [hkey]
      exact conj_mem hw₀ (h₅ a)
  have hn : MulAut.conj d.u d.v ∈ K := hM ⟨d.v, v_mem_U₂_sup_conj d, rfl⟩
  have hnn : MulAut.conj d.u d.v = d.u * d.v * d.u := by rw [MulAut.conj_apply, d.u_inv]
  have hinv : (d.u * d.v * d.u)⁻¹ = d.u * d.v * d.u := by
    simp only [mul_inv_rev, d.u_inv, d.v_inv, mul_assoc]
  have hx1 : ∀ a, d.u * d.x₁ a * d.u ∈ K := fun a => by
    have h := conj_mem hn (h₄ a)
    rwa [hnn, MulAut.conj_apply, hinv, uvu_x₄ d] at h
  have h₁ : ∀ a, d.x₁ a ∈ K := fun a => by
    have h := conj_mem hw₀ (hx1 a)
    rwa [MulAut.conj_apply, d.w₀_inv, w₀_u_x₁_u d] at h
  have hu : d.u ∈ K := by
    refine (sup_le (fun g hg => ?_) ?_ : d.U₁ ⊔ d.U₁.map (MulAut.conj d.u).toMonoidHom ≤ K)
      (u_mem_U₁_sup_conj d)
    · obtain ⟨a, rfl⟩ := hg
      exact h₁ a
    · rintro _ ⟨_, ⟨a, rfl⟩, rfl⟩
      show MulAut.conj d.u (d.x₁ a) ∈ K
      rw [MulAut.conj_apply, d.u_inv]
      exact hx1 a
  have h₃ : ∀ a, d.x₃ a ∈ K := fun a => by
    have h := conj_mem hv (h₁ a)
    rwa [MulAut.conj_apply, d.v_conj_x₁] at h
  exact (invAutGen_iff_closure_invXiAut _).2
    (top_le_of_S_u_v d (S_le_of_root_groups d h₁ h₂ h₃ h₄ h₅ h₆) hu hv)

end CFSG.Quasithin.F7Two
