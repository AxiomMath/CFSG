module

public import CFSG.Quasithin.EmptyFaithful.S153E56E4
public import CFSG.Quasithin.EmptyFaithful.S153E56E1

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.S1417 CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

namespace S153E56e

open CFSG.Quasithin.S153E

section JFacts

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}
  {N₁ N₂ : Subgroup (MulAut ↥(VZ T M))} {g : G} {s : ℕ} {y : G}
  {cx : Ctx15350 T Mc M V₁ V₂ t}

variable (cx) in
abbrev N₂i (N₂ : Subgroup (MulAut ↥(VZ T M))) :
    Subgroup (MulAut (IntMod (VZ T M) cx.c.hyp.elemAbelian)) := N₂

omit [Finite G] in
theorem J_le_YU {y : G} (hy : y ∈ Y153 Mc M) :
    Jgp153 T M V₁ Mc y ≤ Y153 Mc M ⊔ UH153 T M V₁ Mc := by
  refine sup_le le_sup_right fun x hx => ?_
  rw [mem_conjSubgroup_iff] at hx
  have e : x = y⁻¹ * (y * x * y⁻¹) * y := by group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mem_sup_left hy))
    (Subgroup.mem_sup_right hx)) (Subgroup.mem_sup_left hy)

omit [Finite G] in
theorem U_le_J (T M V₁ Mc : Subgroup G) (y : G) : UH153 T M V₁ Mc ≤ Jgp153 T M V₁ Mc y := le_sup_left

omit [Finite G] in
theorem U'_le_J (T M V₁ Mc : Subgroup G) (y : G) :
    conjSubgroup (UH153 T M V₁ Mc) y ≤ Jgp153 T M V₁ Mc y := le_sup_right

theorem bar_mul' (cx : Ctx15350 T Mc M V₁ V₂ t) {x x' : G}
    (hx : x ∈ Y153 Mc M ⊔ UH153 T M V₁ Mc) (hx' : x' ∈ Y153 Mc M ⊔ UH153 T M V₁ Mc)
    (hxx' : x * x' ∈ Y153 Mc M ⊔ UH153 T M V₁ Mc) :
    S153E55.bar cx hxx' = S153E55.bar cx hx * S153E55.bar cx hx' := by
  unfold S153E55.bar
  rw [← map_mul]
  rfl

theorem bar_inv' (cx : Ctx15350 T Mc M V₁ V₂ t) {x : G}
    (hx : x ∈ Y153 Mc M ⊔ UH153 T M V₁ Mc) (hx' : x⁻¹ ∈ Y153 Mc M ⊔ UH153 T M V₁ Mc) :
    S153E55.bar cx hx' = (S153E55.bar cx hx)⁻¹ := by
  unfold S153E55.bar
  rw [← map_inv]
  rfl

theorem bar_pow_eq_one (cx : Ctx15350 T Mc M V₁ V₂ t) {x : G}
    (hx : x ∈ Y153 Mc M ⊔ UH153 T M V₁ Mc) {k : ℕ} (hk : x ^ 2 ^ k = 1) :
    (S153E55.bar cx hx) ^ 2 ^ k = 1 := by
  unfold S153E55.bar
  rw [← map_pow]
  have : (⟨x, S153E55.YU_le_normalizer_V cx hx⟩ : Subgroup.normalizer (VZ T M : Set G)) ^ 2 ^ k = 1 :=
    Subtype.ext hk
  rw [this, map_one]

theorem bar_mem_sup (cx : Ctx15350 T Mc M V₁ V₂ t) (H : Hyps56 cx N₁ N₂ g s y) {ρ : G}
    (hρ : ρ ∈ Y153 Mc M ⊔ UH153 T M V₁ Mc) : S153E55.bar cx hρ ∈ N₁i cx N₁ ⊔ N₂i cx N₂ := by
  have := convI_mem_autI cx.c.hyp.elemAbelian hρ (S153E55.YU_le_normalizer_V cx hρ)
  rwa [S153E55.autI_YU_eq cx H.c.h53one] at this

theorem card_autI_U (cx : Ctx15350 T Mc M V₁ V₂ t) (h51 : Concl15351 cx) (h52 : Concl15352 cx) :
    Nat.card ↥(autI cx.c.hyp.elemAbelian (UH153 T M V₁ Mc)) = 4 := by
  rcases h51.two with h | ⟨hab, -, -, -⟩
  · exact h.2.1.1
  · exfalso
    obtain ⟨a, ha, b, hb, hne⟩ := h52
    exact hne (B2F.isElemAbelian_comm hab ha hb)

theorem card_N₂ (c : Concl15353One cx N₁ N₂) : Nat.card ↥N₂ = 6 := by
  obtain ⟨e⟩ := c.iso₂
  rw [Nat.card_congr e.toEquiv]
  simp [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]

theorem exists_j (H : Hyps56 cx N₁ N₂ g s y) :
    ∃ j ∈ Jgp153 T M V₁ Mc y, y⁻¹ * j ∈ Subgroup.centralizer (VZ T M : Set G) := by
  have hV := cx.c.hyp.elemAbelian
  obtain ⟨e⟩ := H.c.h53one.iso₁
  have hcomm : ∀ a ∈ N₁i cx N₁, ∀ b ∈ N₂i cx N₂, a * b = b * a := H.c.h53one.comm
  have hinf : N₁i cx N₁ ⊓ N₂i cx N₂ = ⊥ := H.c.h53one.inf
  have h4 := card_autI_U cx H.c.h51 H.c.h52
  have h6 := card_N₂ H.c.h53one
  have hnot : ¬ autI hV (UH153 T M V₁ Mc) ≤ N₂i cx N₂ := fun hle => by
    have := Subgroup.card_dvd_of_le hle
    rw [h4] at this
    have h6' : Nat.card ↥(N₂i cx N₂) = 6 := h6
    rw [h6'] at this
    exact absurd this (by norm_num)
  obtain ⟨φ, hφU, hφN₂⟩ := IsConcreteLE.not_le_iff_exists.1 hnot
  obtain ⟨u', hu'U, hu'⟩ := (mem_autI hV).1 hφU
  have hyYU := y_mem_YU H
  have hyN := y_mem_N H
  have huU : (u' : G) ∈ UH153 T M V₁ Mc := hu'U
  have huYU : (u' : G) ∈ Y153 Mc M ⊔ UH153 T M V₁ Mc := Subgroup.mem_sup_right huU
  have hbar_u : S153E55.bar cx huYU = φ := hu'
  obtain ⟨Ω, -, hsup, hΩ⟩ := H.c.h53one.omega
  have hφsup : φ ∈ N₁i cx N₁ ⊔ N₂i cx N₂ := by
    have h1 : autOn (UH153 T M V₁ Mc) (VZ T M) ≤ Ω := le_sup_left.trans hsup.le
    have h2 : φ ∈ Ω := h1 hφU
    rw [← hΩ] at h2
    exact h2
  obtain ⟨a, ha, b, hb, hab⟩ := S153E55.mem_sup_of_comm hcomm hφsup
  have ha1 : a ≠ 1 := by
    intro h1
    apply hφN₂
    rw [← hab, h1, one_mul]
    exact hb
  have hφφ : φ * φ = 1 := autI_U_sq cx hφU
  have hcore := core_conj hcomm hinf e (c := ybar H) (a := a) (b := b) (ybar_mem_N₁ H)
    (ybar_pow_three H) (ybar_ne_one H) ha hb ha1 (by rw [hab]; exact hφφ)
  rw [hab] at hcore
  have hyiYU : y⁻¹ ∈ Y153 Mc M ⊔ UH153 T M V₁ Mc := Subgroup.inv_mem _ hyYU
  have hu'yYU : y⁻¹ * (u' : G) * y ∈ Y153 Mc M ⊔ UH153 T M V₁ Mc :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hyiYU huYU) hyYU
  have hj0YU : (u' : G) * (y⁻¹ * (u' : G) * y) ∈ Y153 Mc M ⊔ UH153 T M V₁ Mc :=
    Subgroup.mul_mem _ huYU hu'yYU
  have hbar_conj : S153E55.bar cx hu'yYU = (ybar H)⁻¹ * φ * ybar H := by
    have h1 : S153E55.bar cx (Subgroup.mul_mem _ hyiYU huYU) = (ybar H)⁻¹ * φ := by
      rw [bar_mul' cx hyiYU huYU, bar_inv' cx hyYU hyiYU, hbar_u]
    rw [bar_mul' cx (Subgroup.mul_mem _ hyiYU huYU) hyYU, h1]
  have hbar_j0 : S153E55.bar cx hj0YU = ybar H * ybar H := by
    rw [bar_mul' cx huYU hu'yYU, hbar_u, hbar_conj]
    exact hcore
  have hj0J : (u' : G) * (y⁻¹ * (u' : G) * y) ∈ Jgp153 T M V₁ Mc y := by
    refine Subgroup.mul_mem _ (U_le_J T M V₁ Mc y huU) (U'_le_J T M V₁ Mc y ?_)
    rw [mem_conjSubgroup_iff]
    have e : y * (y⁻¹ * (u' : G) * y) * y⁻¹ = (u' : G) := by group
    rw [e]
    exact huU
  have hj0J' := J_le_YU (T := T) (M := M) (V₁ := V₁) (Mc := Mc) (y_mem_Y H) hj0J
  have hjYU : ((u' : G) * (y⁻¹ * (u' : G) * y)) * ((u' : G) * (y⁻¹ * (u' : G) * y)) ∈
      Y153 Mc M ⊔ UH153 T M V₁ Mc := Subgroup.mul_mem _ hj0YU hj0YU
  refine ⟨((u' : G) * (y⁻¹ * (u' : G) * y)) * ((u' : G) * (y⁻¹ * (u' : G) * y)),
    Subgroup.mul_mem _ hj0J hj0J, ?_⟩
  have hyiJYU : y⁻¹ * (((u' : G) * (y⁻¹ * (u' : G) * y)) * ((u' : G) * (y⁻¹ * (u' : G) * y))) ∈
      Y153 Mc M ⊔ UH153 T M V₁ Mc := Subgroup.mul_mem _ hyiYU hjYU
  have hone : S153E55.bar cx hyiJYU = 1 := by
    rw [bar_mul' cx hyiYU hjYU, bar_inv' cx hyYU hyiYU, bar_mul' cx hj0YU hj0YU, hbar_j0]
    have h3 := ybar_pow_three H
    calc (ybar H)⁻¹ * (ybar H * ybar H * (ybar H * ybar H)) = ybar H * ybar H * ybar H := by group
      _ = ybar H ^ 3 := by rw [pow_succ, pow_two]
      _ = 1 := h3
  exact (convI_eq_one_iff hV ⟨_, S153E55.YU_le_normalizer_V cx hyiJYU⟩).1 hone

end JFacts

end S153E56e

end CFSG.Quasithin
