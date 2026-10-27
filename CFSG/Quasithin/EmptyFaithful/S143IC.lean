module

public import CFSG.Quasithin.EmptyFaithful.S143FE

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique
open scoped Pointwise

namespace S143

section Noncomm

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {g : G} (c : Counter T M g)

include c

theorem Counter.exists_noncomm_of_card_ge {C : Subgroup G} (hCU : C ≤ uOfL22 T M)
    (hC : 16 ≤ Nat.card C) : ∃ a ∈ C, ∃ b ∈ C, a * b ≠ b * a := by
  by_contra hall
  push Not at hall
  have h := c.h1281
  have hq8 := c.c15.q8sq
  have hcenter : centerOf (uOfL22 T M) = quasithinOmegaOneCenter T := c.centerOf_uOfL22_eq
  have hZ2 : Nat.card ↥(quasithinOmegaOneCenter T) = 2 := h.card_omegaOneCenter
  have hCeq : ∀ x ∈ C, x ∉ quasithinOmegaOneCenter T →
      C = uOfL22 T M ⊓ Subgroup.centralizer ({x} : Set G) := by
    intro x hx hxZ
    have hxc : x ∉ centerOf (uOfL22 T M) := by rw [hcenter]; exact hxZ
    have hcard16 := isQ8Sq_card_centralizer hq8 x (hCU hx) hxc
    have hle : C ≤ uOfL22 T M ⊓ Subgroup.centralizer ({x} : Set G) := fun y hy =>
      ⟨hCU hy, Subgroup.mem_centralizer_singleton_iff.mpr (hall y hy x hx)⟩
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [hcard16]; exact hC)
  obtain ⟨c₁, hc₁C, hc₁Z⟩ : ∃ c₁ ∈ C, c₁ ∉ quasithinOmegaOneCenter T := by
    by_contra hh
    push Not at hh
    have h1 : Nat.card C ≤ Nat.card ↥(quasithinOmegaOneCenter T) :=
      Subgroup.card_le_of_le fun x hx => hh x hx
    omega
  have hcard16 : Nat.card C = 16 := by
    have hxc : c₁ ∉ centerOf (uOfL22 T M) := by rw [hcenter]; exact hc₁Z
    have := isQ8Sq_card_centralizer hq8 c₁ (hCU hc₁C) hxc
    rw [← hCeq c₁ hc₁C hc₁Z] at this
    exact this
  obtain ⟨u₀, hu₀U, hu₀C⟩ : ∃ u₀ ∈ uOfL22 T M, u₀ ∉ C := by
    by_contra hh
    push Not at hh
    have h1 : Nat.card ↥(uOfL22 T M) ≤ Nat.card C := Subgroup.card_le_of_le fun x hx => hh x hx
    rw [hq8.1, hcard16] at h1
    omega
  have hcomm_ne : ∀ x ∈ C, x ∉ quasithinOmegaOneCenter T → u₀ * x * u₀⁻¹ * x⁻¹ ≠ 1 := by
    intro x hx hxZ he
    apply hu₀C
    rw [hCeq x hx hxZ]
    refine ⟨hu₀U, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    calc u₀ * x = (u₀ * x * u₀⁻¹ * x⁻¹) * x * u₀ := by group
      _ = x * u₀ := by rw [he]; group
  have hcomm_Z : ∀ x ∈ C, u₀ * x * u₀⁻¹ * x⁻¹ ∈ quasithinOmegaOneCenter T := fun x hx =>
    h.commutator_mem_omegaOneCenter hu₀U (hCU hx)
  obtain ⟨z₀, -, hz₀⟩ := (Nat.card_eq_two_iff' (1 : ↥(quasithinOmegaOneCenter T))).mp hZ2
  have hZeq : ∀ x ∈ quasithinOmegaOneCenter T, x ≠ 1 → x = (z₀ : G) := by
    intro x hx hx1
    exact congrArg Subtype.val (hz₀ ⟨x, hx⟩ (fun he => hx1 (congrArg Subtype.val he)))
  have hZcen : ∀ x ∈ quasithinOmegaOneCenter T, ∀ y ∈ uOfL22 T M, x * y = y * x := fun x hx y hy =>
    (Subgroup.mem_centralizer_iff.mp (h.omegaOneCenter_le_centerOf_uOfL22 hx).2 y hy).symm
  obtain ⟨c₂, hc₂C, hc₂Z, hc₁c₂Z⟩ : ∃ c₂ ∈ C, c₂ ∉ quasithinOmegaOneCenter T ∧
      c₁ * c₂ ∉ quasithinOmegaOneCenter T := by
    by_contra hh
    push Not at hh
    let S : Set G := (quasithinOmegaOneCenter T : Set G) ∪
      (fun z : G => c₁⁻¹ * z) '' (quasithinOmegaOneCenter T : Set G)
    have hsub : (C : Set G) ⊆ S := by
      intro x hx
      by_cases hxZ : x ∈ quasithinOmegaOneCenter T
      · exact Or.inl hxZ
      · refine Or.inr ⟨c₁ * x, hh x hx hxZ, ?_⟩
        show c₁⁻¹ * (c₁ * x) = x
        group
    have h1 : Nat.card C ≤ 4 := by
      rw [show Nat.card C = (C : Set G).ncard from Nat.card_coe_set_eq (C : Set G)]
      have h2 : (C : Set G).ncard ≤ S.ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
      have h3 : S.ncard ≤ (quasithinOmegaOneCenter T : Set G).ncard +
          ((fun z : G => c₁⁻¹ * z) '' (quasithinOmegaOneCenter T : Set G)).ncard :=
        Set.ncard_union_le _ _
      have h4 : ((fun z : G => c₁⁻¹ * z) '' (quasithinOmegaOneCenter T : Set G)).ncard ≤
          (quasithinOmegaOneCenter T : Set G).ncard := Set.ncard_image_le (Set.toFinite _)
      have h5 : (quasithinOmegaOneCenter T : Set G).ncard = 2 := by
        rw [← Nat.card_coe_set_eq]; exact hZ2
      omega
    omega
  have hc₁c₂C : c₁ * c₂ ∈ C := C.mul_mem hc₁C hc₂C
  have e₁ : u₀ * c₁ * u₀⁻¹ * c₁⁻¹ = (z₀ : G) :=
    hZeq _ (hcomm_Z c₁ hc₁C) (hcomm_ne c₁ hc₁C hc₁Z)
  have e₂ : u₀ * c₂ * u₀⁻¹ * c₂⁻¹ = (z₀ : G) :=
    hZeq _ (hcomm_Z c₂ hc₂C) (hcomm_ne c₂ hc₂C hc₂Z)
  have e₃ : u₀ * (c₁ * c₂) * u₀⁻¹ * (c₁ * c₂)⁻¹ = 1 := by
    have hz₀c : (z₀ : G) ∈ quasithinOmegaOneCenter T := z₀.2
    have hcc : (u₀ * c₁ * u₀⁻¹) = (z₀ : G) * c₁ := by
      calc u₀ * c₁ * u₀⁻¹ = (u₀ * c₁ * u₀⁻¹ * c₁⁻¹) * c₁ := by group
        _ = (z₀ : G) * c₁ := by rw [e₁]
    have hcc' : (u₀ * c₂ * u₀⁻¹) = (z₀ : G) * c₂ := by
      calc u₀ * c₂ * u₀⁻¹ = (u₀ * c₂ * u₀⁻¹ * c₂⁻¹) * c₂ := by group
        _ = (z₀ : G) * c₂ := by rw [e₂]
    have hzz : (z₀ : G) * (z₀ : G) = 1 :=
      c.VZ_sq (Hyp1281Two.omegaOneCenter_le_VZ T M hz₀c)
    calc u₀ * (c₁ * c₂) * u₀⁻¹ * (c₁ * c₂)⁻¹
        = (u₀ * c₁ * u₀⁻¹) * (u₀ * c₂ * u₀⁻¹) * c₂⁻¹ * c₁⁻¹ := by group
      _ = ((z₀ : G) * c₁) * ((z₀ : G) * c₂) * c₂⁻¹ * c₁⁻¹ := by rw [hcc, hcc']
      _ = (z₀ : G) * (c₁ * (z₀ : G)) * c₁⁻¹ := by group
      _ = (z₀ : G) * ((z₀ : G) * c₁) * c₁⁻¹ := by
          rw [← hZcen _ hz₀c c₁ (hCU hc₁C)]
      _ = (z₀ : G) * (z₀ : G) := by group
      _ = 1 := hzz
  exact hcomm_ne (c₁ * c₂) hc₁c₂C hc₁c₂Z e₃

end Noncomm

end S143

end CFSG.Quasithin
