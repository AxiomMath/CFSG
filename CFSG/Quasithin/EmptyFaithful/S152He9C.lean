module

public import CFSG.Quasithin.EmptyFaithful.S152He9W
public import CFSG.Quasithin.Background.A3ComponentsCore

public section

namespace CFSG.Quasithin.He9

open CFSG.Open CFSG.Quasithin

namespace W5

theorem perfect_of_simple {G : Type*} [Group G] {A : Subgroup G} (hA : IsSimpleGroup ↥A)
    (hna : ∃ a ∈ A, ∃ b ∈ A, a * b ≠ b * a) : ⁅A, A⁆ = A := by
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro g₁ h₁ g₂ h₂
    exact A.mul_mem (A.mul_mem (A.mul_mem h₁ h₂) (A.inv_mem h₁)) (A.inv_mem h₂)
  · let C : Subgroup ↥A := (⁅A, A⁆).subgroupOf A
    have : C.Normal := ⟨fun n hn g => by
      show ((g : G) * (n : G) * (g : G)⁻¹) ∈ ⁅A, A⁆
      have h1 : ((g : G) * (n : G) * (g : G)⁻¹ * (n : G)⁻¹) ∈ ⁅A, A⁆ :=
        Subgroup.commutator_mem_commutator g.2 n.2
      have h2 : ((g : G) * (n : G) * (g : G)⁻¹) = ((g : G) * (n : G) * (g : G)⁻¹ * (n : G)⁻¹) * n := by
        group
      rw [h2]
      exact (⁅A, A⁆).mul_mem h1 hn⟩
    rcases hA.eq_bot_or_eq_top_of_normal C with h | h
    · exfalso
      obtain ⟨a, ha, b, hb, hab⟩ := hna
      have h1 : (a * b * a⁻¹ * b⁻¹) ∈ ⁅A, A⁆ := Subgroup.commutator_mem_commutator ha hb
      have h2 : (⟨a * b * a⁻¹ * b⁻¹, A.mul_mem (A.mul_mem (A.mul_mem ha hb) (A.inv_mem ha))
        (A.inv_mem hb)⟩ : ↥A) ∈ C := h1
      rw [h, Subgroup.mem_bot] at h2
      have h3 : a * b * a⁻¹ * b⁻¹ = 1 := congrArg Subtype.val h2
      apply hab
      calc a * b = (a * b * a⁻¹ * b⁻¹) * (b * a) := by group
        _ = b * a := by rw [h3, one_mul]
    · intro a ha
      have : (⟨a, ha⟩ : ↥A) ∈ C := by rw [h]; exact Subgroup.mem_top _
      exact this

theorem eq_bot_or_eq_of_subnormal {G : Type*} [Group G] {A K : Subgroup G} (hA : IsSimpleGroup ↥A)
    (h : IsSubnormal K A) : K = ⊥ ∨ K = A :=
  h.eq_bot_or_eq_of_isSimpleGroup hA

theorem A1_perfect : ⁅A1, A1⁆ = A1 := by
  refine perfect_of_simple A1_simple ?_
  obtain ⟨a, b, ha, hb, hab⟩ := A5_nonabelian
  refine ⟨incl1 a, incl1_mem_A1 (mem_A5.2 ha), incl1 b, incl1_mem_A1 (mem_A5.2 hb), ?_⟩
  intro h
  exact hab (incl1_injective (by rw [map_mul, map_mul, h]))

theorem A2_perfect : ⁅A2, A2⁆ = A2 := by
  refine perfect_of_simple A2_simple ?_
  obtain ⟨a, b, ha, hb, hab⟩ := A5_nonabelian
  refine ⟨incl2 a, incl2_mem_A2 (mem_A5.2 ha), incl2 b, incl2_mem_A2 (mem_A5.2 hb), ?_⟩
  intro h
  exact hab (incl2_injective (by rw [map_mul, map_mul, h]))

theorem base_normal : base.Normal := (RegularWreathProduct.rightHom : W5 →* Q2).normal_ker

theorem A1_subnormal : IsSubnormal A1 (⊤ : Subgroup W5) := by
  refine IsSubnormal.step A1_le_base ?_ (IsSubnormal.step le_top ?_ (IsSubnormal.refl _))
  · rw [Subgroup.normal_subgroupOf_iff_le_normalizer A1_le_base, normalizer_A1]
  · have := base_normal
    exact Subgroup.normal_subgroupOf

theorem A2_subnormal : IsSubnormal A2 (⊤ : Subgroup W5) := by
  refine IsSubnormal.step A2_le_base ?_ (IsSubnormal.step le_top ?_ (IsSubnormal.refl _))
  · rw [Subgroup.normal_subgroupOf_iff_le_normalizer A2_le_base, normalizer_A2]
  · have := base_normal
    exact Subgroup.normal_subgroupOf

theorem A1_mem_cComp : A1 ∈ cComp (⊤ : Subgroup W5) := by
  refine ⟨A1_ne_bot, A1_perfect, A1_subnormal, ?_⟩
  intro K hKlt hKne _ hKsub
  have hsub : IsSubnormal K A1 := A3.subnormal_of_le_of_le hKsub hKlt.le le_top
  rcases eq_bot_or_eq_of_subnormal A1_simple hsub with h | h
  · exact hKne h
  · exact hKlt.ne h

theorem A2_mem_cComp : A2 ∈ cComp (⊤ : Subgroup W5) := by
  refine ⟨A2_ne_bot, A2_perfect, A2_subnormal, ?_⟩
  intro K hKlt hKne _ hKsub
  have hsub : IsSubnormal K A2 := A3.subnormal_of_le_of_le hKsub hKlt.le le_top
  rcases eq_bot_or_eq_of_subnormal A2_simple hsub with h | h
  · exact hKne h
  · exact hKlt.ne h

end W5

end CFSG.Quasithin.He9
