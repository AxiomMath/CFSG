module

public import CFSG.LocalAnalysis.WeakClosure81.EightFifteen

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup

variable {G : Type} [Group G] [Finite G]

theorem Sit813.oTwoMod_le_centralizer_V (hin : W3In814 G) {V H T A L K : Subgroup G} {i : ℕ}
    (h : Sit813 V H T i A L K) : oTwoMod (cGrp H T) K ≤ centralizer (V : Set G) := by
  obtain ⟨hnat, -, h4⟩ := h.eight_fourteen hin
  have hNV1 := hin.nv1 h
  have hNU₁ := h.oTwoMod_le_centralizer_u1Grp hNV1
  have hKN : K ≤ normalizer (oTwoMod (cGrp H T) K : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer oTwoMod_le_self).mp h.oTwoMod_normal
  have h2 : (v1Grp V H T A K).relIndex V = 2 := h.relIndex_v1Grp h4
  have hV₁ : ∀ n ∈ oTwoMod (cGrp H T) K, ∀ y ∈ V, n * y * n⁻¹ * y⁻¹ ∈ v1Grp V H T A K := by
    intro n hn y hy
    exact comm_mem_of_relIndex_two_of_le Sit813.v1Grp_le_V le_rfl h2
      (h.oTwoMod_le_normalizer hn) (Subgroup.centralizer_le_normalizer _ (hNV1 hn)) hy
  have hU₁V : ∀ a ∈ u1Grp V H T A K, ∀ b ∈ V, a * b = b * a := fun a ha b hb =>
    h.isElemAbelian_uGrp.comm (Sit813.u1Grp_le_uGrp ha) (Sit813.V_le_uGrp hb)
  have hcomm : ∀ n ∈ oTwoMod (cGrp H T) K, ∀ x ∈ V, n * x = x * n := by
    intro n hn x hx
    by_contra hne
    set c : G := n * x * n⁻¹ * x⁻¹ with hc
    have hc1 : c ≠ 1 := by
      intro h1
      apply hne
      calc n * x = (n * x * n⁻¹ * x⁻¹) * x * n := by group
        _ = x * n := by rw [← hc, h1]; group
    have hcV₁ : c ∈ v1Grp V H T A K := hV₁ n hn x hx
    have hcV : c ∈ V := Sit813.v1Grp_le_V hcV₁
    have hcU₁ : c ∈ u1Grp V H T A K := Sit813.v1Grp_le_u1Grp hcV₁
    have hcD : c ∉ u1Grp V H T A K ⊓ centralizer (K : Set G) := by
      intro hmem
      refine hc1 (h.eq_one_of_centralizes_K hcV fun k hk => ?_)
      exact Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hmem).2 k hk
    have horb : {y : G | ∃ k ∈ K, y = k * c * k⁻¹} ⊆ (v1Grp V H T A K : Set G) := by
      rintro _ ⟨k, hk, rfl⟩
      have hn' : k * n * k⁻¹ ∈ oTwoMod (cGrp H T) K :=
        (Subgroup.mem_normalizer_iff.mp (hKN hk) n).mp hn
      have hx' : k * x * k⁻¹ ∈ uGrp V K := mem_conjClosure hk hx
      rw [h.eight_fifteen hin] at hx'
      obtain ⟨d, hd, y, hy, hdy⟩ := exists_mul_of_mem_sup_of_comm hU₁V hx'
      have he : (k * n * k⁻¹) * y * (k * n * k⁻¹)⁻¹ * y⁻¹ ∈ v1Grp V H T A K := hV₁ _ hn' y hy
      have hde : d * ((k * n * k⁻¹) * y * (k * n * k⁻¹)⁻¹ * y⁻¹) =
          ((k * n * k⁻¹) * y * (k * n * k⁻¹)⁻¹ * y⁻¹) * d :=
        h.isElemAbelian_uGrp.comm (Sit813.u1Grp_le_uGrp hd)
          (Sit813.u1Grp_le_uGrp (Sit813.v1Grp_le_u1Grp he))
      have hqd : (k * n * k⁻¹) * d = d * (k * n * k⁻¹) :=
        (Subgroup.mem_centralizer_iff.mp (hNU₁ hn') d hd).symm
      have key : k * c * k⁻¹ = (k * n * k⁻¹) * y * (k * n * k⁻¹)⁻¹ * y⁻¹ := by
        have h1 : k * c * k⁻¹ = (k * n * k⁻¹) * (k * x * k⁻¹) * (k * n * k⁻¹)⁻¹ *
            (k * x * k⁻¹)⁻¹ := by rw [hc]; group
        rw [h1, ← hdy]
        calc (k * n * k⁻¹) * (d * y) * (k * n * k⁻¹)⁻¹ * (d * y)⁻¹
            = ((k * n * k⁻¹) * d) * y * (k * n * k⁻¹)⁻¹ * y⁻¹ * d⁻¹ := by group
          _ = (d * (k * n * k⁻¹)) * y * (k * n * k⁻¹)⁻¹ * y⁻¹ * d⁻¹ := by rw [hqd]
          _ = d * ((k * n * k⁻¹) * y * (k * n * k⁻¹)⁻¹ * y⁻¹) * d⁻¹ := by group
          _ = (((k * n * k⁻¹) * y * (k * n * k⁻¹)⁻¹ * y⁻¹) * d) * d⁻¹ := by rw [hde]
          _ = (k * n * k⁻¹) * y * (k * n * k⁻¹)⁻¹ * y⁻¹ := by group
      rw [key]
      exact he
    have h15 := hnat.fifteen_le_ncard_orbit Sit813.k_le_normalizer_u1Grp hcU₁ hcD
    have h4' : Set.ncard (v1Grp V H T A K : Set G) = 4 := by
      rw [← Nat.card_coe_set_eq]
      exact h4
    have hle := Set.ncard_le_ncard horb (Set.toFinite _)
    omega
  intro n hn
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  exact (hcomm n hn x hx).symm

end CFSG.LocalAnalysis.WeakClosure81

end
