module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9P4XArc
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8Stmt1
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P1Lab
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P1Geo

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace P4X

section pair

variable {α a₀ ξ₁ η₁ η' : V}

theorem valence_of_isZ2Pair (F : FanTree Γ G) (hα : valence Γ α = 5)
    (hY : IsZ2Pair Γ G α a₀ ξ₁ η₁ η' 2) :
    valence Γ η₁ = 5 ∧ valence Γ η' = 5 := by
  obtain ⟨-, -, -, -, -, h6, h7, -⟩ := hY
  exact ⟨valence_of_dist_even F hα (by rw [h6]), valence_of_dist_even F hα (by rw [h7])⟩

theorem dist_le_of_isZ2Pair (F : FanTree Γ G) (hY : IsZ2Pair Γ G α a₀ ξ₁ η₁ η' 2) :
    Γ.dist η₁ η' ≤ 4 := by
  obtain ⟨-, -, -, h4, h5, -⟩ := hY
  have h4' : Γ.dist η₁ a₀ = 2 := by rw [SimpleGraph.dist_comm]; exact h4
  have h := F.isTree.connected.dist_triangle (u := η₁) (v := a₀) (w := η')
  omega

theorem dist_alpha_xi_of_isZ2Pair (hY : IsZ2Pair Γ G α a₀ ξ₁ η₁ η' 2) : Γ.dist α ξ₁ = 1 := by
  obtain ⟨h1, -, h3, -⟩ := hY
  omega

theorem t_sq {F : FanTree Γ G} {L : ZLab Γ G} (h71c : Fan71c F L) (hα : valence Γ α = 5)
    (hY : IsZ2Pair Γ G α a₀ ξ₁ η₁ η' 2) :
    (L.z η₁ * L.z η') * (L.z η₁ * L.z η') = 1 := by
  obtain ⟨hv1, hv2⟩ := valence_of_isZ2Pair F hα hY
  have hc := h71c.z_comm_of_dist_le hv1 hv2 (dist_le_of_isZ2Pair F hY)
  have h0 := L.z_mul_self hv1
  have h1 := L.z_mul_self hv2
  calc L.z η₁ * L.z η' * (L.z η₁ * L.z η')
      = L.z η₁ * (L.z η' * L.z η₁) * L.z η' := by group
    _ = (L.z η₁ * L.z η₁) * (L.z η' * L.z η') := by rw [← hc]; group
    _ = 1 := by rw [h0, h1, mul_one]

end pair

theorem t_facts {F : FanTree Γ G} {L : ZLab Γ G} (h71c : Fan71c F L) (h81 : Fan81 F L)
    {α β a₀ ξ₁ η₁ η' : V} (hα : valence Γ α = 5) (hαβ : Γ.Adj α β)
    (hY : IsZ2Pair Γ G α a₀ ξ₁ η₁ η' 2) (hξ : ξ₁ ≠ β) :
    (L.z η₁ * L.z η') * (L.z η₁ * L.z η') = 1 ∧ (L.z η₁ * L.z η') • α = α ∧
      (L.z η₁ * L.z η') • β = β ∧
      ∀ A, Γ.Adj β A → A ≠ α → (L.z η₁ * L.z η') • A ≠ A := by
  have hT := F.isTree
  have key : ∀ v, (Γ.dist α v ≤ 4 ∧ (L.z η₁ * L.z η') • v = v) ↔
      (Γ.dist a₀ v ≤ 2 ∨ Γ.dist ξ₁ v ≤ 2) := fun v =>
    Set.ext_iff.1 (h81 α a₀ ξ₁ η₁ η' hα hY) v
  have hd1 : Γ.dist α ξ₁ = 1 := dist_alpha_xi_of_isZ2Pair hY
  have hd1' : Γ.dist ξ₁ α = 1 := by rw [SimpleGraph.dist_comm]; exact hd1
  have hdb : Γ.dist α β = 1 := dist_eq_one_iff_adj.2 hαβ
  have hdxb : Γ.dist ξ₁ β ≤ 2 := by
    have := hT.connected.dist_triangle (u := ξ₁) (v := α) (w := β)
    omega
  refine ⟨t_sq h71c hα hY, ((key α).2 (Or.inr (by omega))).2,
    ((key β).2 (Or.inr hdxb)).2, fun A hA hAα hfix => ?_⟩
  have hdA : Γ.dist α A ≤ 4 := by
    have := hT.connected.dist_triangle (u := α) (v := β) (w := A)
    have h1 : Γ.dist β A = 1 := dist_eq_one_iff_adj.2 hA
    omega
  obtain ⟨h1, hadj, -⟩ := hY
  have hα₀ : α ≠ a₀ := fun h => by
    rw [h, SimpleGraph.dist_self] at h1
    omega
  let Q : Arc Γ 4 := mkArc4 A β α ξ₁ a₀ hA.symm hαβ.symm
    (dist_eq_one_iff_adj.1 hd1) hadj.symm hAα hξ.symm hα₀
  have e0 : Q.vert 0 = A := mkArc4_vert_zero
  have e3 : Q.vert 3 = ξ₁ := mkArc4_vert_three
  have e4 : Q.vert 4 = a₀ := mkArc4_vert_four
  have d4 := Arc.dist_vert hT Q (i := 0) (j := 4) (by norm_num) le_rfl
  have d3 := Arc.dist_vert hT Q (i := 0) (j := 3) (by norm_num) (by norm_num)
  rw [e0, e4] at d4
  rw [e0, e3] at d3
  rcases (key A).1 ⟨hdA, hfix⟩ with h | h
  · rw [SimpleGraph.dist_comm] at h
    omega
  · rw [SimpleGraph.dist_comm] at h
    omega

end P4X

end CFSG.Quasithin.Fan86
