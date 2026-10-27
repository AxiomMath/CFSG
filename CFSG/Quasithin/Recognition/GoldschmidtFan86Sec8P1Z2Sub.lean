module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P1Z2Key

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph

local notation "pval" => CFSG.Quasithin.Fan86.valence

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace Z2Cfg

variable {α a₀ β δ δ' γ γ' : V} {F : FanTree Γ G} {L : ZLab Γ G}

theorem dist_far (hT : Γ.IsTree) (D : Z2Cfg Γ α a₀ β δ δ' γ γ') {ν w : V} (hν : Γ.Adj β ν)
    (hνa : ν ≠ a₀) (hw : Γ.Adj ν w) (hwβ : w ≠ β) : Γ.dist δ w = 5 :=
  IsTree.dist_eq_five_of_chain hT D.adj_γδ.symm D.adj_aγ.symm D.adj_βa.symm hν hw D.ne_δa
    D.ne_γβ hνa.symm hwβ.symm

theorem dist_far' (hT : Γ.IsTree) (D : Z2Cfg Γ α a₀ β δ δ' γ γ') {ν w : V} (hν : Γ.Adj β ν)
    (hνa : ν ≠ a₀) (hw : Γ.Adj ν w) (hwβ : w ≠ β) : Γ.dist δ' w = 5 :=
  IsTree.dist_eq_five_of_chain hT D.adj_γ'δ'.symm D.adj_aγ'.symm D.adj_βa.symm hν hw D.ne_δ'a
    D.ne_γ'β hνa.symm hwβ.symm

theorem rho_mem_nbrStab (D : Z2Cfg Γ α a₀ β δ δ' γ γ') (h71c : Fan71c F L)
    (hα : pval Γ α = 5) {ν : V} (hν : Γ.Adj β ν) (hνa : ν ≠ a₀) :
    L.z δ * L.z δ' ∈ nbrStab Γ G ν := by
  have hT := F.isTree
  have hδ5 := D.val_δ F hα
  have hδ'5 := D.val_δ' F hα
  have hβa : Γ.dist a₀ β = 1 := dist_eq_one_iff_adj.mpr D.adj_βa.symm
  have hβν : Γ.dist β ν = 1 := dist_eq_one_iff_adj.mpr hν
  have key : ∀ {x : V}, Γ.dist x a₀ ≤ 2 → Γ.dist x β ≤ 3 ∧ Γ.dist x ν ≤ 4 := by
    intro x hx
    have h1 := hT.connected.dist_triangle (u := x) (v := a₀) (w := β)
    have h2 := hT.connected.dist_triangle (u := x) (v := β) (w := ν)
    omega
  obtain ⟨w, hw, hwβ⟩ := F.exists_adj_ne ν β
  have hz : ∀ {x : V}, valence Γ x = 5 → Γ.dist x a₀ ≤ 2 → Γ.dist x w = 5 →
      L.z x ∈ MulAction.stabilizer G ν ⊓ MulAction.stabilizer G β ∧ L.z x ∉ nbrStab Γ G ν := by
    intro x hx5 hxa hxw
    refine ⟨⟨(h71c.z_mem_stabilizer_iff hx5 ν).2 (key hxa).2,
      (h71c.z_mem_stabilizer_iff hx5 β).2 (by have := (key hxa).1; omega)⟩, fun hK => ?_⟩
    have := (h71c.z_smul_eq_iff hx5 w).1 (mem_nbrStab.1 hK w hw)
    omega
  obtain ⟨h1, h1'⟩ := hz hδ5 (D.dist_δ_le hT) (D.dist_far hT hν hνa hw hwβ)
  obtain ⟨h2, h2'⟩ := hz hδ'5 (D.dist_δ'_le hT) (D.dist_far' hT hν hνa hw hwβ)
  exact F.mul_mem_nbrStab_of_sq_eq_one hν.symm h1 h2 (L.z_mul_self hδ5) (L.z_mul_self hδ'5)
    h1' h2'

theorem rho_smul_of_dist_β (D : Z2Cfg Γ α a₀ β δ δ' γ γ') (h71c : Fan71c F L)
    (hα : pval Γ α = 5) {v : V} (hv : Γ.dist β v ≤ 2) : (L.z δ * L.z δ') • v = v := by
  have hT := F.isTree
  have hβa : Γ.dist a₀ β = 1 := dist_eq_one_iff_adj.mpr D.adj_βa.symm
  have hcase : v = β ∨ Γ.Adj β v ∨ ∃ ν, Γ.Adj β ν ∧ Γ.Adj ν v := by
    rcases Nat.lt_or_ge (Γ.dist β v) 2 with h | h
    · rcases Nat.lt_or_ge (Γ.dist β v) 1 with h' | h'
      · left
        exact ((hT.connected.preconnected β v).dist_eq_zero_iff.1 (by omega)).symm
      · right
        left
        exact dist_eq_one_iff_adj.mp (by omega)
    · exact Or.inr (Or.inr (exists_adj_adj_of_dist_two hT (by omega)))
  rcases hcase with rfl | h | ⟨ν, hβν, hνv⟩
  · exact D.rho_smul_of_dist_le h71c hα (by omega)
  · have := hT.connected.dist_triangle (u := a₀) (v := β) (w := v)
    have h1 : Γ.dist β v = 1 := dist_eq_one_iff_adj.mpr h
    exact D.rho_smul_of_dist_le h71c hα (by omega)
  · by_cases hνa : ν = a₀
    · subst hνa
      have := dist_eq_one_iff_adj.mpr hνv
      exact D.rho_smul_of_dist_le h71c hα (by omega)
    · exact mem_nbrStab.1 (D.rho_mem_nbrStab h71c hα hβν hνa) v hνv

theorem sub_target (D : Z2Cfg Γ α a₀ β δ δ' γ γ') (h71c : Fan71c F L) (hα : pval Γ α = 5)
    {v : V} (hv : Γ.dist a₀ v ≤ 2 ∨ Γ.dist β v ≤ 2) :
    Γ.dist α v ≤ 4 ∧ (L.z δ * L.z δ') • v = v := by
  have hT := F.isTree
  have hαβ : Γ.dist α β = 1 := dist_eq_one_iff_adj.mpr D.adj_αβ
  have hβa : Γ.dist β a₀ = 1 := dist_eq_one_iff_adj.mpr D.adj_βa
  rcases hv with h | h
  · refine ⟨?_, D.rho_smul_of_dist_le h71c hα h⟩
    have h1 := hT.connected.dist_triangle (u := α) (v := β) (w := a₀)
    have h2 := hT.connected.dist_triangle (u := α) (v := a₀) (w := v)
    omega
  · refine ⟨?_, D.rho_smul_of_dist_β h71c hα h⟩
    have := hT.connected.dist_triangle (u := α) (v := β) (w := v)
    omega

end Z2Cfg

end CFSG.Quasithin.Fan86
