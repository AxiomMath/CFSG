module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P1Z2Key

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

local notation "pval" => CFSG.Quasithin.Fan86.valence

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace Z2Cfg

variable {α a₀ β δ δ' γ γ' : V}

theorem exists_far (F : FanTree Γ G) (D : Z2Cfg Γ α a₀ β δ δ' γ γ') (hα : pval Γ α = 5)
    {g : G} (hgβ : g • β = β) {v : V} (hgv : g • v = v) (hv : Γ.dist α v ≤ 4)
    (hva : 2 < Γ.dist a₀ v) (hvβ : 2 < Γ.dist β v) :
    ∃ l, pval Γ l = 5 ∧ g • l = l ∧ Γ.dist β l = 3 ∧ Γ.dist a₀ l = 4 ∧
      ∀ c, Γ.Adj a₀ c → c ≠ β → Γ.dist l c = 5 := by
  have hT := F.isTree
  obtain ⟨n, hn⟩ : ∃ n, Γ.dist β v = n := ⟨_, rfl⟩
  obtain ⟨P, hP0, hPn⟩ := IsTree.exists_arc hT n β v hn
  have hn3 : 3 ≤ n := by omega
  have dβ : ∀ k, k ≤ n → Γ.dist β (P.vert k) = k := fun k hk => by
    have := Arc.dist_eq hT P k hk
    rwa [hP0] at this
  have dv : ∀ k, k ≤ n → Γ.dist (P.vert k) v = n - k := fun k hk => by
    have := Arc.dist_vert hT P (i := k) (j := n) hk le_rfl
    rwa [hPn] at this
  have adj : ∀ k, k < n → Γ.Adj (P.vert k) (P.vert (k + 1)) := fun k hk => P.adj k hk
  have hP1 : P.vert 1 ≠ a₀ := by
    intro h1
    have hb : Γ.Adj β (P.vert 1) := by rw [← hP0]; exact adj 0 (by omega)
    have h2 : Γ.dist v (P.vert 1) + 1 = Γ.dist v β := by
      have e1 : Γ.dist v (P.vert 1) = Γ.dist (P.vert 1) v := SimpleGraph.dist_comm
      have e2 : Γ.dist v β = Γ.dist β v := SimpleGraph.dist_comm
      have := dv 1 (by omega)
      omega
    have h3 := IsTree.dist_succ_of_ne hT (a := β) (b := P.vert 1) (b' := α) (w := v) hb
      D.adj_αβ.symm (by rw [h1]; exact D.ne_αa.symm) h2
    have h4 : Γ.dist a₀ v = n - 1 := by rw [← h1]; exact dv 1 (by omega)
    have e1 : Γ.dist v α = Γ.dist α v := SimpleGraph.dist_comm
    have e2 : Γ.dist v β = Γ.dist β v := SimpleGraph.dist_comm
    omega
  have hb : Γ.Adj β (P.vert 1) := by rw [← hP0]; exact adj 0 (by omega)
  have hf : g • P.vert 3 = P.vert 3 :=
    Arc.fixes_of_ends hT F.adj_smul P (by rw [hP0]; exact hgβ) (by rw [hPn]; exact hgv) 3 hn3
  have d1 : Γ.dist (P.vert 3) (P.vert 1) = 2 := by
    rw [SimpleGraph.dist_comm]
    have := Arc.dist_vert hT P (i := 1) (j := 3) (by omega) hn3
    omega
  have d0 : Γ.dist (P.vert 3) β = 3 := by
    rw [SimpleGraph.dist_comm]
    exact dβ 3 hn3
  have d4 : Γ.dist (P.vert 3) a₀ = 4 := by
    have := IsTree.dist_succ_of_ne hT (a := β) (b := P.vert 1) (b' := a₀) (w := P.vert 3) hb
      D.adj_βa hP1 (by omega)
    omega
  refine ⟨P.vert 3, ?_, hf, dβ 3 hn3, by rw [SimpleGraph.dist_comm]; exact d4, ?_⟩
  · have h0 : pval Γ (P.vert 0) = 3 := by rw [hP0]; exact D.val_β F hα
    have h1 := valence_adj_five F h0 (adj 0 (by omega))
    have h2 := valence_adj_three F h1 (adj 1 (by omega))
    exact valence_adj_five F h2 (adj 2 (by omega))
  · intro c hc hcβ
    have := IsTree.dist_succ_of_ne hT (a := a₀) (b := β) (b' := c) (w := P.vert 3)
      D.adj_βa.symm hc (Ne.symm hcβ) (by omega)
    omega

end Z2Cfg

end CFSG.Quasithin.Fan86
