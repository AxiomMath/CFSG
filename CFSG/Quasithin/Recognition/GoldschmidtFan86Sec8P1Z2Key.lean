module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P1Z2Geo
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P1Z2Loc
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P1Lab
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8Base

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph

local notation "pval" => CFSG.Quasithin.Fan86.valence

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

structure Z2Cfg (Γ : SimpleGraph V) (α a₀ β δ δ' γ γ' : V) : Prop where
  adj_αβ : Γ.Adj α β
  adj_βa : Γ.Adj β a₀
  ne_αa : α ≠ a₀
  adj_aγ : Γ.Adj a₀ γ
  ne_γβ : γ ≠ β
  adj_γδ : Γ.Adj γ δ
  ne_δa : δ ≠ a₀
  adj_aγ' : Γ.Adj a₀ γ'
  ne_γ'β : γ' ≠ β
  adj_γ'δ' : Γ.Adj γ' δ'
  ne_δ'a : δ' ≠ a₀

theorem exists_adj_adj_of_dist_two (hT : Γ.IsTree) {a δ : V} (hd : Γ.dist a δ = 2) :
    ∃ c, Γ.Adj a c ∧ Γ.Adj c δ := by
  obtain ⟨c, hcδ, hc⟩ := IsTree.exists_adj_dist_succ hT (u := a) (v := δ) (n := 1) hd
  exact ⟨c, dist_eq_one_iff_adj.mp hc, hcδ⟩

namespace Z2Cfg

theorem of_isZ2Pair (hT : Γ.IsTree) {α a₀ β δ δ' : V} (hZ : IsZ2Pair Γ G α a₀ β δ δ' 2) :
    ∃ γ γ', Z2Cfg Γ α a₀ β δ δ' γ γ' := by
  obtain ⟨hd0, hadj, hdβ, hdδ, hdδ', hαδ, hαδ', -⟩ := hZ
  have hαβ : Γ.Adj α β := dist_eq_one_iff_adj.mp (by omega)
  have hαa : α ≠ a₀ := fun h => by rw [h, SimpleGraph.dist_self] at hd0; omega
  obtain ⟨γ, hγ, hγδ⟩ := exists_adj_adj_of_dist_two hT hdδ
  obtain ⟨γ', hγ', hγ'δ'⟩ := exists_adj_adj_of_dist_two hT hdδ'
  have hne : ∀ {x y : V}, Γ.dist α y = 4 → Γ.Adj x y → x ≠ β := by
    intro x y hαy hxy hxβ
    subst hxβ
    have h1 := hT.connected.dist_triangle (u := α) (v := x) (w := y)
    have h2 : Γ.dist x y = 1 := dist_eq_one_iff_adj.mpr hxy
    have h3 : Γ.dist α x = 1 := dist_eq_one_iff_adj.mpr hαβ
    omega
  have hδne : ∀ {y : V}, Γ.dist a₀ y = 2 → y ≠ a₀ := fun hy h => by
    rw [h, SimpleGraph.dist_self] at hy
    omega
  exact ⟨γ, γ', ⟨hαβ, hadj.symm, hαa, hγ, hne (by omega) hγδ, hγδ, hδne hdδ, hγ',
    hne (by omega) hγ'δ', hγ'δ', hδne hdδ'⟩⟩

variable {α a₀ β δ δ' γ γ' : V}

theorem val_β (F : FanTree Γ G) (D : Z2Cfg Γ α a₀ β δ δ' γ γ') (hα : pval Γ α = 5) :
    pval Γ β = 3 := valence_adj_three F hα D.adj_αβ

theorem val_a (F : FanTree Γ G) (D : Z2Cfg Γ α a₀ β δ δ' γ γ') (hα : pval Γ α = 5) :
    pval Γ a₀ = 5 := valence_adj_five F (D.val_β F hα) D.adj_βa

theorem val_δ (F : FanTree Γ G) (D : Z2Cfg Γ α a₀ β δ δ' γ γ') (hα : pval Γ α = 5) :
    pval Γ δ = 5 :=
  valence_adj_five F (valence_adj_three F (D.val_a F hα) D.adj_aγ) D.adj_γδ

theorem val_δ' (F : FanTree Γ G) (D : Z2Cfg Γ α a₀ β δ δ' γ γ') (hα : pval Γ α = 5) :
    pval Γ δ' = 5 :=
  valence_adj_five F (valence_adj_three F (D.val_a F hα) D.adj_aγ') D.adj_γ'δ'

theorem dist_δ_le (hT : Γ.IsTree) (D : Z2Cfg Γ α a₀ β δ δ' γ γ') : Γ.dist δ a₀ ≤ 2 := by
  have h1 := hT.connected.dist_triangle (u := δ) (v := γ) (w := a₀)
  have h2 : Γ.dist δ γ = 1 := dist_eq_one_iff_adj.mpr D.adj_γδ.symm
  have h3 : Γ.dist γ a₀ = 1 := dist_eq_one_iff_adj.mpr D.adj_aγ.symm
  omega

theorem dist_δ'_le (hT : Γ.IsTree) (D : Z2Cfg Γ α a₀ β δ δ' γ γ') : Γ.dist δ' a₀ ≤ 2 := by
  have h1 := hT.connected.dist_triangle (u := δ') (v := γ') (w := a₀)
  have h2 : Γ.dist δ' γ' = 1 := dist_eq_one_iff_adj.mpr D.adj_γ'δ'.symm
  have h3 : Γ.dist γ' a₀ = 1 := dist_eq_one_iff_adj.mpr D.adj_aγ'.symm
  omega

variable {F : FanTree Γ G} {L : ZLab Γ G}

theorem rho_smul_of_dist_le (D : Z2Cfg Γ α a₀ β δ δ' γ γ') (h71c : Fan71c F L)
    (hα : pval Γ α = 5) {v : V} (hv : Γ.dist a₀ v ≤ 2) : (L.z δ * L.z δ') • v = v := by
  have hT := F.isTree
  have h1 : Γ.dist δ v ≤ 4 := by
    have := hT.connected.dist_triangle (u := δ) (v := a₀) (w := v)
    have := D.dist_δ_le hT
    omega
  have h2 : Γ.dist δ' v ≤ 4 := by
    have := hT.connected.dist_triangle (u := δ') (v := a₀) (w := v)
    have := D.dist_δ'_le hT
    omega
  rw [mul_smul, (h71c.z_smul_eq_iff (D.val_δ' F hα) v).2 h2,
    (h71c.z_smul_eq_iff (D.val_δ F hα) v).2 h1]

end Z2Cfg

end CFSG.Quasithin.Fan86
