module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P514Ctx
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec4Loc
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5Stmt

public section

namespace CFSG.Quasithin.Fan86

namespace P514

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem mkCtx (F : FanTree Γ G) (h40 : Fan40 F) (hXi1 : ∀ T : Track Γ G, ¬ Xi 1 T)
    (h513a : Fan513a F) {z : G} {α o : V} (hadj : Γ.Adj α o) (hv5 : valence Γ o = 5)
    (hcinv : z ∈ Cinv G α) (hball : z ∈ ballStab Γ G 2 α)
    (hprod : ∀ (l : List V) (h : V → G), l.Nodup → (∀ u, u ∈ l ↔ Γ.Adj o u) →
      (∀ u, Γ.Adj o u → h u • α = u) →
        (l.map fun u => h u * z * (h u)⁻¹).Pairwise Commute ∧
          (l.map fun u => h u * z * (h u)⁻¹).prod = 1) :
    LblCtx Γ z α o :=
  let B := mkBase F hadj hv5 hcinv hball hprod
  { adj := B.adj, v5 := B.v5, cinv := B.cinv, ball := B.ball, prod5 := B.prod5
    ne := by
      intro u u' hu hu' hne
      have hLu := Lb_cinv hcinv (exists_conj_of_adj F hadj hu)
      have hLu' := Lb_cinv hcinv (exists_conj_of_adj F hadj hu')
      have hnsr : ¬ RightSingular Γ G (Arc.two hu.symm hu' hne).vert 0 1 := fun hr =>
        h40 1 le_rfl (by norm_num) ⟨⟨(Arc.two hu.symm hu' hne).vert,
          fun i hi => (Arc.two hu.symm hu' hne).adj i (by omega),
          fun i hi => absurd hi (by omega)⟩, hr⟩
      exact h513a h40 hXi1 1 1 (Arc.two hu.symm hu' hne) le_rfl le_rfl hnsr
        (fun h => absurd h (by norm_num)) _ (by rw [Arc.two_vert_zero]; exact hLu) _
        (by
          show Lb z α u' ∈ Cinv G ((Arc.two hu.symm hu' hne).vert 2)
          rw [Arc.two_vert_two]
          exact hLu') }

end P514

end CFSG.Quasithin.Fan86
