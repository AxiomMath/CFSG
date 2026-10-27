module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P1D10Dist

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace D10Set

variable {L : ZLab Γ G} {α : V} (D : D10Set L α)

theorem dist_beta_below (F : FanTree Γ G) (h : Fan71c F L) {i m : Fin 5} (hi : i ≠ m) {w : V}
    (hw : Γ.dist w (D.beta m) + 1 = Γ.dist w α) :
    Γ.dist w (D.beta i) = Γ.dist w α + 1 :=
  IsTree.dist_succ_of_ne F.isTree (D.adj_start_beta m) (D.adj_start_beta i)
    (fun e => hi (D.beta_injective F h e).symm) hw

theorem dist_alpha_below (F : FanTree Γ G) (h : Fan71c F L) {i m : Fin 5} (hi : i ≠ m) {w : V}
    (hw : Γ.dist w (D.beta m) + 1 = Γ.dist w α) :
    Γ.dist w (D.alpha i) = Γ.dist w α + 2 := by
  have h1 := D.dist_beta_below F h hi hw
  have := IsTree.dist_succ_of_ne F.isTree (D.adj_start_beta i).symm (D.adj_beta_alpha i)
    (D.alpha_ne_start i).symm h1.symm
  omega

theorem dist_beta_alpha_ne (F : FanTree Γ G) (h : Fan71c F L) {i m : Fin 5} (hi : i ≠ m) :
    Γ.dist (D.beta m) (D.alpha i) = 3 := by
  have h1 : Γ.dist (D.beta m) (D.beta m) + 1 = Γ.dist (D.beta m) α := by
    rw [SimpleGraph.dist_self, SimpleGraph.dist_comm, D.dist_start_beta F m]
  have := D.dist_alpha_below F h hi h1
  rw [this, SimpleGraph.dist_comm, D.dist_start_beta F m]

theorem dist_alpha_start (F : FanTree Γ G) (i : Fin 5) : Γ.dist (D.alpha i) α = 2 := by
  rw [SimpleGraph.dist_comm, D.dist_start_alpha F i]

end D10Set

end CFSG.Quasithin.Fan86
