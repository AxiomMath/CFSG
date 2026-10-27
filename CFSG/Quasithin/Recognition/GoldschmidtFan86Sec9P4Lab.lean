module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P1D10Dist
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P1D10Refl

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace D10Set

variable {L : ZLab Γ G} {α : V} (D : D10Set L α)

theorem za_mul_self (F : FanTree Γ G) (i : Fin 5) :
    L.z (D.alpha i) * L.z (D.alpha i) = 1 :=
  L.z_mul_self (D.valence_alpha F i)

theorem za_inv (F : FanTree Γ G) (i : Fin 5) : (L.z (D.alpha i))⁻¹ = L.z (D.alpha i) :=
  L.z_inv (D.valence_alpha F i)

theorem za_comm (F : FanTree Γ G) (h : Fan71c F L) (i j : Fin 5) :
    L.z (D.alpha i) * L.z (D.alpha j) = L.z (D.alpha j) * L.z (D.alpha i) := by
  apply h.z_comm_of_dist_le (D.valence_alpha F i) (D.valence_alpha F j)
  by_cases hij : i = j
  · subst hij; simp
  · have := D.dist_vert_ne F h hij (m := 2) (m' := 2) (by norm_num) (by norm_num)
    exact this.le.trans (by norm_num)

theorem za_comm_start (F : FanTree Γ G) (h : Fan71c F L) (i : Fin 5) :
    L.z (D.alpha i) * L.z α = L.z α * L.z (D.alpha i) := by
  apply h.z_comm_of_dist_le (D.valence_alpha F i) D.val
  rw [SimpleGraph.dist_comm, D.dist_start_alpha F i]
  norm_num

theorem zd_comm_start (F : FanTree Γ G) (h : Fan71c F L) (i : Fin 5) :
    L.z (D.delta i) * L.z α = L.z α * L.z (D.delta i) := by
  apply h.z_comm_of_dist_le (D.valence_delta F i) D.val
  rw [SimpleGraph.dist_comm, D.dist_delta F i]

theorem z_delta_z_alpha (F : FanTree Γ G) (h : Fan71c F L) (k i : Fin 5) :
    L.z (D.delta k) * L.z (D.alpha i) * L.z (D.delta k) = L.z (D.alpha (2 * k - i)) := by
  have h1 : L.z (D.delta k) • D.alpha i = D.alpha (2 * k - i) :=
    D.z_delta_smul_vert F h k i (m := 2) (by norm_num)
  have h2 := L.equivariant (L.z (D.delta k)) (D.alpha i) (D.valence_alpha F i)
  rw [h1] at h2
  rw [h2, L.z_inv (D.valence_delta F k)]

end D10Set

end CFSG.Quasithin.Fan86
