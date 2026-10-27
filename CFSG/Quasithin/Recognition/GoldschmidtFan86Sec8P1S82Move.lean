module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P1S82a

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace D10Set

variable {L : ZLab Γ G} {α : V} (D : D10Set L α)

theorem not_mem_nbrStab_delta (F : FanTree Γ G) (h : Fan71c F L) {i j m : Fin 5} (hmi : i ≠ m)
    (hmid : 2 * m - i = j) :
    L.z (D.alpha i) * L.z (D.alpha j) ∉ nbrStab Γ G (D.delta m) := by
  intro hK
  have hne : (Γ.neighborSet (D.delta m) \ {D.xi m}).Nonempty := by
    apply Set.nonempty_of_ncard_ne_zero
    rw [neighborSet_diff_ncard (D.valence_delta F m) (D.adj_xi_delta m).symm]
    norm_num
  obtain ⟨e, he, hexi⟩ := hne
  have hexi' : D.xi m ≠ e := fun e' => hexi (by rw [e']; rfl)
  have hza : L.z (D.alpha i) • D.alpha m = D.alpha m :=
    (h.z_smul_eq_iff (D.valence_alpha F i) _).2 (by rw [D.dist_alpha_alpha F h hmi])
  have hzξ : L.z (D.alpha i) • D.xi m ≠ D.xi m := fun e' => by
    have h5 := (h.z_smul_eq_iff (D.valence_alpha F i) _).1 e'
    have := D.dist_vert_ne F h hmi (m := 2) (m' := 3) (by norm_num) (by norm_num)
    have h6 : Γ.dist (D.alpha i) (D.xi m) = 5 := this
    omega
  have hadj1 : Γ.Adj (D.alpha m) (L.z (D.alpha i) • D.xi m) := by
    have := (F.adj_smul (L.z (D.alpha i)) (D.alpha m) (D.xi m)).2 (D.adj_alpha_xi m)
    rwa [hza] at this
  have hadj2 : Γ.Adj (L.z (D.alpha i) • D.xi m) (L.z (D.alpha i) • D.delta m) :=
    (F.adj_smul _ _ _).2 (D.adj_xi_delta m)
  have hd1 : Γ.dist (L.z (D.alpha i) • D.delta m) (D.alpha m) = 2 := by
    have := dist_smul F (L.z (D.alpha i)) (D.delta m) (D.alpha m)
    rw [hza, SimpleGraph.dist_comm (u := D.delta m), D.dist_alpha_delta F m] at this
    exact this
  have hd2 : Γ.dist (L.z (D.alpha i) • D.delta m) (D.xi m) = 3 := by
    have h1 : Γ.dist (L.z (D.alpha i) • D.delta m) (L.z (D.alpha i) • D.xi m) = 1 := by
      rw [SimpleGraph.dist_comm]
      exact dist_eq_one_iff_adj.2 hadj2
    have := IsTree.dist_succ_of_ne F.isTree hadj1 (D.adj_alpha_xi m) hzξ
      (by rw [h1, hd1])
    rw [this, hd1]
  have hd3 : Γ.dist (L.z (D.alpha i) • D.delta m) (D.delta m) = 4 := by
    have := IsTree.dist_succ_of_ne F.isTree (D.adj_alpha_xi m).symm (D.adj_xi_delta m)
      (D.delta_ne_alpha m).symm (by rw [hd1, hd2])
    rw [this, hd2]
  have hd4 : Γ.dist (L.z (D.alpha i) • D.delta m) e = 5 := by
    have := IsTree.dist_succ_of_ne F.isTree (D.adj_xi_delta m).symm he hexi' (by rw [hd2, hd3])
    rw [this, hd3]
  have hvδ : valence Γ (L.z (D.alpha i) • D.delta m) = 5 := by
    rw [valence_smul F]
    exact D.valence_delta F m
  have hj : L.z (D.alpha j) = L.z (D.delta m) * L.z (D.alpha i) * L.z (D.delta m) := by
    have := D.z_delta_conj_alpha F h m i
    rw [hmid, L.z_inv (D.valence_delta F m)] at this
    exact this.symm
  have hid : L.z (D.alpha i) * L.z (D.alpha j) =
      L.z (L.z (D.alpha i) • D.delta m) * L.z (D.delta m) := by
    rw [L.equivariant _ _ (D.valence_delta F m), hj, L.z_inv (D.valence_alpha F i)]
    group
  have hfix := mem_nbrStab.1 hK e he
  have hze : L.z (D.delta m) • e = e := (h.z_smul_eq_iff (D.valence_delta F m) e).2 (by
    rw [dist_eq_one_iff_adj.2 he]; norm_num)
  rw [hid, mul_smul, hze] at hfix
  have := (h.z_smul_eq_iff hvδ e).1 hfix
  omega

end D10Set

end CFSG.Quasithin.Fan86
