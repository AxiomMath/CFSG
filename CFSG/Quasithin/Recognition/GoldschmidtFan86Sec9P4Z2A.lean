module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P1S82Base

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem fin5_pair_cond : ∀ i j k : Fin 5, j ≠ i → k ≠ i → j ≠ k → 2 * i ≠ j + k →
    k - i ≠ j - i ∧ k - i ≠ -(j - i) := by decide

namespace D10Set

variable {L : ZLab Γ G} {α : V} (D : D10Set L α) (F : FanTree Γ G) (h : Fan71c F L)

include F h

theorem isZ2Pair_alpha_lam {i j k : Fin 5} (hji : j ≠ i) (hki : k ≠ i) (hjk : j ≠ k)
    (hk2 : 2 * i ≠ j + k) {lam : V} (hl : Γ.Adj (D.beta i) lam) (hlα : lam ≠ α) :
    IsZ2Pair Γ G lam α (D.beta i) (D.alpha j) (D.alpha k) 2 := by
  obtain ⟨-, -, -, -, -, -, -, hnot⟩ :=
    D.isZ2Pair_alpha F h hji hki (fin5_pair_cond i j k hji hki hjk hk2)
  have hT := F.isTree
  have hlb : Γ.dist lam (D.beta i) = 1 := dist_eq_one_iff_adj.2 hl.symm
  have hl0 : Γ.dist lam lam + 1 = Γ.dist lam (D.beta i) := by rw [dist_self, hlb]
  have hd2 : Γ.dist lam α = 2 := by
    have := IsTree.dist_succ_of_ne hT hl (D.adj_start_beta i).symm hlα hl0
    rw [this, hlb]
  have hbi : ∀ m : Fin 5, i ≠ m → Γ.dist lam (D.alpha m) = 4 := fun m him => by
    have hb : Γ.dist lam (D.beta m) = 3 := by
      have := IsTree.dist_succ_of_ne hT (D.adj_start_beta i) (D.adj_start_beta m)
        (fun h' => him (D.beta_injective F h h')) (by rw [hlb, hd2])
      rw [this, hd2]
    have := IsTree.dist_succ_of_ne hT (D.adj_start_beta m).symm (D.adj_beta_alpha m)
      (D.alpha_ne_start m).symm (by rw [hd2, hb])
    rw [this, hb]
  exact ⟨hd2, D.adj_start_beta i, by rw [hlb, hd2], D.dist_start_alpha F j,
    D.dist_start_alpha F k, hbi j hji.symm, hbi k hki.symm, hnot⟩

omit h in
theorem zAlpha_ne_one (i : Fin 5) : L.z (D.alpha i) ≠ 1 := L.z_ne_one (D.valence_alpha F i)

theorem alpha_ne_alpha {i j : Fin 5} (hij : i ≠ j) : D.alpha i ≠ D.alpha j := fun h' => by
  have := D.dist_alpha_alpha F h hij
  rw [h', dist_self] at this
  omega

theorem zAlpha_ne {i j : Fin 5} (hij : i ≠ j) : L.z (D.alpha i) ≠ L.z (D.alpha j) := fun h' =>
  D.alpha_ne_alpha F h hij (h.z_injective (D.valence_alpha F i) (D.valence_alpha F j) h')

theorem zAlpha_ne_zStart (i : Fin 5) : L.z (D.alpha i) ≠ L.z α := fun h' =>
  D.alpha_ne_start i (h.z_injective (D.valence_alpha F i) D.val h')

theorem zAlpha_prod_ne_one {i j : Fin 5} (hij : i ≠ j) :
    L.z (D.alpha i) * L.z (D.alpha j) * L.z α ≠ 1 := by
  refine h.2.2 _ _ _ (D.valence_alpha F i) (D.valence_alpha F j) D.val (D.alpha_ne_alpha F h hij)
    (D.alpha_ne_start i) (D.alpha_ne_start j) ?_
  rintro ⟨b, hb⟩
  have hi : D.alpha i ∈ Γ.neighborSet b := by rw [← hb]; simp
  have hj : D.alpha j ∈ Γ.neighborSet b := by rw [← hb]; simp
  have h1 := F.isTree.connected.dist_triangle (u := D.alpha i) (v := b) (w := D.alpha j)
  have h2 : Γ.dist (D.alpha i) b = 1 := dist_eq_one_iff_adj.2 hi.symm
  have h3 : Γ.dist b (D.alpha j) = 1 := dist_eq_one_iff_adj.2 hj
  have := D.dist_alpha_alpha F h hij
  omega

end D10Set

end CFSG.Quasithin.Fan86
