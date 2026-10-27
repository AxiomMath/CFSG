module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P1S82Geo
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P1S82Base
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P2cNbr
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P3F87V

public section

namespace CFSG.Quasithin.Fan86.P2d1

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T CFSG.Quasithin.Fan86.F87

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}
  {F : FanTree Γ G} {L : ZLab Γ G} {α : V} (D : D10Set L α)

theorem dist_far (h71c : Fan71c F L) {a k : Fin 5} (hak : a ≠ k) {c e : V}
    (hβc : Γ.Adj (D.beta k) c) (hcα : c ≠ α) (hce : Γ.Adj c e) (heβ : e ≠ D.beta k) :
    Γ.dist (D.alpha a) c = 4 ∧ Γ.dist (D.alpha a) e = 5 := by
  have h1 : Γ.dist (D.alpha a) (D.beta k) = 3 := by
    rw [SimpleGraph.dist_comm]
    exact D.dist_beta_alpha_ne F h71c hak
  have h2 : Γ.dist (D.alpha a) α = 2 := D.dist_alpha_start F a
  have h3 := IsTree.dist_succ_of_ne F.isTree (D.adj_start_beta k).symm hβc
    (fun h => hcα h.symm) (w := D.alpha a) (by omega)
  have h4 := IsTree.dist_succ_of_ne F.isTree hβc.symm hce (fun h => heβ h.symm)
    (w := D.alpha a) (by omega)
  omega

theorem labels_mem_nbrStab (h71c : Fan71c F L) {a b k : Fin 5} (hak : a ≠ k) (hbk : b ≠ k)
    {c e : V} (hβc : Γ.Adj (D.beta k) c) (hcα : c ≠ α) (hce : Γ.Adj c e) (heβ : e ≠ D.beta k) :
    L.z (D.alpha a) * L.z (D.alpha b) ∈ nbrStab Γ G c := by
  obtain ⟨ha1, ha2⟩ := dist_far D h71c hak hβc hcα hce heβ
  obtain ⟨hb1, hb2⟩ := dist_far D h71c hbk hβc hcα hce heβ
  have hA : Γ.dist (D.alpha a) (D.beta k) = 3 := by
    rw [SimpleGraph.dist_comm]
    exact D.dist_beta_alpha_ne F h71c hak
  have hB : Γ.dist (D.alpha b) (D.beta k) = 3 := by
    rw [SimpleGraph.dist_comm]
    exact D.dist_beta_alpha_ne F h71c hbk
  exact mul_z_mem_nbrStab F h71c (D.valence_alpha F a) (D.valence_alpha F b) hβc.symm hce
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)

theorem labels_mem_ballStab_two (h7 : Fan7 F L) {a b k : Fin 5} (hak : a ≠ k) (hbk : b ≠ k) :
    L.z (D.alpha a) * L.z (D.alpha b) ∈ ballStab Γ G 2 (D.beta k) := by
  have h71c : Fan71c F L := h7.2.2.1
  have hzV : ∀ s, L.z (D.alpha s) ∈ L.zGroup 2 α := fun s =>
    z_mem_zGroup (by rw [D.dist_start_alpha F s]) (D.valence_alpha F s)
  have hpH : L.z (D.alpha a) * L.z (D.alpha b) ∈ ballStab Γ G 2 α :=
    zGroup_le_ballStab h7 D (mul_mem (hzV a) (hzV b))
  have hfix : ∀ w, Γ.dist α w ≤ 2 → (L.z (D.alpha a) * L.z (D.alpha b)) • w = w :=
    fun w hw => mem_ballStab.1 hpH w hw
  refine P2c.mem_ballStab_two_of F (hfix _ (by rw [D.dist_start_beta F]; norm_num)) fun u hu => ?_
  obtain ⟨t, hts, hαt, hkt⟩ := exists_third_neighbor (D.valence_beta F k)
    (D.adj_start_beta k).symm (D.adj_beta_alpha k) (D.alpha_ne_start k).symm
  have hmem : u ∈ Γ.neighborSet (D.beta k) := hu
  rw [hts] at hmem
  rcases hmem with rfl | rfl | rfl
  · exact ⟨hfix _ (by rw [SimpleGraph.dist_self]; norm_num),
      mem_nbrStab.2 fun w hw => hfix w (by rw [SimpleGraph.dist_eq_one_iff_adj.2 hw]; norm_num)⟩
  · refine ⟨hfix _ (by rw [D.dist_start_alpha F]), ?_⟩
    exact labels_mem_nbrStab D h71c hak hbk hu (D.alpha_ne_start k) (D.adj_alpha_xi k)
      (D.xi_ne_beta k)
  · obtain ⟨e, het, heβ⟩ := F.exists_adj_ne u (D.beta k)
    refine ⟨hfix _ ?_, labels_mem_nbrStab D h71c hak hbk hu (Ne.symm hαt) het heβ⟩
    have := F.isTree.connected.dist_triangle (u := α) (v := D.beta k) (w := u)
    have h1 := D.dist_start_beta F k
    have h2 : Γ.dist (D.beta k) u = 1 := SimpleGraph.dist_eq_one_iff_adj.2 hu
    omega

end CFSG.Quasithin.Fan86.P2d1
