module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P3F87Sib
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P1S82Geo
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P1D10Cal
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P1S82Base

public section

namespace CFSG.Quasithin.Fan86.P2c

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T CFSG.Quasithin.Fan86.F87

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}
  {F : FanTree Γ G} {L : ZLab Γ G} {α : V} (D : D10Set L α)

theorem valence_pair_fst (F : FanTree Γ G) {i : Fin 5} {l₁ l₂ : V}
    (hZ : IsZ2Pair Γ G α (D.alpha i) (D.beta i) l₁ l₂ 2) : valence Γ l₁ = 5 :=
  valence_of_dist_even F D.val (by rw [hZ.2.2.2.2.2.1])

theorem valence_pair_snd (F : FanTree Γ G) {i : Fin 5} {l₁ l₂ : V}
    (hZ : IsZ2Pair Γ G α (D.alpha i) (D.beta i) l₁ l₂ 2) : valence Γ l₂ = 5 :=
  valence_of_dist_even F D.val (by rw [hZ.2.2.2.2.2.2.1])

theorem pair_sq (h71c : Fan71c F L) {i : Fin 5} {l₁ l₂ : V}
    (hZ : IsZ2Pair Γ G α (D.alpha i) (D.beta i) l₁ l₂ 2) :
    (L.z l₁ * L.z l₂) * (L.z l₁ * L.z l₂) = 1 := by
  have h1 := valence_pair_fst D F hZ
  have h2 := valence_pair_snd D F hZ
  have hd : Γ.dist l₁ l₂ ≤ 4 := by
    have := F.isTree.connected.dist_triangle (u := l₁) (v := D.alpha i) (w := l₂)
    have e1 := hZ.2.2.2.1
    have e2 := hZ.2.2.2.2.1
    rw [SimpleGraph.dist_comm] at e1
    omega
  have hc := h71c.z_comm_of_dist_le h1 h2 hd
  calc L.z l₁ * L.z l₂ * (L.z l₁ * L.z l₂)
      = L.z l₁ * (L.z l₂ * L.z l₁) * L.z l₂ := by group
    _ = L.z l₁ * (L.z l₁ * L.z l₂) * L.z l₂ := by rw [hc]
    _ = (L.z l₁ * L.z l₁) * (L.z l₂ * L.z l₂) := by group
    _ = 1 := by rw [L.z_mul_self h1, L.z_mul_self h2, one_mul]

theorem pair_fixed_iff (h81 : Fan81 F L) {i : Fin 5} {l₁ l₂ : V}
    (hZ : IsZ2Pair Γ G α (D.alpha i) (D.beta i) l₁ l₂ 2) {v : V} (hv : Γ.dist α v ≤ 4) :
    (L.z l₁ * L.z l₂) • v = v ↔ (Γ.dist (D.alpha i) v ≤ 2 ∨ Γ.dist (D.beta i) v ≤ 2) := by
  have hF := h81 α (D.alpha i) (D.beta i) l₁ l₂ D.val hZ
  have := Set.ext_iff.1 hF v
  exact ⟨fun hy => this.1 ⟨hv, hy⟩, fun hv' => (this.2 hv').2⟩

theorem dist_beta_le_two (F : FanTree Γ G) (i : Fin 5) {w : V} (hw : Γ.Adj α w) :
    Γ.dist (D.beta i) w ≤ 2 := by
  have := F.isTree.connected.dist_triangle (u := D.beta i) (v := α) (w := w)
  have h1 := D.dist_start_beta F i
  have h2 := SimpleGraph.dist_eq_one_iff_adj.2 hw
  rw [SimpleGraph.dist_comm] at h1
  omega

theorem pair_mem_nbrStab (h81 : Fan81 F L) {i : Fin 5} {l₁ l₂ : V}
    (hZ : IsZ2Pair Γ G α (D.alpha i) (D.beta i) l₁ l₂ 2) : L.z l₁ * L.z l₂ ∈ nbrStab Γ G α :=
  mem_nbrStab.2 fun w hw => (pair_fixed_iff D h81 hZ (by
    rw [SimpleGraph.dist_eq_one_iff_adj.2 hw]; norm_num)).2 (Or.inr (dist_beta_le_two D F i hw))

theorem pair_fix_beta (h81 : Fan81 F L) {i : Fin 5} {l₁ l₂ : V}
    (hZ : IsZ2Pair Γ G α (D.alpha i) (D.beta i) l₁ l₂ 2) (j : Fin 5) :
    (L.z l₁ * L.z l₂) • D.beta j = D.beta j :=
  mem_nbrStab.1 (pair_mem_nbrStab D h81 hZ) _ (D.adj_start_beta j)

theorem pair_moves_alpha (h71c : Fan71c F L) (h81 : Fan81 F L) {i j : Fin 5} {l₁ l₂ : V}
    (hZ : IsZ2Pair Γ G α (D.alpha i) (D.beta i) l₁ l₂ 2) (hji : j ≠ i) :
    (L.z l₁ * L.z l₂) • D.alpha j ≠ D.alpha j := by
  intro hfix
  have h1 := (pair_fixed_iff D h81 hZ (by rw [D.dist_start_alpha F j]; norm_num)).1 hfix
  have h2 : Γ.dist (D.alpha i) (D.alpha j) = 4 := D.dist_alpha_alpha F h71c hji.symm
  have h3 : Γ.dist (D.beta i) (D.alpha j) = 3 := D.dist_beta_alpha_ne F h71c hji
  omega

theorem pair_alpha_third (h71c : Fan71c F L) (h81 : Fan81 F L) {i j : Fin 5} {l₁ l₂ : V}
    (hZ : IsZ2Pair Γ G α (D.alpha i) (D.beta i) l₁ l₂ 2) (hji : j ≠ i) :
    ∃ t, Γ.neighborSet (D.beta j) = {α, D.alpha j, t} ∧ α ≠ t ∧ D.alpha j ≠ t ∧
      (L.z l₁ * L.z l₂) • D.alpha j = t := by
  obtain ⟨t, hts, hat, hjt⟩ := exists_third_neighbor (D.valence_beta F j)
    (D.adj_start_beta j).symm (D.adj_beta_alpha j) (D.alpha_ne_start j).symm
  refine ⟨t, hts, hat, hjt, ?_⟩
  have hβ := pair_fix_beta D h81 hZ j
  have hα : (L.z l₁ * L.z l₂) • α = α := MulAction.mem_stabilizer_iff.1
    (F.nbrStab_le_stabilizer α (pair_mem_nbrStab D h81 hZ))
  have hadj : Γ.Adj (D.beta j) ((L.z l₁ * L.z l₂) • D.alpha j) := by
    have := (F.adj_smul (L.z l₁ * L.z l₂) (D.beta j) (D.alpha j)).2 (D.adj_beta_alpha j)
    rwa [hβ] at this
  have hmem : (L.z l₁ * L.z l₂) • D.alpha j ∈ Γ.neighborSet (D.beta j) := hadj
  rw [hts] at hmem
  have hne1 : (L.z l₁ * L.z l₂) • D.alpha j ≠ α := fun e => D.alpha_ne_start j (by
    apply MulAction.injective (L.z l₁ * L.z l₂)
    show (L.z l₁ * L.z l₂) • D.alpha j = (L.z l₁ * L.z l₂) • α
    rw [e, hα])
  rcases hmem with h1 | h1 | h1
  · exact absurd h1 hne1
  · exact absurd h1 (pair_moves_alpha D h71c h81 hZ hji)
  · exact h1

theorem calpha_mem_nbrStab_alpha (h7 : Fan7 F L) {c : G} (hc : c ∈ D.calpha) (j : Fin 5) :
    c ∈ nbrStab Γ G (D.alpha j) :=
  F.fix_two_nbrs (D.adj_beta_alpha j).symm (D.adj_alpha_xi j) (D.xi_ne_beta j).symm
    (D.fix_of_mem_calpha F h7.1 h7.2.2.1 hc j (m := 1) (by norm_num))
    (D.fix_of_mem_calpha F h7.1 h7.2.2.1 hc j (m := 3) (by norm_num))

theorem fcomm_pair_mem (h7 : Fan7 F L) (h512 : Fan512 F L) {i : Fin 5} {l₁ l₂ : V}
    (hZ : IsZ2Pair Γ G α (D.alpha i) (D.beta i) l₁ l₂ 2) {c : G} (hc : c ∈ D.calpha) :
    InZ L (D.alpha i) (fcomm (L.z l₁ * L.z l₂) c) := by
  have h71c : Fan71c F L := h7.2.2.1
  have hα := D.valence_alpha F i
  have hcK : c ∈ nbrStab Γ G (D.alpha i) := calpha_mem_nbrStab_alpha D h7 hc i
  have hl : ∀ l, valence Γ l = 5 → Γ.dist (D.alpha i) l = 2 → InZ L (D.alpha i) (fcomm (L.z l) c) :=
    fun l hl5 hd => by
      rw [← fcomm_inv_eq]
      exact InZ.inv hα (fcomm_z_mem h7 h512 hα hcK (le_of_eq hd) hl5)
  have hs2 : L.z l₂ ∈ MulAction.stabilizer G (D.alpha i) :=
    (h71c.z_mem_stabilizer_iff (valence_pair_snd D F hZ) (D.alpha i)).2 (by
      rw [SimpleGraph.dist_comm, hZ.2.2.2.2.1]; norm_num)
  have e1 := hl _ (valence_pair_fst D F hZ) hZ.2.2.2.1
  have e2 := hl _ (valence_pair_snd D F hZ) hZ.2.2.2.2.1
  rw [fcomm_mul_left, (InZ.conj hα hs2 e1).1]
  exact InZ.mul hα e1 e2

end CFSG.Quasithin.Fan86.P2c
