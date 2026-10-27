module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P1D10Tr
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8Hyp
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P1S82Geo
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8Stmt1

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace D10Set

variable {L : ZLab Γ G} {α : V} (D : D10Set L α)

theorem fcomm_z_alpha_eq (F : FanTree Γ G) (h : Fan71c F L) (h512 : Fan512 F L) (j : Fin 5)
    {g : G} (hα : g • α = α) (hβ : g • D.beta j = D.beta j) (hmove : g • D.alpha j ≠ D.alpha j) :
    fcomm g (L.z (D.alpha j)) = L.z α := by
  have hα' : g⁻¹ • α = α := inv_smul_eq_iff.2 hα.symm
  have hβ' : g⁻¹ • D.beta j = D.beta j := inv_smul_eq_iff.2 hβ.symm
  have hadj : Γ.Adj (D.beta j) (g⁻¹ • D.alpha j) := by
    have := (F.adj_smul g⁻¹ (D.beta j) (D.alpha j)).2 (D.adj_beta_alpha j)
    rwa [hβ'] at this
  have hne1 : g⁻¹ • D.alpha j ≠ α := fun e => D.alpha_ne_start j (by
    apply MulAction.injective g⁻¹
    show g⁻¹ • D.alpha j = g⁻¹ • α
    rw [e, hα'])
  have hne2 : g⁻¹ • D.alpha j ≠ D.alpha j := fun e => hmove (inv_smul_eq_iff.1 e).symm
  obtain ⟨t, hts, hat, hjt⟩ := exists_third_neighbor (D.valence_beta F j)
    (D.adj_start_beta j).symm (D.adj_beta_alpha j) (D.alpha_ne_start j).symm
  have hmem : g⁻¹ • D.alpha j ∈ Γ.neighborSet (D.beta j) := hadj
  rw [hts] at hmem
  have hu : g⁻¹ • D.alpha j = t := by
    rcases hmem with h1 | h1 | h1
    · exact absurd h1 hne1
    · exact absurd h1 hne2
    · exact h1
  have h3 := h512.2.2.1 (D.beta j) α (D.alpha j) t (D.valence_beta F j) hts
    (D.alpha_ne_start j).symm hat hjt
  have hzt : L.z t = L.z (D.alpha j) * L.z α := by
    rw [eq_inv_of_mul_eq_one_right h3, mul_inv_rev, L.z_inv (D.valence_alpha F j),
      L.z_inv D.val]
  have hcomm : L.z (D.alpha j) * L.z α = L.z α * L.z (D.alpha j) :=
    h.z_comm_of_dist_le (D.valence_alpha F j) D.val (by rw [D.dist_alpha_start F j]; norm_num)
  have hz : L.z (g⁻¹ • D.alpha j) = g⁻¹ * L.z (D.alpha j) * g :=
    L.z_inv_smul g (D.valence_alpha F j)
  unfold fcomm
  rw [L.z_inv (D.valence_alpha F j)]
  calc g⁻¹ * L.z (D.alpha j) * g * L.z (D.alpha j)
      = L.z (g⁻¹ • D.alpha j) * L.z (D.alpha j) := by rw [hz]
    _ = L.z t * L.z (D.alpha j) := by rw [hu]
    _ = L.z (D.alpha j) * L.z α * L.z (D.alpha j) := by rw [hzt]
    _ = L.z α * (L.z (D.alpha j) * L.z (D.alpha j)) := by rw [hcomm, mul_assoc]
    _ = L.z α := by rw [L.z_mul_self (D.valence_alpha F j), mul_one]

theorem valence_ypair (F : FanTree Γ G) {δ' : V} (hY : D.IsYPair δ') : valence Γ δ' = 5 :=
  valence_of_dist_even F (D.valence_alpha F 0) (by rw [hY.2.2.2.2.1])

theorem y_fixed_iff (F : FanTree Γ G) (h : Fan71c F L) (h81 : Fan81 F L) {δ' : V}
    (hY : D.IsYPair δ') (i : Fin 5) {v : V} (hv : Γ.dist α v ≤ 4) :
    D.y δ' i • v = v ↔ (Γ.dist (D.alpha i) v ≤ 2 ∨ Γ.dist (D.beta i) v ≤ 2) := by
  have hZ := D.isZ2Pair_translate F h hY i
  have hF := h81 α (D.alpha i) (D.beta i) (D.delta i) ((D.x ^ i.val)⁻¹ • δ') D.val hZ
  rw [← D.y_eq F h (D.valence_ypair F hY) i] at hF
  have := Set.ext_iff.1 hF v
  exact ⟨fun hy => this.1 ⟨hv, hy⟩, fun hv' => (this.2 hv').2⟩

end D10Set

end CFSG.Quasithin.Fan86
