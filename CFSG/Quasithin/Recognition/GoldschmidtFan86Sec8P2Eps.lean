module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P1S82a
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P2V2
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P2Y

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

theorem fin5_kstar_mid : ∀ i j : Fin 5, i ≠ j →
    2 * midlab i j - kstar i j = kstar j i ∧ 2 * midlab i j - kstar j i = kstar i j := by
  unfold midlab kstar
  decide

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace D10Set

variable {L : ZLab Γ G} {α : V} (D : D10Set L α)

theorem z_pair_eq_conj (F : FanTree Γ G) (h : Fan71c F L) {a b m : Fin 5}
    (hb : 2 * m - a = b) :
    L.z (D.alpha a) * L.z (D.alpha b) = L.z (L.z (D.alpha a) • D.delta m) * L.z (D.delta m) := by
  have hj : L.z (D.alpha b) = L.z (D.delta m) * L.z (D.alpha a) * L.z (D.delta m) := by
    have := D.z_delta_conj_alpha F h m a
    rw [hb, L.z_inv (D.valence_delta F m)] at this
    exact this.symm
  rw [L.equivariant _ _ (D.valence_delta F m), hj, L.z_inv (D.valence_alpha F a)]
  group

theorem fcomm_y_ne_mul_z (F : FanTree Γ G) (h7 : Fan7 F L) (h81 : Fan81 F L) {δ' : V}
    (hY : D.IsYPair δ') {i j : Fin 5} (hij : i ≠ j) :
    fcomm (D.y δ' i) (D.y δ' j) ≠
      (L.z (D.alpha (kstar i j)) * L.z (D.alpha (kstar j i))) * L.z α := by
  intro hv
  have h71c : Fan71c F L := h7.2.2.1
  obtain ⟨⟨-, -, hi1, hi2, hi3, hj1, hj2, hj3, hij'⟩, ⟨hmid, hmid2⟩, -⟩ :=
    fin5_midlab_facts i j hij
  obtain ⟨hk1, hk2⟩ := fin5_kstar_mid i j hij
  have hzm2 := L.z_mul_self (D.valence_delta F (midlab i j))
  have hyi := D.y_mul_self' F h71c hY i
  have hyj := D.y_mul_self' F h71c hY j
  have hyi' : (D.y δ' i)⁻¹ = D.y δ' i := inv_eq_of_mul_eq_one_right hyi
  have hyj' : (D.y δ' j)⁻¹ = D.y δ' j := inv_eq_of_mul_eq_one_right hyj
  have hr1 : L.z (D.delta (midlab i j)) * D.y δ' i * L.z (D.delta (midlab i j)) = D.y δ' j := by
    rw [D.y_refl F h71c hY (midlab i j) i, hmid]
  have hr2 : L.z (D.delta (midlab i j)) * D.y δ' j * L.z (D.delta (midlab i j)) = D.y δ' i := by
    rw [D.y_refl F h71c hY (midlab i j) j, hmid2]
  have hu : L.z (D.delta (midlab i j)) * (D.y δ' i * D.y δ' j) * L.z (D.delta (midlab i j)) =
      (D.y δ' i * D.y δ' j)⁻¹ := by
    have e : (L.z (D.delta (midlab i j)) * D.y δ' i * L.z (D.delta (midlab i j))) *
        (L.z (D.delta (midlab i j)) * D.y δ' j * L.z (D.delta (midlab i j))) =
        L.z (D.delta (midlab i j)) * (D.y δ' i * D.y δ' j) * L.z (D.delta (midlab i j)) := by
      calc _ = L.z (D.delta (midlab i j)) * D.y δ' i * (L.z (D.delta (midlab i j)) *
            L.z (D.delta (midlab i j))) * D.y δ' j * L.z (D.delta (midlab i j)) := by group
        _ = _ := by rw [hzm2]; group
    rw [← e, hr1, hr2, mul_inv_rev, hyi', hyj']
  have hvu : fcomm (D.y δ' i) (D.y δ' j) = (D.y δ' i * D.y δ' j) * (D.y δ' i * D.y δ' j) := by
    rw [D.fcomm_y_eq F h71c hY]
    group
  have hvδ : valence Γ (D.delta (midlab i j)) = 5 := D.valence_delta F _
  have hvinv : L.z ((D.y δ' i * D.y δ' j)⁻¹ • D.delta (midlab i j)) * L.z (D.delta (midlab i j)) =
      (fcomm (D.y δ' i) (D.y δ' j))⁻¹ := by
    rw [L.z_inv_smul _ hvδ, hvu, mul_inv_rev, ← mul_inv_rev]
    calc (D.y δ' i * D.y δ' j)⁻¹ * L.z (D.delta (midlab i j)) * (D.y δ' i * D.y δ' j) *
          L.z (D.delta (midlab i j))
        = (D.y δ' i * D.y δ' j)⁻¹ * (L.z (D.delta (midlab i j)) * (D.y δ' i * D.y δ' j) *
          L.z (D.delta (midlab i j))) := by group
      _ = (D.y δ' i * D.y δ' j)⁻¹ * (D.y δ' i * D.y δ' j)⁻¹ := by rw [hu]
      _ = _ := by rw [← mul_inv_rev]
  have hcommα : ∀ s : Fin 5, L.z α * L.z (D.alpha s) = L.z (D.alpha s) * L.z α := fun s =>
    h71c.z_comm_of_dist_le D.val (D.valence_alpha F s)
      (by rw [D.dist_start_alpha F s]; norm_num)
  have hcommzz : ∀ s t : Fin 5,
      L.z (D.alpha s) * L.z (D.alpha t) = L.z (D.alpha t) * L.z (D.alpha s) := by
    intro s t
    by_cases hst : s = t
    · rw [hst]
    · exact h71c.z_comm_of_dist_le (D.valence_alpha F s) (D.valence_alpha F t)
        (by rw [D.dist_alpha_alpha F h71c hst])
  have hzs : ∀ s : Fin 5, L.z (D.alpha s) * L.z (D.alpha s) = 1 :=
    fun s => L.z_mul_self (D.valence_alpha F s)
  have hzα2 := L.z_mul_self D.val
  have hgg : (L.z (D.alpha (kstar i j)) * L.z (D.alpha (kstar j i))) *
      (L.z (D.alpha (kstar i j)) * L.z (D.alpha (kstar j i))) = 1 := by
    calc _ = L.z (D.alpha (kstar i j)) * (L.z (D.alpha (kstar j i)) *
          L.z (D.alpha (kstar i j))) * L.z (D.alpha (kstar j i)) := by group
      _ = L.z (D.alpha (kstar i j)) * (L.z (D.alpha (kstar i j)) *
          L.z (D.alpha (kstar j i))) * L.z (D.alpha (kstar j i)) := by
        rw [hcommzz (kstar j i) (kstar i j)]
      _ = (L.z (D.alpha (kstar i j)) * L.z (D.alpha (kstar i j))) *
          (L.z (D.alpha (kstar j i)) * L.z (D.alpha (kstar j i))) := by group
      _ = 1 := by rw [hzs, hzs, one_mul]
  have hgz : L.z α * (L.z (D.alpha (kstar i j)) * L.z (D.alpha (kstar j i))) =
      (L.z (D.alpha (kstar i j)) * L.z (D.alpha (kstar j i))) * L.z α := by
    rw [← mul_assoc, hcommα, mul_assoc, hcommα, ← mul_assoc]
  have hgα : ((L.z (D.alpha (kstar i j)) * L.z (D.alpha (kstar j i))) * L.z α) *
      ((L.z (D.alpha (kstar i j)) * L.z (D.alpha (kstar j i))) * L.z α) = 1 := by
    calc _ = (L.z (D.alpha (kstar i j)) * L.z (D.alpha (kstar j i))) *
          (L.z α * (L.z (D.alpha (kstar i j)) * L.z (D.alpha (kstar j i)))) * L.z α := by group
      _ = ((L.z (D.alpha (kstar i j)) * L.z (D.alpha (kstar j i))) *
          (L.z (D.alpha (kstar i j)) * L.z (D.alpha (kstar j i)))) * (L.z α * L.z α) := by
        rw [hgz]; group
      _ = 1 := by rw [hgg, hzα2, one_mul]
  have h1 : L.z ((D.y δ' i * D.y δ' j)⁻¹ • D.delta (midlab i j)) * L.z (D.delta (midlab i j)) =
      (L.z (D.alpha (kstar i j)) * L.z (D.alpha (kstar j i))) * L.z α := by
    rw [hvinv, hv]
    exact inv_eq_of_mul_eq_one_right hgα
  have hgd := D.z_pair_eq_conj F h71c (a := kstar i j) (b := kstar j i) (m := midlab i j) hk1
  have hzmα : L.z (D.delta (midlab i j)) * L.z α = L.z α * L.z (D.delta (midlab i j)) :=
    h71c.z_comm_of_dist_le hvδ D.val (by rw [SimpleGraph.dist_comm, D.dist_delta F])
  have h2 : L.z ((D.y δ' i * D.y δ' j)⁻¹ • D.delta (midlab i j)) =
      L.z (L.z (D.alpha (kstar i j)) • D.delta (midlab i j)) * L.z α := by
    calc L.z ((D.y δ' i * D.y δ' j)⁻¹ • D.delta (midlab i j))
        = L.z ((D.y δ' i * D.y δ' j)⁻¹ • D.delta (midlab i j)) * L.z (D.delta (midlab i j)) *
          L.z (D.delta (midlab i j)) := by rw [mul_assoc, hzm2, mul_one]
      _ = ((L.z (L.z (D.alpha (kstar i j)) • D.delta (midlab i j)) *
          L.z (D.delta (midlab i j))) * L.z α) * L.z (D.delta (midlab i j)) := by
        rw [h1, hgd]
      _ = L.z (L.z (D.alpha (kstar i j)) • D.delta (midlab i j)) * (L.z (D.delta (midlab i j)) *
          L.z α) * L.z (D.delta (midlab i j)) := by group
      _ = L.z (L.z (D.alpha (kstar i j)) • D.delta (midlab i j)) * L.z α *
          (L.z (D.delta (midlab i j)) * L.z (D.delta (midlab i j))) := by rw [hzmα]; group
      _ = _ := by rw [hzm2, mul_one]
  have hyα : ∀ k, D.y δ' k • α = α := D.y_fixes_alpha_start F h71c h81 hY
  have huα : (D.y δ' i * D.y δ' j)⁻¹ • α = α := by
    refine inv_smul_eq_iff.2 ?_
    rw [mul_smul, hyα j, hyα i]
  have hzaα : L.z (D.alpha (kstar i j)) • α = α :=
    (h71c.z_smul_eq_iff (D.valence_alpha F _) α).2 (by rw [D.dist_alpha_start F]; norm_num)
  have hdα' : Γ.dist α (L.z (D.alpha (kstar i j)) • D.delta (midlab i j)) = 4 := by
    have := dist_smul F (L.z (D.alpha (kstar i j))) α (D.delta (midlab i j))
    rw [hzaα, D.dist_delta F] at this
    exact this
  have hdû : Γ.dist α ((D.y δ' i * D.y δ' j)⁻¹ • D.delta (midlab i j)) = 4 := by
    have := dist_smul F (D.y δ' i * D.y δ' j)⁻¹ α (D.delta (midlab i j))
    rw [huα, D.dist_delta F] at this
    exact this
  have hv1 : valence Γ (L.z (D.alpha (kstar i j)) • D.delta (midlab i j)) = 5 := by
    rw [valence_smul F]
    exact hvδ
  have hv2 : valence Γ ((D.y δ' i * D.y δ' j)⁻¹ • D.delta (midlab i j)) = 5 := by
    rw [valence_smul F]
    exact hvδ
  have hzd2 := L.z_mul_self hv1
  refine h71c.2.2 _ _ α hv1 hv2 D.val ?_ ?_ ?_ ?_ ?_
  · intro e
    have h := h2
    rw [← e] at h
    exact L.z_ne_one D.val (mul_eq_left.1 h.symm)
  · intro e
    rw [e, SimpleGraph.dist_self] at hdα'
    omega
  · intro e
    rw [e, SimpleGraph.dist_self] at hdû
    omega
  · rintro ⟨β, hβ⟩
    have ha : α ∈ Γ.neighborSet β := by rw [← hβ]; simp
    have hd : L.z (D.alpha (kstar i j)) • D.delta (midlab i j) ∈ Γ.neighborSet β := by
      rw [← hβ]; simp
    have h5 := dist_eq_one_iff_adj.2 ha
    have h6 := dist_eq_one_iff_adj.2 hd
    have h7' := F.isTree.connected.dist_triangle (u := α) (v := β)
      (w := L.z (D.alpha (kstar i j)) • D.delta (midlab i j))
    rw [SimpleGraph.dist_comm (u := α) (v := β)] at h7'
    omega
  · rw [h2]
    calc L.z (L.z (D.alpha (kstar i j)) • D.delta (midlab i j)) *
          (L.z (L.z (D.alpha (kstar i j)) • D.delta (midlab i j)) * L.z α) * L.z α
        = (L.z (L.z (D.alpha (kstar i j)) • D.delta (midlab i j)) *
          L.z (L.z (D.alpha (kstar i j)) • D.delta (midlab i j))) * (L.z α * L.z α) := by
          group
      _ = 1 := by rw [hzd2, hzα2, one_mul]

end D10Set

end CFSG.Quasithin.Fan86
