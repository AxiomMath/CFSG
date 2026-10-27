module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P3Cal
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P1D10Cal

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

namespace Sec8P3

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}
  {F : FanTree Γ G} {L : ZLab Γ G} {α : V} (D : D10Set L α)

theorem z_mem_calpha_of_fan75 (h71c : Fan71c F L) (h75 : Fan75 F L) : L.z α ∈ D.calpha := by
  obtain ⟨P, -, h4, -, -, -⟩ := D.exists_arc8 F h71c (i := 2) (j := 0) (by decide)
  have h := (h75 P (by rw [h4]; exact D.val)).1
  rw [h4] at h
  have hz : L.z α ∈ ballStab Γ G 3 α := by
    rw [h]
    exact Subgroup.mem_zpowers _
  refine Subgroup.mem_inf.2 ⟨mem_nbrStab.2 fun w hw => ?_, ?_⟩
  · exact mem_ballStab.1 hz w (by rw [dist_eq_one_iff_adj.2 hw]; norm_num)
  · rw [Subgroup.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    subst hg
    exact L.comm_z_of_mem_stabilizer D.val (D.x_mem_stabilizer F h71c)

theorem finite_calpha (F : FanTree Γ G) : Finite ↥D.calpha := by
  have : Finite ↥(MulAction.stabilizer G α) := F.loc_finite α
  exact Finite.of_injective (Subgroup.inclusion (show D.calpha ≤ MulAction.stabilizer G α from
    fun g hg => F.nbrStab_le_stabilizer α (Subgroup.mem_inf.1 hg).1))
    (Subgroup.inclusion_injective _)

theorem calpha_involution (F : FanTree Γ G) (h71c : Fan71c F L) (h75 : Fan75 F L)
    (hcyc : IsCyclic ↥D.calpha) {c : G} (hc : c ∈ D.calpha) (hc2 : c * c = 1) :
    c = 1 ∨ c = L.z α := by
  have := finite_calpha D F
  have hz := z_mem_calpha_of_fan75 D h71c h75
  have hne : (1 : ↥D.calpha) ≠ ⟨L.z α, hz⟩ := fun h =>
    L.z_ne_one D.val (congrArg Subtype.val h).symm
  have hzz : (⟨L.z α, hz⟩ : ↥D.calpha) ^ 2 = 1 :=
    Subtype.ext (by simpa [pow_two] using L.z_mul_self D.val)
  rcases eq_or_eq_of_sq_eq_one hne (one_pow 2) hzz (c := (⟨c, hc⟩ : ↥D.calpha))
    (Subtype.ext (by simpa [pow_two] using hc2)) with h | h
  · exact Or.inl (congrArg Subtype.val h)
  · exact Or.inr (congrArg Subtype.val h)

theorem calpha_sq_mem (F : FanTree Γ G) (h71c : Fan71c F L) (h75 : Fan75 F L)
    (hcyc : IsCyclic ↥D.calpha) (hle : Nat.card ↥D.calpha ≤ 4) {c : G} (hc : c ∈ D.calpha) :
    c * c = 1 ∨ c * c = L.z α := by
  have := finite_calpha D F
  have hz := z_mem_calpha_of_fan75 D h71c h75
  have hzo : orderOf (⟨L.z α, hz⟩ : ↥D.calpha) = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · exact Subtype.ext (by simpa [pow_two] using L.z_mul_self D.val)
    · intro h
      exact L.z_ne_one D.val (congrArg Subtype.val h)
  have h2 : 2 ∣ Nat.card ↥D.calpha := hzo ▸ orderOf_dvd_natCard _
  have hpos : 0 < Nat.card ↥D.calpha := Nat.card_pos
  have h4 : Nat.card ↥D.calpha ∣ 4 := by
    have : Nat.card ↥D.calpha = 2 ∨ Nat.card ↥D.calpha = 4 := by omega
    rcases this with h | h
    · rw [h]
      norm_num
    · rw [h]
  have hc4 : (⟨c, hc⟩ : ↥D.calpha) ^ 4 = 1 :=
    orderOf_dvd_iff_pow_eq_one.1 ((orderOf_dvd_natCard _).trans h4)
  have hd : c * c ∈ D.calpha := mul_mem hc hc
  refine calpha_involution D F h71c h75 hcyc hd ?_
  have := congrArg Subtype.val hc4
  simp only [Subgroup.coe_pow, Subgroup.coe_one] at this
  calc c * c * (c * c) = c ^ 4 := by simp [pow_succ, mul_assoc]
    _ = 1 := this

theorem fixes_delta (F : FanTree Γ G) (h71a : Fan71a F L) (h71c : Fan71c F L) (h75 : Fan75 F L)
    (hcyc : IsCyclic ↥D.calpha) {w : G} (hwα : w • α = α) (hwβ : w • D.beta 0 = D.beta 0)
    (hw : w⁻¹ * D.x * w = D.x ^ 2) : w • D.delta 0 = D.delta 0 := by
  have hx5 : D.x ^ 5 = 1 := D.x_pow_five
  have hz2 : L.z (D.delta 0) * L.z (D.delta 0) = 1 := D.zd_mul_self F 0
  have hzx : L.z (D.delta 0) * D.x * L.z (D.delta 0) = D.x⁻¹ := D.zd_x_inv F
  have hz0β : L.z (D.delta 0) • D.beta 0 = D.beta 0 := by
    rw [h71c.z_smul_eq_iff (D.valence_delta F 0), dist_comm, D.dist_beta_delta F 0]
    norm_num
  have hvε : valence Γ (w⁻¹ • D.delta 0) = 5 := by
    rw [valence_smul F]
    exact D.valence_delta F 0
  have hzε : L.z (w⁻¹ • D.delta 0) = w⁻¹ * L.z (D.delta 0) * w :=
    L.z_inv_smul w (D.valence_delta F 0)
  set u : G := w⁻¹ * L.z (D.delta 0) * w with hu
  have hu2 : u * u = 1 := by
    calc u * u = w⁻¹ * (L.z (D.delta 0) * L.z (D.delta 0)) * w := by rw [hu]; group
      _ = 1 := by rw [hz2]; group
  have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
  have hux : u * D.x * u = D.x⁻¹ := conj_inv_conj_inv hx5 hw hz2 hzx
  have hconj : u * D.x⁻¹ * u = D.x := by
    have := congrArg (fun y => y⁻¹) hux
    simpa [mul_assoc, huinv] using this
  have hgx : (u * L.z (D.delta 0)) * D.x = D.x * (u * L.z (D.delta 0)) := by
    rw [← mul_inv_eq_iff_eq_mul, mul_inv_rev, inv_eq_of_mul_eq_one_right hz2, huinv]
    calc u * L.z (D.delta 0) * D.x * (L.z (D.delta 0) * u)
        = u * (L.z (D.delta 0) * D.x * L.z (D.delta 0)) * u := by group
      _ = D.x := by rw [hzx, hconj]
  have hwβ' : w⁻¹ • D.beta 0 = D.beta 0 := by
    rw [inv_smul_eq_iff]
    exact hwβ.symm
  have huβ : u • D.beta 0 = D.beta 0 := by
    rw [hu, mul_smul, mul_smul, hwβ, hz0β, hwβ']
  have hg : u * L.z (D.delta 0) ∈ D.calpha :=
    mem_calpha_of_comm h71c D hgx (by rw [mul_smul, hz0β, huβ])
  have hgδ := D.fix_of_mem_calpha F h71a h71c hg 0 (m := 4) le_rfl
  have hδ : (D.P 0).vert 4 = D.delta 0 := rfl
  rw [hδ, mul_smul, L.z_smul_self (D.valence_delta F 0)] at hgδ
  have hdist : Γ.dist (w⁻¹ • D.delta 0) (D.delta 0) ≤ 4 := by
    rw [← h71c.z_smul_eq_iff hvε, hzε]
    exact hgδ
  have hcomm : L.z (w⁻¹ • D.delta 0) * L.z (D.delta 0) = L.z (D.delta 0) * L.z (w⁻¹ • D.delta 0) :=
    h71c.z_comm_of_dist_le hvε (D.valence_delta F 0) hdist
  have hg2 : (u * L.z (D.delta 0)) * (u * L.z (D.delta 0)) = 1 := by
    have hu_eq : u = L.z (w⁻¹ • D.delta 0) := hzε.symm
    rw [hu_eq]
    calc L.z (w⁻¹ • D.delta 0) * L.z (D.delta 0) * (L.z (w⁻¹ • D.delta 0) * L.z (D.delta 0))
        = L.z (w⁻¹ • D.delta 0) * (L.z (D.delta 0) * L.z (w⁻¹ • D.delta 0)) * L.z (D.delta 0) := by
          group
      _ = (L.z (w⁻¹ • D.delta 0) * L.z (w⁻¹ • D.delta 0)) *
          (L.z (D.delta 0) * L.z (D.delta 0)) := by
          rw [← hcomm]
          group
      _ = 1 := by rw [L.z_mul_self hvε, hz2, mul_one]
  have hδα : D.delta 0 ≠ α := fun h => by
    have := D.dist_delta F 0
    rw [h] at this
    simp at this
  rcases calpha_involution D F h71c h75 hcyc hg hg2 with h1 | h1
  · have h2 : L.z (w⁻¹ • D.delta 0) = L.z (D.delta 0) := by
      calc L.z (w⁻¹ • D.delta 0) = L.z (w⁻¹ • D.delta 0) * (L.z (D.delta 0) * L.z (D.delta 0)) := by
            rw [hz2, mul_one]
        _ = (L.z (w⁻¹ • D.delta 0) * L.z (D.delta 0)) * L.z (D.delta 0) := by group
        _ = L.z (D.delta 0) := by rw [hzε, h1, one_mul]
    have h3 := h71c.z_injective hvε (D.valence_delta F 0) h2
    rw [inv_smul_eq_iff] at h3
    exact h3.symm
  · exfalso
    have hεδ : w⁻¹ • D.delta 0 ≠ D.delta 0 := fun heq => by
      have : u * L.z (D.delta 0) = 1 := by rw [← hzε, heq, hz2]
      rw [h1] at this
      exact L.z_ne_one D.val this
    have hεα : w⁻¹ • D.delta 0 ≠ α := fun heq => by
      apply hδα
      rw [inv_smul_eq_iff, hwα] at heq
      exact heq
    have hprod : L.z (w⁻¹ • D.delta 0) * L.z (D.delta 0) * L.z α = 1 := by
      rw [hzε, h1, L.z_mul_self D.val]
    have hnb : ¬ ∃ β, ({w⁻¹ • D.delta 0, D.delta 0, α} : Set V) = Γ.neighborSet β := by
      rintro ⟨β, hβ⟩
      have hd0 : D.delta 0 ∈ Γ.neighborSet β := hβ ▸ (by simp)
      have hα' : α ∈ Γ.neighborSet β := hβ ▸ (by simp)
      have hle : Γ.dist α (D.delta 0) ≤ 2 := by
        have := F.isTree.connected.dist_triangle (u := α) (v := β) (w := D.delta 0)
        rw [dist_eq_one_iff_adj.2 hα'.symm, dist_eq_one_iff_adj.2 hd0] at this
        omega
      rw [D.dist_delta F 0] at hle
      omega
    exact h71c.2.2 _ _ _ hvε (D.valence_delta F 0) D.val hεδ hεα hδα hnb hprod

end Sec8P3

end CFSG.Quasithin.Fan86
