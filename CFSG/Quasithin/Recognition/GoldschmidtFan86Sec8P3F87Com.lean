module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P3F87Y
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P3F87Phi

public section

namespace CFSG.Quasithin.Fan86.F87

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}
  {F : FanTree Γ G} {L : ZLab Γ G} {α : V}

theorem InZ.mem_zGroup (hα : valence Γ α = 5) {e : G} (he : InZ L α e) : e ∈ L.zGroup 2 α := by
  rcases he with rfl | rfl
  · exact one_mem _
  · exact z_mem_zGroup (by simp) hα

theorem vc_sq (h7 : Fan7 F L) (h84 : Fan84a F L) (D : D10Set L α) {v c : G}
    (hv : v ∈ L.zGroup 2 α) (hc : c ∈ D.calpha) (h4 : orderOf c = 4) :
    v * c * (v * c) = L.z α := by
  have hcv : c * v = v * c :=
    ballStab_comm h7.2.2.1 (calpha_le_ballStab h7 D hc) hv
  calc v * c * (v * c) = v * (c * v) * c := by group
    _ = v * (v * c) * c := by rw [hcv]
    _ = (v * v) * (c * c) := by group
    _ = L.z α := by rw [zGroup_sq h7.2.2.1 hv, calpha_sq h7 h84 D hc h4, one_mul]

theorem solo_cases (h7 : Fan7 F L) (h84 : Fan84a F L) (D : D10Set L α) {h : G}
    (hh : h ∈ ballStab Γ G 2 α) (hord : orderOf h = 4) :
    ∃ v ∈ L.zGroup 2 α, ∃ c ∈ D.calpha, orderOf c = 4 ∧ h = v * c ∧ h * h = L.z α := by
  rcases exists_vc h7 h84 D hh with hV | ⟨v, hv, c, hc, h4, rfl⟩
  · exfalso
    have h2 : orderOf h ∣ 2 :=
      orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact zGroup_sq h7.2.2.1 hV)
    rw [hord] at h2
    omega
  · exact ⟨v, hv, c, hc, h4, rfl, vc_sq h7 h84 D hv hc h4⟩

open scoped IsMulCommutative in
theorem pair_cases (h7 : Fan7 F L) (h512 : Fan512 F L) (h83 : Fan83 F L) (h84 : Fan84a F L)
    (D : D10Set L α) {δ' : V} (hY : D.IsYPair δ') {k l : Fin 5} (hkl : k ≠ l) {h : G}
    (hh : h ∈ ballStab Γ G 2 α) :
    (h ∈ L.zGroup 2 α ∧ ∃ ε : G, (ε = 1 ∨ ε = L.z α) ∧
      (D.y δ' k * D.y δ' l * h) * (D.y δ' k * D.y δ' l * h) =
        L.z (D.alpha (kstar k l)) * L.z (D.alpha (kstar l k)) * ε) ∨
    (∃ v ∈ L.zGroup 2 α, ∃ c ∈ D.calpha, orderOf c = 4 ∧ h = v * c ∧ ∃ ε : G,
      (ε = 1 ∨ ε = L.z α) ∧
      (D.y δ' k * D.y δ' l * h) * (D.y δ' k * D.y δ' l * h) =
        L.z (D.alpha (kstar k l)) * L.z (D.alpha (kstar l k)) *
          (L.z (D.alpha k) * L.z (D.alpha l)) * ε) := by
  have h71c : Fan71c F L := h7.2.2.1
  have hα : valence Γ α = 5 := D.val
  have hyK := y_mem_nbrStab h83.1 D hY
  have hYK : D.y δ' k * D.y δ' l ∈ nbrStab Γ G α := mul_mem (hyK k) (hyK l)
  have hsq := yy_sq h7 h83.2.2.2.1 D hY hkl
  have hle := zGroup_le_stabilizer (α := α) h71c
  have hcommY : ∀ {v : G}, v ∈ L.zGroup 2 α → InZ L α (fcomm v (D.y δ' k * D.y δ' l)) :=
    fun hv => by
      rw [← fcomm_inv_eq]
      exact InZ.inv hα (fcomm_mem_Z h7 h512 hα hYK hv)
  have hzV : ∀ s, L.z (D.alpha s) ∈ L.zGroup 2 α := fun s =>
    z_mem_zGroup (by rw [D.dist_start_alpha F s]) (D.valence_alpha F s)
  rcases exists_vc h7 h84 D hh with hV | ⟨v, hv, c, hc, h4, rfl⟩
  · left
    have hε := hcommY hV
    refine ⟨hV, _, hε, ?_⟩
    have hcomm : Commute (fcomm h (D.y δ' k * D.y δ' l)) h := by
      rcases hε with he | he
      · rw [he]
        exact Commute.one_left h
      · rw [he]
        exact (L.comm_z_of_mem_stabilizer hα (hle hV)).symm
    rw [sq_mul _ _ hcomm, hsq, zGroup_sq h71c hV, mul_one]
  · right
    have hcs : c ∈ MulAction.stabilizer G α :=
      F.nbrStab_le_stabilizer α (Subgroup.mem_inf.1 hc).1
    have hcH : c ∈ ballStab Γ G 2 α := calpha_le_ballStab h7 D hc
    have hε := hcommY hv
    have hfh : fcomm (v * c) (D.y δ' k * D.y δ' l) = fcomm v (D.y δ' k * D.y δ' l) *
        (L.z (D.alpha l) * (L.z (D.alpha k) * L.z α)) := by
      rw [fcomm_mul_left, (InZ.conj hα hcs hε).1, fcomm_c_yy h7 h83 h84 D hY hc h4 hkl]
    have hzα : L.z α ∈ L.zGroup 2 α := z_mem_zGroup (by simp) hα
    have hxV : fcomm v (D.y δ' k * D.y δ' l) *
        (L.z (D.alpha l) * (L.z (D.alpha k) * L.z α)) ∈ L.zGroup 2 α :=
      mul_mem (InZ.mem_zGroup hα hε) (mul_mem (hzV l) (mul_mem (hzV k) hzα))
    have hcomm : Commute (fcomm (v * c) (D.y δ' k * D.y δ' l)) (v * c) := by
      rw [hfh]
      exact Commute.mul_right (zGroup_comm h71c hxV hv) (ballStab_comm h71c hcH hxV).symm
    refine ⟨v, hv, c, hc, h4, rfl, _, hε, ?_⟩
    rw [sq_mul _ _ hcomm, hsq, vc_sq h7 h84 D hv hc h4, hfh]
    have := isMulCommutative_zGroup (α := α) h71c
    exact congrArg Subtype.val (sq_aux (A := ↥(L.zGroup 2 α))
      ⟨L.z (D.alpha (kstar k l)), hzV _⟩ ⟨L.z (D.alpha (kstar l k)), hzV _⟩ ⟨L.z α, hzα⟩
      ⟨_, InZ.mem_zGroup hα hε⟩ ⟨L.z (D.alpha l), hzV l⟩ ⟨L.z (D.alpha k), hzV k⟩
      (Subtype.ext (L.z_mul_self hα)))

end CFSG.Quasithin.Fan86.F87
