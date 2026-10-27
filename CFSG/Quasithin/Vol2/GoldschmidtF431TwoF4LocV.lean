module

public import CFSG.Quasithin.Vol2.GoldschmidtF431TwoF4LocSpec
public import CFSG.Quasithin.Vol2.GoldschmidtF431Loc442Klein

public section

namespace CFSG.Quasithin.H13.F431.TwoF4

open CFSG.Quasithin CFSG.Quasithin.RuType CFSG.Quasithin.RuType.J47 CFSG.Quasithin.H13.F45Ru
  CFSG.Sporadic.Schreier.Tits CFSG.RuF45 CFSG.TwoF4Lie CFSG.TwoF4Loc CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native

local notation "TA" => CFSG.Sporadic.Schreier.Tits.titsA

open scoped Pointwise

set_option linter.unusedSectionVars false


theorem mem_A (x : ↥twoF4M) : x.1 ∈ TA :=
  (SetLike.ext_iff.1 twoF4M_eq_titsA x.1).1 x.2

theorem mem_twoF4M1_iff (x : ↥twoF4M) : x ∈ twoF4M1 ↔ x.1 0 = 0 :=
  (Subgroup.mem_subgroupOf).trans (mem_twoF4H_iff (mem_A x))

theorem mem_twoF4M2_iff (x : ↥twoF4M) : x ∈ twoF4M2 ↔ x.1 • titsLine 0 = titsLine 0 :=
  (Subgroup.mem_subgroupOf).trans (mem_twoF4N_iff (mem_A x))

theorem zM_sq : zM * zM = 1 := by
  have h := pow_orderOf_eq_one zM
  rwa [orderOf_zM, pow_two] at h

theorem zM_ne_one : zM ≠ 1 := by
  intro h
  have := orderOf_zM
  rw [h, orderOf_one] at this
  omega

theorem z1M_sq : z1M * z1M = 1 := by
  unfold z1M
  calc cM * zM * cM⁻¹ * (cM * zM * cM⁻¹) = cM * (zM * zM) * cM⁻¹ := by group
    _ = 1 := by rw [zM_sq]; group

theorem z1M_ne_one : z1M ≠ 1 := by
  intro h
  apply zM_ne_one
  unfold z1M at h
  calc zM = cM⁻¹ * (cM * zM * cM⁻¹) * cM := by group
    _ = 1 := by rw [h]; group

@[expose] noncomputable def VM : Subgroup ↥twoF4M := kleinFour zM z1M zM_sq z1M_sq V_rels.2.1

theorem mem_VM {x : ↥twoF4M} : x ∈ VM ↔ x = 1 ∨ x = zM ∨ x = z1M ∨ x = z2M := by
  rw [VM, mem_kleinFour, V_rels.1]

theorem card_VM : Nat.card VM = 4 := card_kleinFour zM_ne_one z1M_ne_one V_rels.2.2

theorem zP_eq {g g' : ↥twoF4M} (h : g.1 0 = g'.1 0) : g * zM * g⁻¹ = g' * zM * g'⁻¹ := by
  have hh : g'⁻¹ * g ∈ twoF4M1 := by
    rw [mem_twoF4M1_iff]
    show (g'.1)⁻¹ (g.1 0) = 0
    rw [h]
    simp
  rw [← cent_z_model] at hh
  have hc := Subgroup.mem_centralizer_singleton_iff.1 hh
  calc g * zM * g⁻¹ = g' * (g'⁻¹ * g * zM) * g⁻¹ := by group
    _ = g' * (zM * (g'⁻¹ * g)) * g⁻¹ := by rw [hc]
    _ = g' * zM * g'⁻¹ := by group

theorem cM_val : cM.1 = cEl.1 := rfl

theorem cMinv_apply_zero : (cM⁻¹).1 0 = cEl.1 (cEl.1 0) := by
  rw [cM_inv, Subgroup.coe_mul, Equiv.Perm.mul_apply, cM_val]

theorem mul_cM_apply (x : ↥twoF4M) : (x * cM).1 0 = x.1 (cEl.1 0) := by
  rw [Subgroup.coe_mul, Equiv.Perm.mul_apply, cM_val]

theorem mul_cMinv_apply (x : ↥twoF4M) : (x * cM⁻¹).1 0 = x.1 (cEl.1 (cEl.1 0)) := by
  rw [Subgroup.coe_mul, Equiv.Perm.mul_apply, cMinv_apply_zero]

theorem zP_mem_V {g : ↥twoF4M}
    (h : g.1 0 = 0 ∨ g.1 0 = cEl.1 0 ∨ g.1 0 = cEl.1 (cEl.1 0)) : g * zM * g⁻¹ ∈ VM := by
  rcases h with h | h | h
  · have := zP_eq (g' := 1) (by rw [h]; simp)
    rw [this]
    simp only [inv_one, mul_one, one_mul]
    exact mem_VM.2 (Or.inr (Or.inl rfl))
  · have := zP_eq (g' := cM) (by rw [h, cM_val])
    rw [this]
    exact mem_VM.2 (Or.inr (Or.inr (Or.inl rfl)))
  · have := zP_eq (g' := cM⁻¹) (by rw [h, cMinv_apply_zero])
    rw [this, inv_inv]
    exact mem_VM.2 (Or.inr (Or.inr (Or.inr rfl)))

theorem cent_t_line {x : ↥twoF4M} (hx : x ∈ Subgroup.centralizer ({tM} : Set ↥twoF4M))
    {p : Fin 1755} (hp : p ∈ titsLine 0) :
    x.1 p = 0 ∨ x.1 p = cEl.1 0 ∨ x.1 p = cEl.1 (cEl.1 0) := by
  have hN := (mem_twoF4M2_iff x).1 (cent_t_model hx)
  have : x.1 p ∈ titsLine 0 := by
    rw [← hN]
    exact Finset.smul_mem_smul_finset hp
  exact line_zero_points.2.2.2 _ this

theorem cM_mem_cent : cM ∈ Subgroup.centralizer ({tM} : Set ↥twoF4M) :=
  Subgroup.mem_centralizer_singleton_iff.2 (Subtype.ext cEl_comm)

theorem V_norm_model : ∀ x ∈ Subgroup.centralizer ({tM} : Set ↥twoF4M), ∀ v ∈ VM,
    x * v * x⁻¹ ∈ VM := by
  intro x hx v hv
  obtain ⟨hp0, hp1, hp2, -⟩ := line_zero_points
  rcases mem_VM.1 hv with rfl | rfl | rfl | rfl
  · simp
  · have := zP_mem_V (g := x) (cent_t_line hx hp0)
    simpa using this
  · have := zP_mem_V (g := x * cM) (by rw [mul_cM_apply]; exact cent_t_line hx hp1)
    unfold z1M
    simpa [mul_assoc] using this
  · have := zP_mem_V (g := x * cM⁻¹) (by rw [mul_cMinv_apply]; exact cent_t_line hx hp2)
    unfold z2M
    simpa [mul_assoc] using this

theorem V_conj_model : ∀ v ∈ VM, v ≠ 1 →
    ∃ x ∈ Subgroup.centralizer ({tM} : Set ↥twoF4M), v = x * zM * x⁻¹ := by
  intro v hv hne
  rcases mem_VM.1 hv with rfl | rfl | rfl | rfl
  · exact absurd rfl hne
  · exact ⟨1, Subgroup.one_mem _, by simp⟩
  · exact ⟨cM, cM_mem_cent, rfl⟩
  · exact ⟨cM⁻¹, Subgroup.inv_mem _ cM_mem_cent, by unfold z2M; rw [inv_inv]⟩

end CFSG.Quasithin.H13.F431.TwoF4
