module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P1Geo
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P1Lab
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P3ExArc
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P3ExDih

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace P4X

theorem exists_d10Set_arcs {F : FanTree Γ G} {L : ZLab Γ G} (h71a : Fan71a F L)
    (h71c : Fan71c F L) {α : V} (hα : valence Γ α = 5) (Q₀ Q₂ : Arc Γ 4) (h0 : Q₀.vert 0 = α)
    (h2 : Q₂.vert 0 = α) (hne : Q₀.vert 1 ≠ Q₂.vert 1) :
    ∃ D : D10Set L α, (∀ m, m ≤ 4 → (D.P 0).vert m = Q₀.vert m) ∧
      ∀ m, m ≤ 4 → (D.P 2).vert m = Q₂.vert m := by
  have hT := F.isTree
  have hd0 : Γ.dist α (Q₀.vert 4) = 4 := by
    have := Arc.dist_eq hT Q₀ 4 le_rfl
    rwa [h0] at this
  have hd2 : Γ.dist α (Q₂.vert 4) = 4 := by
    have := Arc.dist_eq hT Q₂ 4 le_rfl
    rwa [h2] at this
  have h05 : valence Γ (Q₀.vert 4) = 5 := valence_of_dist_even F hα (by rw [hd0])
  have h25 : valence Γ (Q₂.vert 4) = 5 := valence_of_dist_even F hα (by rw [hd2])
  obtain ⟨s, hs_def⟩ : ∃ s, s = L.z (Q₀.vert 4) := ⟨_, rfl⟩
  have hs2 : s * s = 1 := hs_def ▸ L.z_mul_self h05
  have hsα : s ∈ MulAction.stabilizer G α := hs_def ▸
    (h71c.z_mem_stabilizer_iff h05 α).2 (by rw [SimpleGraph.dist_comm, hd0])
  have hsα' : s • α = α := MulAction.mem_stabilizer_iff.1 hsα
  have hs1 : s • Q₀.vert 1 = Q₀.vert 1 := by
    rw [hs_def]
    refine (h71c.z_smul_eq_iff h05 _).2 ?_
    have := Arc.dist_vert hT Q₀ (i := 1) (j := 4) (by norm_num) le_rfl
    rw [dist_comm]
    omega
  have hQ1₀ : (Arc.act F s Q₂).vert 0 = Q₀.vert 0 := by
    rw [Arc.act_vert, h2, h0, hsα']
  have hQ1₁ : (Arc.act F s Q₂).vert 1 ≠ Q₀.vert 1 := fun h => hne (by
    rw [Arc.act_vert] at h
    exact (MulAction.injective s (h.trans hs1.symm)).symm)
  obtain ⟨R, hR0, hR4, hR8⟩ := exists_arc_eight hQ1₀ hQ1₁
  rw [Arc.act_vert] at hR0 hR4
  rw [h2, hsα'] at hR4
  have hv0 : valence Γ (R.vert 0) = 5 := by
    rw [hR0, valence_smul F]
    exact h25
  have hφ := (h71a R hv0).1
  rw [hR0, hR8] at hφ
  obtain ⟨φ⟩ := hφ
  have hse : valence Γ (s • Q₂.vert 4) = 5 := by
    rw [valence_smul F]
    exact h25
  obtain ⟨e, he_def⟩ : ∃ e, e = L.z (s • Q₂.vert 4) := ⟨_, rfl⟩
  have he2 : e * e = 1 := he_def ▸ L.z_mul_self hse
  have hne' : s ≠ e := fun h => by
    have h' := h71c.z_injective h05 hse (hs_def ▸ he_def ▸ h)
    have := Arc.vert_injOn hT R (i := 0) (j := 8) (by norm_num) (by norm_num)
      (by rw [hR0, hR8]; exact h'.symm)
    omega
  have hφ' : Nonempty (↥(Subgroup.closure ({e, s} : Set G)) ≃* DihedralGroup 5) := by
    have hset : ({e, s} : Set G) = {L.z (s • Q₂.vert 4), L.z (Q₀.vert 4)} := by
      rw [← he_def, ← hs_def]
    rw [hset]
    exact ⟨φ⟩
  obtain ⟨φ'⟩ := hφ'
  have hr := dihedral_orderOf_rot hs2 he2 (hs_def ▸ L.z_ne_one h05) (he_def ▸ L.z_ne_one hse)
    hne' φ'
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs2
  have he_eq : e = s * L.z (Q₂.vert 4) * s := by
    rw [he_def, L.equivariant s _ h25, hsinv]
  have hrdef : s * e = L.z (Q₂.vert 4) * s := by
    rw [he_eq]
    calc s * (s * L.z (Q₂.vert 4) * s) = (s * s) * L.z (Q₂.vert 4) * s := by group
      _ = L.z (Q₂.vert 4) * s := by rw [hs2, one_mul]
  have hz2α : L.z (Q₂.vert 4) ∈ MulAction.stabilizer G α :=
    (h71c.z_mem_stabilizer_iff h25 α).2 (by rw [SimpleGraph.dist_comm, hd2])
  have hrα : s * e ∈ MulAction.stabilizer G α := by
    rw [hrdef]
    exact Subgroup.mul_mem _ hz2α hsα
  have hinv : ∀ i : Fin 5, ((s * e) ^ (i : ℕ))⁻¹ ∈ MulAction.stabilizer G α := fun i =>
    inv_mem (Subgroup.pow_mem _ hrα _)
  let P : Fin 5 → Arc Γ 4 := fun i => Arc.act F (((s * e) ^ (i : ℕ))⁻¹) Q₀
  have hstart : ∀ i, (P i).vert 0 = α := fun i => by
    show ((s * e) ^ (i : ℕ))⁻¹ • Q₀.vert 0 = α
    rw [h0]
    exact MulAction.mem_stabilizer_iff.1 (hinv i)
  have hz : ∀ i : Fin 5, L.z ((P i).vert 4) = dihConj s (s * e) i := by
    intro i
    show L.z (((s * e) ^ (i : ℕ))⁻¹ • Q₀.vert 4) = _
    rw [L.equivariant _ _ h05, inv_inv, ← hs_def]
    rfl
  have hfun : (fun i : Fin 5 => L.z ((P i).vert 4)) = dihConj s (s * e) := funext hz
  have hv4 : ∀ i : Fin 5, valence Γ ((P i).vert 4) = 5 := fun i => by
    show valence Γ (((s * e) ^ (i : ℕ))⁻¹ • Q₀.vert 4) = 5
    rw [valence_smul F]
    exact h05
  have hdih2 : dihConj s (s * e) 2 = L.z (Q₂.vert 4) := by
    have h := dihConj_two_mul_zero hs2 he2 hr
    have h0' : dihConj s (s * e) 0 = s := by simp [dihConj]
    have h' : dihConj s (s * e) 2 * s = L.z (Q₂.vert 4) * s := by
      rw [← hrdef]
      rw [h0'] at h
      exact h
    exact mul_right_cancel h'
  refine ⟨⟨P, hα, hstart, ?_, ?_, fun i => ?_⟩, fun m _ => ?_, ?_⟩
  · rw [hfun]
    exact dihConj_injective hs2 he2 hr
  · rw [hfun, dihConj_closure hs2 he2 hr]
    exact ⟨φ'⟩
  · rw [hz 2, hz 0, hz i, hz (i + 1)]
    exact dihConj_shift hs2 he2 hr i
  · show ((s * e) ^ ((0 : Fin 5) : ℕ))⁻¹ • Q₀.vert m = Q₀.vert m
    simp
  · have h4 : (P 2).vert 4 = Q₂.vert 4 :=
      h71c.z_injective (hv4 2) h25 (by rw [hz 2, hdih2])
    exact Arc.vert_eq_of_ends hT (P 2) Q₂ ((hstart 2).trans h2.symm) h4

end P4X

end CFSG.Quasithin.Fan86
