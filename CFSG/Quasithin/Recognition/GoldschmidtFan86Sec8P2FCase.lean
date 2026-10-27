module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P2FSib
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P2KRed

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

namespace Sec8P2F

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}
  {F : FanTree Γ G} {L : ZLab Γ G} {α : V} {D : D10Set L α}

theorem case_nu_inv (F : FanTree Γ G) (h7 : Fan7 F L) (h512 : Fan512 F L) (h83a : Fan83a F L)
    (h83b : Fan83b F L) (h83d : Fan83d F L) {δ' : V} (hY : D.IsYPair δ') {ν : V}
    (hν : Γ.Adj (D.alpha 0) ν) (hνδ : Γ.Adj ν δ')
    (hcase : ν = (D.y δ' 2 * D.y δ' 1)⁻¹ • D.xi 0) : prodFive (D.y δ') = 1 := by
  have h71a : Fan71a F L := h7.1
  have h71c : Fan71c F L := h7.2.2.1
  obtain ⟨hy, -, -⟩ := y_labels F h71c h83a h83b h83d hY
  have hu : (D.y δ' 2 * D.y δ' 1) • D.alpha 0 = D.alpha 0 := u_fix_alpha F h71c h83a h83b hY
  have hu' : (D.y δ' 2 * D.y δ' 1)⁻¹ • D.alpha 0 = D.alpha 0 := inv_smul_eq_iff.2 hu.symm
  obtain ⟨hdd, -⟩ := smul_delta_facts F (D := D) hu'
  have hδ'' : Γ.Adj ν ((D.y δ' 2 * D.y δ' 1)⁻¹ • D.delta 0) := by
    rw [hcase]
    exact (F.adj_smul _ _ _).2 (D.adj_xi_delta 0)
  have hν3 : valence Γ ν = 3 := valence_adj_three F (D.valence_alpha F 0) hν
  have hap : D.alpha 0 ≠ δ' := fun h => by
    have := hY.2.2.2.2.1
    rw [← h, SimpleGraph.dist_self] at this
    omega
  have haq : D.alpha 0 ≠ (D.y δ' 2 * D.y δ' 1)⁻¹ • D.delta 0 := fun h => by
    rw [← h, SimpleGraph.dist_self] at hdd
    omega
  rcases z_mul_sibling F h512 hν3 hν.symm hνδ hδ'' hap haq with h | h
  · rw [hy]
    exact h
  · exfalso
    apply z_alpha_not_mem_calpha F h71a h71c (D := D)
    rw [← h, ← hy]
    exact prodFive_mem_calpha F h71c h83a h83b h83d hY

theorem case_nu (F : FanTree Γ G) (h7 : Fan7 F L) (h512 : Fan512 F L) (h517 : Fan517 F L)
    (h82a : Fan82a F L) (h83a : Fan83a F L) (h83b : Fan83b F L) (h83d : Fan83d F L) {δ' : V}
    (hY : D.IsYPair δ') {ν : V} (hν : Γ.Adj (D.alpha 0) ν) (hνδ : Γ.Adj ν δ')
    (hcase : ν = (D.y δ' 2 * D.y δ' 1) • D.xi 0) : False := by
  have h71a : Fan71a F L := h7.1
  have h71c : Fan71c F L := h7.2.2.1
  have h73b : Fan73b F L := h7.2.2.2.2.2.2.1
  obtain ⟨-, hy', -⟩ := y_labels F h71c h83a h83b h83d hY
  have hR := fiveRel D F h71c h83a h83b h83d hY
  have hu : (D.y δ' 2 * D.y δ' 1) • D.alpha 0 = D.alpha 0 := u_fix_alpha F h71c h83a h83b hY
  obtain ⟨hdd, -⟩ := smul_delta_facts F (D := D) hu
  have hδ''' : Γ.Adj ν ((D.y δ' 2 * D.y δ' 1) • D.delta 0) := by
    rw [hcase]
    exact (F.adj_smul _ _ _).2 (D.adj_xi_delta 0)
  have hν3 : valence Γ ν = 3 := valence_adj_three F (D.valence_alpha F 0) hν
  have hap : D.alpha 0 ≠ δ' := fun h => by
    have := hY.2.2.2.2.1
    rw [← h, SimpleGraph.dist_self] at this
    omega
  have haq : D.alpha 0 ≠ (D.y δ' 2 * D.y δ' 1) • D.delta 0 := fun h => by
    rw [← h, SimpleGraph.dist_self] at hdd
    omega
  have hcp : D.y δ' 2 * D.y δ' 1 * (D.y δ' 4 * D.y δ' 3) =
      (L.z (D.alpha 3) * L.z (D.alpha 2) * L.z α) *
        (D.y δ' 1 * D.y δ' 2 * D.y δ' 3 * D.y δ' 4) := hR.comm_pair
  have hcc : D.y δ' 0 * (L.z (D.alpha 3) * L.z (D.alpha 2) * L.z α) * D.y δ' 0 =
      L.z (D.alpha 3) * L.z (D.alpha 2) * L.z α := hR.conj_c
  have hcsq := hR.c_sq
  have hy2 := hR.sq_a 0
  have hprod : prodFive (D.y δ') = D.y δ' 0 * (D.y δ' 1 * D.y δ' 2 * D.y δ' 3 * D.y δ' 4) := by
    simp only [prodFive, mul_assoc]
  have he' : L.z δ' * L.z ((D.y δ' 2 * D.y δ' 1) • D.delta 0) =
      (L.z (D.alpha 3) * L.z (D.alpha 2) * L.z α) * prodFive (D.y δ') := by
    rw [← hy', hcp, hprod]
    calc D.y δ' 0 * ((L.z (D.alpha 3) * L.z (D.alpha 2) * L.z α) *
          (D.y δ' 1 * D.y δ' 2 * D.y δ' 3 * D.y δ' 4))
        = D.y δ' 0 * (L.z (D.alpha 3) * L.z (D.alpha 2) * L.z α) * (D.y δ' 0 * D.y δ' 0) *
          (D.y δ' 1 * D.y δ' 2 * D.y δ' 3 * D.y δ' 4) := by
          rw [hy2, mul_one]
          simp only [mul_assoc]
      _ = (D.y δ' 0 * (L.z (D.alpha 3) * L.z (D.alpha 2) * L.z α) * D.y δ' 0) *
          (D.y δ' 0 * (D.y δ' 1 * D.y δ' 2 * D.y δ' 3 * D.y δ' 4)) := by simp only [mul_assoc]
      _ = _ := by rw [hcc]
  have hyc : prodFive (D.y δ') = (L.z (D.alpha 3) * L.z (D.alpha 2) * L.z α) *
      (L.z δ' * L.z ((D.y δ' 2 * D.y δ' 1) • D.delta 0)) := by
    rw [he']
    calc prodFive (D.y δ') = 1 * prodFive (D.y δ') := (one_mul _).symm
      _ = (L.z (D.alpha 3) * L.z (D.alpha 2) * L.z α) *
          ((L.z (D.alpha 3) * L.z (D.alpha 2) * L.z α) * prodFive (D.y δ')) := by
          rw [← mul_assoc, hcsq]
  have hcV : L.z (D.alpha 3) * L.z (D.alpha 2) * L.z α ∈ L.zGroup 2 α :=
    mul_mem (mul_mem (Sec8P3.z_alpha_mem_zGroup D F 3) (Sec8P3.z_alpha_mem_zGroup D F 2))
      (Sec8P3.z_mem_zGroup D.val)
  have hyC := prodFive_mem_calpha F h71c h83a h83b h83d hY
  obtain ⟨P8, -, h4', -, -, -, hLD, -⟩ := Sec8P2K.exists_arc8_calpha D F h71a h71c
  have hv : valence Γ (P8.vert 4) = 5 := by
    rw [h4']
    exact D.val
  have hVC := (h73b P8 hv).2
  rw [h4', hLD] at hVC
  have hd : ∀ i, Γ.dist α (D.alpha i) = 2 := fun i => D.dist_start_alpha F i
  have hw0 : L.z (D.alpha 0) * L.z α = L.z α * L.z (D.alpha 0) := hR.comm_zw 0
  have hww := hR.sq_w
  rcases z_mul_sibling F h512 hν3 hν.symm hνδ hδ''' hap haq with h | h
  ·
    rw [h, mul_one] at hyc
    have hmemV : prodFive (D.y δ') ∈ L.zGroup 2 α := by
      rw [hyc]
      exact hcV
    have hzp : prodFive (D.y δ') ∈ Subgroup.zpowers (L.z α) := by
      rw [← hVC]
      exact Subgroup.mem_inf.2 ⟨hmemV, hyC⟩
    have h32 : L.z (D.alpha 3) * L.z (D.alpha 2) ∈ Subgroup.zpowers (L.z α) := by
      have : L.z (D.alpha 3) * L.z (D.alpha 2) = prodFive (D.y δ') * L.z α := by
        rw [hyc, mul_assoc (L.z (D.alpha 3) * L.z (D.alpha 2)) (L.z α) (L.z α), hww, mul_one]
      rw [this]
      exact Subgroup.mul_mem _ hzp (Subgroup.mem_zpowers _)
    have hrel : L.z (D.alpha 0) * L.z (D.alpha 1) * L.z (D.alpha 4) =
        L.z (D.alpha 3) * L.z (D.alpha 2) := hR.prod_rel (h82a α D)
    exact ((h517 α D.val).2 (D.alpha 0) (D.alpha 1) (D.alpha 4) (hd 0) (hd 1) (hd 4))
      (by rw [hrel]; exact h32)
  ·
    rw [h] at hyc
    have hmemV : prodFive (D.y δ') ∈ L.zGroup 2 α := by
      rw [hyc]
      exact mul_mem hcV (Sec8P3.z_alpha_mem_zGroup D F 0)
    have hzp : prodFive (D.y δ') ∈ Subgroup.zpowers (L.z α) := by
      rw [← hVC]
      exact Subgroup.mem_inf.2 ⟨hmemV, hyC⟩
    have h320 : L.z (D.alpha 3) * L.z (D.alpha 2) * L.z (D.alpha 0) ∈
        Subgroup.zpowers (L.z α) := by
      have : L.z (D.alpha 3) * L.z (D.alpha 2) * L.z (D.alpha 0) = prodFive (D.y δ') * L.z α := by
        rw [hyc]
        calc L.z (D.alpha 3) * L.z (D.alpha 2) * L.z (D.alpha 0)
            = L.z (D.alpha 3) * L.z (D.alpha 2) * L.z (D.alpha 0) * (L.z α * L.z α) := by
              rw [hww, mul_one]
          _ = L.z (D.alpha 3) * L.z (D.alpha 2) * (L.z (D.alpha 0) * L.z α) * L.z α := by
              simp only [mul_assoc]
          _ = (L.z (D.alpha 3) * L.z (D.alpha 2) * L.z α) * L.z (D.alpha 0) * L.z α := by
              rw [hw0]
              simp only [mul_assoc]
      rw [this]
      exact Subgroup.mul_mem _ hzp (Subgroup.mem_zpowers _)
    exact ((h517 α D.val).2 (D.alpha 3) (D.alpha 2) (D.alpha 0) (hd 3) (hd 2) (hd 0)) h320

end Sec8P2F

end CFSG.Quasithin.Fan86
