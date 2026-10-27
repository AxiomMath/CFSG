module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3cAutSq

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL CFSG.Quasithin.F6.GoldAmL3
  CFSG.Quasithin.F6.GoldAmL2T

namespace F6

namespace GoldAmL3c

variable {D : Type*} [Group D] {A B : Subgroup D} {z : D} {V : Subgroup D}

section NB

variable [Finite D] {x a a₁ a₂ : D} {N : Subgroup D} (g : Gen3 A B z V x a a₁ a₂)
  (d : NData B V x N)

include g d

theorem NData.isCentralProduct₂ (hU : Nat.card (conjClosure V B) = 8) :
    IsCentralProduct₂ ↥N (QuaternionGroup 2) (QuaternionGroup 2) := by
  obtain ⟨q₀, hq₀N, h₀, hinv⟩ := d.exists_q₀_invol g hU
  obtain ⟨p, hpN, hpp, hap, ha₂p, hq₀p, hpcases⟩ := d.exists_p g hU hq₀N h₀ hinv
  have hz1 : z ≠ 1 := g.hyp.natural.z_ne
  have haN : a ∈ N := d.U_le g.a_mem_U
  have ha₂N : a₂ ∈ N := d.U_le g.a₂_mem_U
  have hqa := g.comm_a_of_fst_z (q := q₀) (by rw [h₀])
  have hq₀B : (q₀ : D) ∈ B := pCoreOf_le 2 B q₀.2
  have hzs : z * a = a * z := (g.z_comm g.a_mem_B).symm
  have hzs' : z * a₂ = a₂ * z := (g.z_comm g.a₂_mem_B).symm
  have hts : (q₀ : D) * a * (q₀ : D)⁻¹ = z * a := by
    have hqa' : (q₀ : D) * a * (q₀ : D)⁻¹ * a⁻¹ = z := by
      calc (q₀ : D) * a * (q₀ : D)⁻¹ * a⁻¹ = (a * q₀ * a⁻¹ * (q₀ : D)⁻¹)⁻¹ := by group
        _ = z := by rw [hqa, g.z_inv]
    calc (q₀ : D) * a * (q₀ : D)⁻¹ = ((q₀ : D) * a * (q₀ : D)⁻¹ * a⁻¹) * a := by group
      _ = z * a := by rw [hqa']
  have hts' : p * a₂ * p⁻¹ = z * a₂ := by
    have e : p * a₂ * p⁻¹ * a₂⁻¹ = z := by
      calc p * a₂ * p⁻¹ * a₂⁻¹ = (a₂ * p * a₂⁻¹ * p⁻¹)⁻¹ := by group
        _ = z := by rw [ha₂p, g.z_inv]
    calc p * a₂ * p⁻¹ = (p * a₂ * p⁻¹ * a₂⁻¹) * a₂ := by group
      _ = z * a₂ := by rw [e]
  have c3 : (q₀ : D) * a₂ = a₂ * q₀ := by
    have h := g.comm_a₂ hU q₀
    have e : (a * (q₀ : D) * a⁻¹ * (q₀ : D)⁻¹) * (a₁ * (q₀ : D) * a₁⁻¹ * (q₀ : D)⁻¹) = 1 := by
      change ((psi g q₀).1 : D) * ((psi g q₀).2 : D) = 1
      rw [h₀]
      simp [zel, g.z_mul_z]
    rw [e] at h
    calc (q₀ : D) * a₂ = (a₂ * (q₀ : D) * a₂⁻¹ * (q₀ : D)⁻¹)⁻¹ * (a₂ * q₀) := by group
      _ = a₂ * q₀ := by rw [h]; simp
  refine isCentralProduct₂_of_dihedral_pair N (s := a) (t := (q₀ : D)) (s' := a₂)
    (t' := p) (z₀ := z) haN hq₀N ha₂N hpN hz1 g.z_mul_z hzs hzs' g.a_sq hinv g.a₂_sq hpp hts hts'
    (g.U_comm g.a_mem_U g.a₂_mem_U) hap c3 hq₀p ?_ d.card_N
  apply le_antisymm
  · rw [Subgroup.closure_le]
    intro w hw
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl | rfl | rfl
    · exact haN
    · exact hq₀N
    · exact ha₂N
    · exact hpN
  · intro q hq
    set C := Subgroup.closure ({a, (q₀ : D), a₂, p} : Set D) with hC
    have haC : a ∈ C := Subgroup.subset_closure (by simp)
    have hq₀C : (q₀ : D) ∈ C := Subgroup.subset_closure (by simp)
    have ha₂C : a₂ ∈ C := Subgroup.subset_closure (by simp)
    have hpC : p ∈ C := Subgroup.subset_closure (by simp)
    have hzC : z ∈ C := by
      have e : z = a * (q₀ : D) * a⁻¹ * (q₀ : D)⁻¹ := hqa.symm
      rw [e]
      exact C.mul_mem (C.mul_mem (C.mul_mem haC hq₀C) (C.inv_mem haC)) (C.inv_mem hq₀C)
    have ha₁C : a₁ ∈ C := by
      rcases g.a₂_eq_or hU with e | e
      · have : a₁ = a⁻¹ * a₂ := by rw [e]; group
        rw [this]; exact C.mul_mem (C.inv_mem haC) ha₂C
      · have : a₁ = (z * a)⁻¹ * a₂ := by rw [e]; group
        rw [this]; exact C.mul_mem (C.inv_mem (C.mul_mem hzC haC)) ha₂C
    have hVC : ∀ v ∈ V, v ∈ C := by
      intro v hv
      rcases g.mem_V_iff.mp hv with rfl | rfl | rfl | rfl
      · exact C.one_mem
      · exact hzC
      · exact haC
      · exact C.mul_mem hzC haC
    have hUC : ∀ u ∈ conjClosure V B, u ∈ C := by
      intro u hu
      rcases g.mem_U_cases hU hu with huV | ⟨v, hv, rfl⟩
      · exact hVC u huV
      · exact C.mul_mem (hVC v hv) ha₁C
    have hxcC : (g.xc q₀ : D) ∈ C := by
      rcases hpcases with e | e
      · rw [← e]; exact hpC
      · have : (g.xc q₀ : D) = p * a⁻¹ := by rw [e]; group
        rw [this]; exact C.mul_mem hpC (C.inv_mem haC)
    have hcl := d.mem_closure g hU hq₀N h₀ hq
    have hle : Subgroup.closure ((conjClosure V B : Set D) ∪ {(q₀ : D), (g.xc q₀ : D)}) ≤ C := by
      rw [Subgroup.closure_le]
      rintro w (hw | hw | hw)
      · exact hUC w hw
      · rw [hw]; exact hq₀C
      · rw [Set.mem_singleton_iff.mp hw]; exact hxcC
    exact hle hcl

end NB

end GoldAmL3c

end F6

end CFSG.Quasithin
