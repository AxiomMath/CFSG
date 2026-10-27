module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3cAutComm
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3cQ8

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

theorem NData.sq_q₀_mem (hU : Nat.card (conjClosure V B) = 8)
    {q₀ : ↥(pCoreOf 2 B)} (hq₀N : (q₀ : D) ∈ N) (h₀ : psi g q₀ = (zel z, zel z)) :
    (q₀ : D) * q₀ ∈ Subgroup.zpowers z := by
  have hzz := g.zel_mul_zel
  have hz1 : z ≠ 1 := g.hyp.natural.z_ne
  have hcomm01 := d.comm_q₀_q₁_mem g hU hq₀N h₀
  have rot := g.psi_xc hU
  have h₁ : psi g (g.xc q₀) = (1, zel z) := by rw [rot, h₀]; simp [hzz]
  have hq₀B : (q₀ : D) ∈ B := pCoreOf_le 2 B q₀.2
  have hq₁B : (g.xc q₀ : D) ∈ B := pCoreOf_le 2 B (g.xc q₀).2
  have hs_ker : psi g (q₀ * q₀) = 1 := by
    rw [map_mul, h₀]; simp [hzz]
  have hs_N : (((q₀ * q₀ : ↥(pCoreOf 2 B)) : D)) ∈ N := N.mul_mem hq₀N hq₀N
  have hs_U : (q₀ : D) * q₀ ∈ conjClosure V B := d.mem_U_of_psi_eq_one g hU hs_N hs_ker
  obtain ⟨d', hd⟩ : ∃ d' : D, d' = (q₀ : D) * (g.xc q₀ : D) * (q₀ : D)⁻¹ * (g.xc q₀ : D)⁻¹ :=
    ⟨_, rfl⟩
  rw [← hd] at hcomm01
  have hdd : d' * d' = 1 := by
    rcases zpowers_cases g.hyp hcomm01 with e | e
    · rw [e]; simp
    · rw [e]; exact g.z_mul_z
  have e1 : (q₀ : D) * (g.xc q₀ : D) = d' * (g.xc q₀ : D) * (q₀ : D) := by rw [hd]; group
  have hc0 : (q₀ : D) * d' = d' * (q₀ : D) := zpowers_comm_B g.hyp hq₀B hcomm01
  have hsq₁ : ((q₀ : D) * q₀) * (g.xc q₀ : D) = (g.xc q₀ : D) * ((q₀ : D) * q₀) := by
    calc (q₀ : D) * q₀ * (g.xc q₀ : D) = q₀ * (q₀ * (g.xc q₀ : D)) := by group
      _ = q₀ * (d' * (g.xc q₀ : D) * q₀) := by rw [e1]
      _ = ((q₀ : D) * d') * (g.xc q₀ : D) * q₀ := by group
      _ = (d' * (q₀ : D)) * (g.xc q₀ : D) * q₀ := by rw [hc0]
      _ = d' * ((q₀ : D) * (g.xc q₀ : D)) * q₀ := by group
      _ = d' * (d' * (g.xc q₀ : D) * q₀) * q₀ := by rw [e1]
      _ = (d' * d') * (g.xc q₀ : D) * ((q₀ : D) * q₀) := by group
      _ = (g.xc q₀ : D) * ((q₀ : D) * q₀) := by rw [hdd, one_mul]
  have hsV : (q₀ : D) * q₀ ∈ V := by
    rcases g.mem_U_cases hU hs_U with hsV | ⟨v, hv, hsv⟩
    · exact hsV
    · exfalso
      have hap : a * (g.xc q₀ : D) = (g.xc q₀ : D) * a :=
        g.comm_a_of_fst_one (by rw [h₁])
      have hvq : v * (g.xc q₀ : D) = (g.xc q₀ : D) * v := g.comm_V_of hq₁B hap hv
      rw [hsv] at hsq₁
      have h1 : a₁ * (g.xc q₀ : D) = (g.xc q₀ : D) * a₁ := by
        have : v * (a₁ * (g.xc q₀ : D)) = v * ((g.xc q₀ : D) * a₁) := by
          calc v * (a₁ * (g.xc q₀ : D)) = (v * a₁) * (g.xc q₀ : D) := by group
            _ = (g.xc q₀ : D) * (v * a₁) := hsq₁
            _ = ((g.xc q₀ : D) * v) * a₁ := by group
            _ = (v * (g.xc q₀ : D)) * a₁ := by rw [hvq]
            _ = v * ((g.xc q₀ : D) * a₁) := by group
        exact mul_left_cancel this
      have h2 := g.comm_a₁_of_snd_z (q := g.xc q₀) (by rw [h₁])
      rw [h1] at h2
      have : (g.xc q₀ : D) * a₁ * a₁⁻¹ * (g.xc q₀ : D)⁻¹ = 1 := by group
      rw [this] at h2
      exact hz1 h2.symm
  have hqa := g.comm_a_of_fst_z (q := q₀) (by rw [h₀])
  rcases g.mem_V_iff.mp hsV with e | e | e | e
  · rw [e]; exact Subgroup.one_mem _
  · rw [e]; exact Subgroup.mem_zpowers z
  · exfalso
    have hc : a * (q₀ : D) = (q₀ : D) * a := by
      calc a * (q₀ : D) = ((q₀ : D) * q₀) * q₀ := by rw [← e]
        _ = q₀ * ((q₀ : D) * q₀) := by group
        _ = (q₀ : D) * a := by rw [e]
    have : a * (q₀ : D) * a⁻¹ * (q₀ : D)⁻¹ = 1 := by
      rw [hc]; group
    rw [this] at hqa
    exact hz1 hqa.symm
  · exfalso
    have hc : z * a * (q₀ : D) = (q₀ : D) * (z * a) := by
      calc z * a * (q₀ : D) = ((q₀ : D) * q₀) * q₀ := by rw [← e]
        _ = q₀ * ((q₀ : D) * q₀) := by group
        _ = (q₀ : D) * (z * a) := by rw [e]
    have hzq : z * (q₀ : D) = (q₀ : D) * z := (g.z_comm hq₀B).symm
    have hc' : a * (q₀ : D) = (q₀ : D) * a := by
      have : z * (a * (q₀ : D)) = z * ((q₀ : D) * a) := by
        calc z * (a * (q₀ : D)) = z * a * (q₀ : D) := by group
          _ = (q₀ : D) * (z * a) := hc
          _ = ((q₀ : D) * z) * a := by group
          _ = (z * (q₀ : D)) * a := by rw [hzq]
          _ = z * ((q₀ : D) * a) := by group
      exact mul_left_cancel this
    have : a * (q₀ : D) * a⁻¹ * (q₀ : D)⁻¹ = 1 := by
      rw [hc']; group
    rw [this] at hqa
    exact hz1 hqa.symm

theorem NData.exists_q₀_invol (hU : Nat.card (conjClosure V B) = 8) :
    ∃ q : ↥(pCoreOf 2 B), (q : D) ∈ N ∧ psi g q = (zel z, zel z) ∧ (q : D) * q = 1 := by
  obtain ⟨q₀, hq₀N, h₀⟩ := d.exists_q₀ g hU
  have hs := d.sq_q₀_mem g hU hq₀N h₀
  rcases zpowers_cases g.hyp hs with e | e
  · exact ⟨q₀, hq₀N, h₀, e⟩
  · refine ⟨q₀ * ⟨a, g.a_mem_QB⟩, N.mul_mem hq₀N (d.U_le g.a_mem_U), ?_, ?_⟩
    · rw [map_mul, g.psi_a hU, mul_one, h₀]
    · have hq₀B : (q₀ : D) ∈ B := pCoreOf_le 2 B q₀.2
      have hqa := g.comm_a_of_fst_z (q := q₀) (by rw [h₀])
      have e1 : a * (q₀ : D) = z * q₀ * a := by
        calc a * (q₀ : D) = (a * q₀ * a⁻¹ * (q₀ : D)⁻¹) * q₀ * a := by group
          _ = z * q₀ * a := by rw [hqa]
      have hzq : (q₀ : D) * z = z * (q₀ : D) := g.z_comm hq₀B
      show (q₀ : D) * a * ((q₀ : D) * a) = 1
      calc (q₀ : D) * a * ((q₀ : D) * a) = q₀ * (a * q₀) * a := by group
        _ = q₀ * (z * q₀ * a) * a := by rw [e1]
        _ = (q₀ * z) * q₀ * (a * a) := by group
        _ = (z * q₀) * q₀ * (a * a) := by rw [hzq]
        _ = z * ((q₀ : D) * q₀) * (a * a) := by group
        _ = 1 := by rw [e, g.a_sq, g.z_mul_z]; group

theorem NData.exists_p (hU : Nat.card (conjClosure V B) = 8) {q₀ : ↥(pCoreOf 2 B)}
    (hq₀N : (q₀ : D) ∈ N) (h₀ : psi g q₀ = (zel z, zel z)) (hinv : (q₀ : D) * q₀ = 1) :
    ∃ p : D, p ∈ N ∧ p * p = 1 ∧ a * p = p * a ∧ a₂ * p * a₂⁻¹ * p⁻¹ = z ∧
      (q₀ : D) * p = p * q₀ ∧ (p = (g.xc q₀ : D) ∨ p = (g.xc q₀ : D) * a) := by
  have hzz := g.zel_mul_zel
  have rot := g.psi_xc hU
  have h₁ : psi g (g.xc q₀) = (1, zel z) := by rw [rot, h₀]; simp [hzz]
  have hq₁N : ((g.xc q₀ : ↥(pCoreOf 2 B)) : D) ∈ N := d.xc_mem g hq₀N
  have hq₁inv : (g.xc q₀ : D) * (g.xc q₀ : D) = 1 := by
    show x * q₀ * x⁻¹ * (x * q₀ * x⁻¹) = 1
    calc x * (q₀ : D) * x⁻¹ * (x * q₀ * x⁻¹) = x * ((q₀ : D) * q₀) * x⁻¹ := by group
      _ = 1 := by rw [hinv]; group
  have haq₁ : a * (g.xc q₀ : D) = (g.xc q₀ : D) * a := g.comm_a_of_fst_one (by rw [h₁])
  have ha₂q₁ : a₂ * (g.xc q₀ : D) * a₂⁻¹ * (g.xc q₀ : D)⁻¹ = z := by
    have h := g.comm_a₂ hU (g.xc q₀)
    have e : (a * (g.xc q₀ : D) * a⁻¹ * (g.xc q₀ : D)⁻¹) *
        (a₁ * (g.xc q₀ : D) * a₁⁻¹ * (g.xc q₀ : D)⁻¹) = z := by
      change ((psi g (g.xc q₀)).1 : D) * ((psi g (g.xc q₀)).2 : D) = z
      rw [h₁]
      simp [zel]
    rw [h, e]
  have hqa := g.comm_a_of_fst_z (q := q₀) (by rw [h₀])
  have hq₀B : (q₀ : D) ∈ B := pCoreOf_le 2 B q₀.2
  have hq₁B : (g.xc q₀ : D) ∈ B := pCoreOf_le 2 B (g.xc q₀).2
  have hcomm01 := d.comm_q₀_q₁_mem g hU hq₀N h₀
  rcases zpowers_cases g.hyp hcomm01 with hd | hd
  · refine ⟨(g.xc q₀ : D), hq₁N, hq₁inv, haq₁, ha₂q₁, ?_, Or.inl rfl⟩
    calc (q₀ : D) * (g.xc q₀ : D) = ((q₀ : D) * (g.xc q₀ : D) * (q₀ : D)⁻¹ * (g.xc q₀ : D)⁻¹) *
        ((g.xc q₀ : D) * q₀) := by group
      _ = (g.xc q₀ : D) * q₀ := by rw [hd, one_mul]
  · have haQ := g.a_mem_QB
    have haN : a ∈ N := d.U_le g.a_mem_U
    have ha₂i : a₂⁻¹ = a₂ := inv_eq_of_mul_eq_one_right g.a₂_sq
    have hzq₁ : (g.xc q₀ : D) * z = z * (g.xc q₀ : D) := g.z_comm hq₁B
    have hq₀a' : (q₀ : D) * a * (q₀ : D)⁻¹ * a⁻¹ = z := by
      calc (q₀ : D) * a * (q₀ : D)⁻¹ * a⁻¹ = (a * q₀ * a⁻¹ * (q₀ : D)⁻¹)⁻¹ := by group
        _ = z := by rw [hqa, g.z_inv]
    have hq₀a : (q₀ : D) * a = z * a * q₀ := by
      calc (q₀ : D) * a = ((q₀ : D) * a * (q₀ : D)⁻¹ * a⁻¹) * a * q₀ := by group
        _ = z * a * q₀ := by rw [hq₀a']
    have e : (q₀ : D) * (g.xc q₀ : D) = z * (g.xc q₀ : D) * q₀ := by
      calc (q₀ : D) * (g.xc q₀ : D) = ((q₀ : D) * (g.xc q₀ : D) * (q₀ : D)⁻¹ *
          (g.xc q₀ : D)⁻¹) * (g.xc q₀ : D) * q₀ := by group
        _ = z * (g.xc q₀ : D) * q₀ := by rw [hd]
    have haa₂ : a * a₂⁻¹ = a₂⁻¹ * a :=
      (show Commute a a₂ from g.U_comm g.a_mem_U g.a₂_mem_U).inv_right.eq
    refine ⟨(g.xc q₀ : D) * a, N.mul_mem hq₁N haN, ?_, ?_, ?_, ?_, Or.inr rfl⟩
    · calc (g.xc q₀ : D) * a * ((g.xc q₀ : D) * a) = (g.xc q₀ : D) * (a * (g.xc q₀ : D)) * a := by
            group
        _ = (g.xc q₀ : D) * ((g.xc q₀ : D) * a) * a := by rw [haq₁]
        _ = ((g.xc q₀ : D) * (g.xc q₀ : D)) * (a * a) := by group
        _ = 1 := by rw [hq₁inv, g.a_sq]; group
    · calc a * ((g.xc q₀ : D) * a) = (a * (g.xc q₀ : D)) * a := by group
        _ = ((g.xc q₀ : D) * a) * a := by rw [haq₁]
    · calc a₂ * ((g.xc q₀ : D) * a) * a₂⁻¹ * ((g.xc q₀ : D) * a)⁻¹
          = a₂ * (g.xc q₀ : D) * (a * a₂⁻¹) * a⁻¹ * (g.xc q₀ : D)⁻¹ := by group
        _ = a₂ * (g.xc q₀ : D) * (a₂⁻¹ * a) * a⁻¹ * (g.xc q₀ : D)⁻¹ := by rw [haa₂]
        _ = a₂ * (g.xc q₀ : D) * a₂⁻¹ * (g.xc q₀ : D)⁻¹ := by group
        _ = z := ha₂q₁
    · calc (q₀ : D) * ((g.xc q₀ : D) * a) = ((q₀ : D) * (g.xc q₀ : D)) * a := by group
        _ = (z * (g.xc q₀ : D) * q₀) * a := by rw [e]
        _ = z * (g.xc q₀ : D) * ((q₀ : D) * a) := by group
        _ = z * (g.xc q₀ : D) * (z * a * q₀) := by rw [hq₀a]
        _ = z * ((g.xc q₀ : D) * z) * a * q₀ := by group
        _ = z * (z * (g.xc q₀ : D)) * a * q₀ := by rw [hzq₁]
        _ = (z * z) * (g.xc q₀ : D) * a * q₀ := by group
        _ = ((g.xc q₀ : D) * a) * q₀ := by rw [g.z_mul_z, one_mul]

end NB

end GoldAmL3c

end F6

end CFSG.Quasithin
