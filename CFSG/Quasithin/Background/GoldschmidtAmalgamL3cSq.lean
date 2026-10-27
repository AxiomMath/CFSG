module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3cComm

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL CFSG.Quasithin.F6.GoldAmL3
  CFSG.Quasithin.F6.GoldAmL2T

namespace F6

namespace GoldAmL3c

variable {D : Type*} [Group D] {A B : Subgroup D} {z : D} {V : Subgroup D}

section Sq

variable [Finite D] {x a a₁ a₂ : D} (g : Gen3 A B z V x a a₁ a₂)

include g

theorem Gen3.psi_fst (q : ↥(pCoreOf 2 B)) :
    ((psi g q).1 : D) = a * q * a⁻¹ * (q : D)⁻¹ := rfl

theorem Gen3.comm_a_of_fst_one {q : ↥(pCoreOf 2 B)} (h : (psi g q).1 = 1) :
    a * (q : D) = q * a := by
  have h1 := congrArg (fun w : ↥(Subgroup.zpowers z) => (w : D)) h
  simp only [Gen3.psi_fst, OneMemClass.coe_one] at h1
  calc a * (q : D) = (a * q * a⁻¹ * (q : D)⁻¹) * ((q : D) * a) := by group
    _ = (q : D) * a := by rw [h1, one_mul]

theorem Gen3.comm_a_of_fst_z {q : ↥(pCoreOf 2 B)} (h : (psi g q).1 = zel z) :
    a * (q : D) * a⁻¹ * (q : D)⁻¹ = z := by
  have h1 := congrArg (fun w : ↥(Subgroup.zpowers z) => (w : D)) h
  exact h1

theorem Gen3.comm_a₁_of_snd_z {q : ↥(pCoreOf 2 B)} (h : (psi g q).2 = zel z) :
    a₁ * (q : D) * a₁⁻¹ * (q : D)⁻¹ = z := by
  have h1 := congrArg (fun w : ↥(Subgroup.zpowers z) => (w : D)) h
  exact h1

omit [Finite D] in
theorem Gen3.z_inv : z⁻¹ = z := inv_eq_of_mul_eq_one_right g.z_mul_z

omit [Finite D] in
theorem Gen3.comm_V_of {q : D} (hq : q ∈ B) (hqa : a * q = q * a) {v : D} (hv : v ∈ V) :
    v * q = q * v := by
  have hzq : z * q = q * z := (g.z_comm hq).symm
  rcases g.mem_V_iff.mp hv with rfl | rfl | rfl | rfl
  · simp
  · exact hzq
  · exact hqa
  · calc z * a * q = z * (a * q) := by group
      _ = z * (q * a) := by rw [hqa]
      _ = (z * q) * a := by group
      _ = (q * z) * a := by rw [hzq]
      _ = q * (z * a) := by group

theorem Gen3.sq_q₀_mem (hU : Nat.card (conjClosure V B) = 8) (hT : Nat.card ↥(A ⊓ B) = 64)
    {q₀ : ↥(pCoreOf 2 B)} (h₀ : psi g q₀ = (zel z, zel z)) :
    (q₀ : D) * q₀ ∈ Subgroup.zpowers z := by
  have hzz := g.zel_mul_zel
  have hz1 : z ≠ 1 := g.hyp.natural.z_ne
  have hcomm01 := g.comm_q₀_q₁_mem hU hT h₀
  have rot := g.psi_xc hU
  have h₁ : psi g (g.xc q₀) = (1, zel z) := by rw [rot, h₀]; simp [hzz]
  have hq₀B : (q₀ : D) ∈ B := pCoreOf_le 2 B q₀.2
  have hq₁B : (g.xc q₀ : D) ∈ B := pCoreOf_le 2 B (g.xc q₀).2
  have hs_ker : q₀ * q₀ ∈ (psi g).ker := by
    rw [MonoidHom.mem_ker, map_mul, h₀]; simp [hzz]
  have hs_U : (q₀ : D) * q₀ ∈ conjClosure V B :=
    (g.U_eq_K hU hT).ge ((g.mem_ker_psi hU _).mp hs_ker)
  obtain ⟨d, hd⟩ : ∃ d : D, d = (q₀ : D) * (g.xc q₀ : D) * (q₀ : D)⁻¹ * (g.xc q₀ : D)⁻¹ :=
    ⟨_, rfl⟩
  rw [← hd] at hcomm01
  have hdd : d * d = 1 := by
    rcases zpowers_cases g.hyp hcomm01 with e | e
    · rw [e]; simp
    · rw [e]; exact g.z_mul_z
  have e1 : (q₀ : D) * (g.xc q₀ : D) = d * (g.xc q₀ : D) * (q₀ : D) := by rw [hd]; group
  have hc0 : (q₀ : D) * d = d * (q₀ : D) := zpowers_comm_B g.hyp hq₀B hcomm01
  have hsq₁ : ((q₀ : D) * q₀) * (g.xc q₀ : D) = (g.xc q₀ : D) * ((q₀ : D) * q₀) := by
    calc (q₀ : D) * q₀ * (g.xc q₀ : D) = q₀ * (q₀ * (g.xc q₀ : D)) := by group
      _ = q₀ * (d * (g.xc q₀ : D) * q₀) := by rw [e1]
      _ = ((q₀ : D) * d) * (g.xc q₀ : D) * q₀ := by group
      _ = (d * (q₀ : D)) * (g.xc q₀ : D) * q₀ := by rw [hc0]
      _ = d * ((q₀ : D) * (g.xc q₀ : D)) * q₀ := by group
      _ = d * (d * (g.xc q₀ : D) * q₀) * q₀ := by rw [e1]
      _ = (d * d) * (g.xc q₀ : D) * ((q₀ : D) * q₀) := by group
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
      have := hsq₁
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

end Sq

end GoldAmL3c

end F6

end CFSG.Quasithin
