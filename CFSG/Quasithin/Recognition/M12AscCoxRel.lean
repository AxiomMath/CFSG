module

public import CFSG.Quasithin.Recognition.M12AscMir
public import CFSG.Quasithin.Recognition.M12AscX1
public import CFSG.Quasithin.Recognition.M12AscCoxInputs

public section

namespace CFSG.Quasithin

open Subgroup

variable {G : Type*} [Group G] {z : G}

open CFSG.GH74.M12 (Asc03Hyp)

theorem cube_eq_nrmG {x f : G} (hx3 : x * x * x = 1)
    (hc2 : f * (x * (f * (x * x))) = (x * (f * (x * x))) * f)
    (hc3 : f * ((x * x) * (f * x)) = ((x * x) * (f * x)) * f) :
    (x * f) ^ 3 = nrmG x f := by
  have hx4 : x * x * (x * x) = x := by
    calc x * x * (x * x) = (x * x * x) * x := by group
      _ = x := by rw [hx3, one_mul]
  have e3 : (x * f) ^ 3 = x * f * x * f * x * f := by
    rw [pow_succ, pow_two]; group
  have h1 : x * (f * (x * x)) * ((x * x) * (f * x)) * f = x * f * x * f * x * f := by
    calc x * (f * (x * x)) * ((x * x) * (f * x)) * f
        = x * f * (x * x * (x * x)) * f * x * f := by group
      _ = x * f * x * f * x * f := by rw [hx4]
  rw [e3, ← h1]
  unfold nrmG
  calc x * (f * (x * x)) * ((x * x) * (f * x)) * f
      = (x * (f * (x * x))) * (((x * x) * (f * x)) * f) := by group
    _ = (x * (f * (x * x))) * (f * ((x * x) * (f * x))) := by rw [hc3]
    _ = ((x * (f * (x * x))) * f) * ((x * x) * (f * x)) := by group
    _ = (f * (x * (f * (x * x)))) * ((x * x) * (f * x)) := by rw [hc2]
    _ = f * ((x * (f * (x * x))) * ((x * x) * (f * x))) := by group

@[expose] def coxVec (z x1 a u' x : G) : Fin 5 → G := ![z, x1 * z, a * u', u' * x, u']

theorem nrmG_mem {x f : G} {H : Subgroup G} (hx : x ∈ H) (hf : f ∈ H) : nrmG x f ∈ H := by
  unfold nrmG
  exact mul_mem hf (mul_mem (mul_mem hx (mul_mem hf (mul_mem hx hx)))
    (mul_mem (mul_mem hx hx) (mul_mem hf hx)))

namespace AscModel

variable (m : AscModel z)

include m

theorem exists_g_u [Finite G] (hyp : Asc03Hyp G z) :
    ∃ g : G, g * z * g⁻¹ ≠ z ∧ g * z * g⁻¹ ∈ ascQ z ∧ m.ψ mU ∈ ascQ (g * z * g⁻¹) := by
  classical
  obtain ⟨g₁, hg₁z, hs₁Q⟩ := exists_conj_data hyp
  obtain ⟨-, -, -, -, v₀, hv₀, hv₀o, hv₀Q⟩ := config_of_conj hyp hg₁z hs₁Q
  have hv₀2 : v₀ * v₀ = 1 := by
    have := pow_orderOf_eq_one v₀
    rwa [hv₀o, pow_two] at this
  have huH : m.ψ mU ∈ ascH z := m.ψ_mem mU
  have huQ : m.ψ mU ∉ ascQ z := by
    intro h
    have := ((m.mem_ascQ_iff_tb hyp).1 h).2
    rw [m.tb_ψ_mU] at this
    exact uTab_not_q this
  have hu2 : m.ψ mU * m.ψ mU = 1 := by rw [← map_mul, mU_sq, map_one]
  obtain ⟨h, hhH, hh⟩ := m.outInv_orbit_G hyp hv₀.1 hv₀Q hv₀2 huH huQ hu2
  have hhz : h * z = z * h := Subgroup.mem_centralizer_singleton_iff.1 hhH
  refine ⟨h * g₁, ?_, ?_, ?_⟩
  · intro hcon
    apply hg₁z
    have e : (h * g₁) * z * (h * g₁)⁻¹ = h * (g₁ * z * g₁⁻¹) * h⁻¹ := by group
    rw [e] at hcon
    calc g₁ * z * g₁⁻¹ = h⁻¹ * (h * (g₁ * z * g₁⁻¹) * h⁻¹) * h := by group
      _ = h⁻¹ * z * h := by rw [hcon]
      _ = z := by
        calc h⁻¹ * z * h = h⁻¹ * (z * h) := by group
          _ = h⁻¹ * (h * z) := by rw [hhz]
          _ = z := by group
  · have e : (h * g₁) * z * (h * g₁)⁻¹ = h * (g₁ * z * g₁⁻¹) * h⁻¹ := by group
    rw [e, m.ascQ_eq_qSub hyp]
    rw [m.ascQ_eq_qSub hyp] at hs₁Q
    exact m.qSub_normal hhH hs₁Q
  · rw [mem_ascQ_conj]
    have : (h * g₁)⁻¹ * m.ψ mU * (h * g₁) = g₁⁻¹ * v₀ * g₁ := by
      calc (h * g₁)⁻¹ * m.ψ mU * (h * g₁) = g₁⁻¹ * (h⁻¹ * (m.ψ mU * h)) * g₁ := by group
        _ = g₁⁻¹ * (h⁻¹ * (h * v₀)) * g₁ := by rw [← hh]
        _ = g₁⁻¹ * v₀ * g₁ := by group
    rw [this]
    exact (mem_map_conj_iff _ g₁ v₀).1 hv₀.2

theorem exists_coxeter [Finite G] [IsSimpleGroup G] (hyp : Asc03Hyp G z) (h27 : 27 ∣ Nat.card G) :
    ∃ u' x1 : G, (u' = m.ψ mU ∨ u' = m.ψ (mU * mZ)) ∧ orderOf x1 = 3 ∧
      x1 * m.ψ mX = m.ψ mX * x1 ∧ x1 * u' = u' * x1 ∧ z * x1 * z⁻¹ = x1⁻¹ ∧
      x1 ∉ zpowers (m.ψ mX) ∧
      (∀ i, coxVec z x1 (m.ψ mA) u' (m.ψ mX) i * coxVec z x1 (m.ψ mA) u' (m.ψ mX) i = 1) ∧
      (∀ i j : Fin 5, i.val < j.val →
        (coxVec z x1 (m.ψ mA) u' (m.ψ mX) i * coxVec z x1 (m.ψ mA) u' (m.ψ mX) j) ^
          coxExp i j = 1) ∧
      coxVec z x1 (m.ψ mA) u' (m.ψ mX) 0 * coxVec z x1 (m.ψ mA) u' (m.ψ mX) 2 ≠ 1 ∧
      ∃ g : G, g * z * g⁻¹ = z * m.ψ mA ∧ u' ∈ ascQ (z * m.ψ mA) := by
  classical
  obtain ⟨u', x1, hu'cases, hx1o, hx1x, hx1u, hx1z, hx1X⟩ := m.exists_x1 hyp h27
  refine ⟨u', x1, hu'cases, hx1o, hx1x, hx1u, hx1z, hx1X, ?_⟩
  have hz2 : z * z = 1 := asc_z_sq hyp
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
  have hx1z' : z * x1 * z = x1⁻¹ := by rw [hzi] at hx1z; exact hx1z
  have hx1_3 : x1 ^ 3 = 1 := by rw [← hx1o]; exact pow_orderOf_eq_one x1
  have hx1_3' : x1 * x1 * x1 = 1 := by rw [← hx1_3, pow_succ, pow_two]
  have hx1_1 : x1 ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hx1o
    omega
  obtain ⟨uM, huM, hu'eq⟩ : ∃ uM : ↥ascHModel, (uM = mU ∨ uM = mU * mZ) ∧ u' = m.ψ uM := by
    rcases hu'cases with h | h
    · exact ⟨mU, Or.inl rfl, h⟩
    · exact ⟨mU * mZ, Or.inr rfl, h⟩
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13⟩ := cox_local uM huM
  have d1 : u' * u' = 1 := by
    have := congrArg m.ψ c1
    simpa only [map_mul, map_one, ← hu'eq] using this
  have d2 : u' * m.ψ mX * u' = (m.ψ mX)⁻¹ := by
    have := congrArg m.ψ c2
    simpa only [map_mul, map_inv, ← hu'eq] using this
  have d3 : (u' * m.ψ mX) * (u' * m.ψ mX) = 1 := by
    have := congrArg m.ψ c3
    simpa only [map_mul, map_one, ← hu'eq] using this
  have d4 : m.ψ mA * u' = u' * m.ψ mA := by
    have := congrArg m.ψ c4
    simpa only [map_mul, ← hu'eq] using this
  have d6 : (m.ψ mA * u') * (m.ψ mA * u') = 1 := by
    have := congrArg m.ψ c6
    simpa only [map_mul, map_one, ← hu'eq] using this
  have d7 : (z * (m.ψ mA * u')) * (z * (m.ψ mA * u')) = 1 := by
    have := congrArg m.ψ c7
    simpa only [map_mul, map_one, m.ψ_hz, ← hu'eq] using this
  have d8 : (z * (u' * m.ψ mX)) * (z * (u' * m.ψ mX)) = 1 := by
    have := congrArg m.ψ c8
    simpa only [map_mul, map_one, m.ψ_hz, ← hu'eq] using this
  have d9 : (z * u') * (z * u') = 1 := by
    have := congrArg m.ψ c9
    simpa only [map_mul, map_one, m.ψ_hz, ← hu'eq] using this
  have d10 : ((m.ψ mA * u') * (u' * m.ψ mX)) ^ 3 = 1 := by
    have := congrArg m.ψ c10
    simpa only [map_mul, map_one, map_pow, ← hu'eq] using this
  have d11 : ((m.ψ mA * u') * u') * ((m.ψ mA * u') * u') = 1 := by
    have := congrArg m.ψ c11
    simpa only [map_mul, map_one, ← hu'eq] using this
  have d12 : ((u' * m.ψ mX) * u') ^ 3 = 1 := by
    have := congrArg m.ψ c12
    simpa only [map_mul, map_one, map_pow, ← hu'eq] using this
  have d13 : m.ψ mA * u' ≠ z := by
    intro h
    apply c13
    apply m.ψ_injective
    rw [map_mul, ← hu'eq, h, m.ψ_hz]
  have hzx : z * m.ψ mX = m.ψ mX * z := (m.ψ_comm_z mX).symm
  have hzu' : z * u' = u' * z := by
    have : u' ∈ ascH z := by rw [hu'eq]; exact m.ψ_mem uM
    exact (Subgroup.mem_centralizer_singleton_iff.1 this).symm
  have hza : z * m.ψ mA = m.ψ mA * z := (m.ψ_comm_z mA).symm
  have hx1x' : x1 * m.ψ mX = m.ψ mX * x1 := hx1x
  obtain ⟨g, hgz, hsQ, huQs⟩ := m.exists_g_u hyp
  have hs1 : g * z * g⁻¹ ≠ 1 := asc_conj_ne_one hyp g
  have hsF : g * z * g⁻¹ ∈ m.fSub := m.conj_mem_fSub hyp hgz hsQ
  have hhyp_s : Asc03Hyp G (g * z * g⁻¹) := asc03Hyp_conj hyp g
  have hwQs : z ∈ ascQ (g * z * g⁻¹) :=
    (mem_ascQ_conj z g z).2 (config_of_conj hyp hgz hsQ).1
  have hu'Qs : u' ∈ ascQ (g * z * g⁻¹) := by
    rcases hu'cases with h | h
    · rw [h]; exact huQs
    · rw [h, map_mul, m.ψ_hz]; exact mul_mem huQs hwQs
  have hxH : m.ψ mX ∈ ascH z := m.ψ_mem mX
  have claimH : nrmG (m.ψ mX) (g * z * g⁻¹) ≠ 1 := fun hN =>
    mirror_claim hyp m hhyp_s (m.conj g) hsF hs1 hgz hwQs hxH m.x_cube m.x_ne d1 hu'Qs d2 hN
  have hsu' : u' * (g * z * g⁻¹) = (g * z * g⁻¹) * u' :=
    Subgroup.mem_centralizer_singleton_iff.1 (ascQ_le_ascH _ hu'Qs)
  have hsz : z * (g * z * g⁻¹) = (g * z * g⁻¹) * z := m.z_comm_conj hyp hgz hsQ
  have hsH : g * z * g⁻¹ ∈ ascH z := ascQ_le_ascH z hsQ
  have hsFt : m.tb (g * z * g⁻¹) ∈ FTabs := (m.mem_fSub_iff.1 hsF).2
  have hNH : nrmG (m.ψ mX) (g * z * g⁻¹) ∈ ascH z := nrmG_mem hxH hsH
  have hnrmtb := m.tb_nrmG hxH hsH
  rw [m.tb_ψ_mX] at hnrmtb
  have hNz : nrmG (m.ψ mX) (g * z * g⁻¹) = z := by
    rcases nrm_mem xTab xTab_mem xTab_cube xTab_ne _ hsFt with h | h
    · exact absurd ((m.eq_one_iff hNH).2 (by rw [hnrmtb]; exact h)) claimH
    · exact (m.eq_z_iff hNH).2 (by rw [hnrmtb]; exact h)
  have hzs_tb : m.tb (z * (g * z * g⁻¹)) = tmul zTab (m.tb (g * z * g⁻¹)) := by
    rw [m.tb_mul (z_mem_ascH z) hsH, m.tb_z]
  have hzsH : z * (g * z * g⁻¹) ∈ ascH z := mul_mem (z_mem_ascH z) hsH
  have hzsF : m.tb (z * (g * z * g⁻¹)) ∈ FTabs := by
    rw [hzs_tb]; exact FTabs_mul _ zTab_mem_F _ hsFt
  have hnrm_zs : nrm xTab (m.tb (z * (g * z * g⁻¹))) = tid := by
    rw [hzs_tb]
    apply nrm_mul_z _ hsFt
    rw [hNz, m.tb_z] at hnrmtb
    exact hnrmtb.symm
  have hzs1 : z * (g * z * g⁻¹) ≠ 1 := by
    intro h
    apply hgz
    rw [eq_inv_of_mul_eq_one_right h, hzi]
  have hsu : (g * z * g⁻¹) * m.ψ mU = m.ψ mU * (g * z * g⁻¹) := by
    rcases hu'cases with h | h
    · rw [h] at hsu'; exact hsu'.symm
    · rw [h, map_mul, m.ψ_hz] at hsu'
      have h2 : (m.ψ mU * (g * z * g⁻¹)) * z = ((g * z * g⁻¹) * m.ψ mU) * z := by
        calc (m.ψ mU * (g * z * g⁻¹)) * z = m.ψ mU * (z * (g * z * g⁻¹)) := by rw [hsz]; group
          _ = (m.ψ mU * z) * (g * z * g⁻¹) := by group
          _ = (g * z * g⁻¹) * (m.ψ mU * z) := hsu'
          _ = ((g * z * g⁻¹) * m.ψ mU) * z := by group
      exact (mul_right_cancel h2).symm
  have hzsu : (z * (g * z * g⁻¹)) * m.ψ mU = m.ψ mU * (z * (g * z * g⁻¹)) := by
    have hzu0 : z * m.ψ mU = m.ψ mU * z := (m.ψ_comm_z mU).symm
    calc (z * (g * z * g⁻¹)) * m.ψ mU = z * ((g * z * g⁻¹) * m.ψ mU) := by group
      _ = z * (m.ψ mU * (g * z * g⁻¹)) := by rw [hsu]
      _ = (z * m.ψ mU) * (g * z * g⁻¹) := by group
      _ = (m.ψ mU * z) * (g * z * g⁻¹) := by rw [hzu0]
      _ = m.ψ mU * (z * (g * z * g⁻¹)) := by group
  have hzsa : z * (g * z * g⁻¹) = m.ψ mA := by
    have h1 : m.tb (z * (g * z * g⁻¹)) = aFTab := by
      apply aFTab_unique _ hzsF (fun h => hzs1 ((m.eq_one_iff hzsH).2 h)) hnrm_zs
      rw [← m.tb_ψ_mU]
      exact (m.comm_iff hzsH (m.ψ_mem mU)).1 hzsu
    apply m.tb_inj hzsH (m.ψ_mem mA)
    rw [h1, m.tb_ψ mA]
    exact (tabOf_aFPerm).symm
  have hs_eq : g * z * g⁻¹ = z * m.ψ mA := by
    calc g * z * g⁻¹ = z * (z * (g * z * g⁻¹)) := by rw [← mul_assoc, hz2, one_mul]
      _ = z * m.ψ mA := by rw [hzsa]
  have hu'H : u' ∈ ascH z := by rw [hu'eq]; exact m.ψ_mem uM
  have hu'Q : u' ∉ ascQ z := by
    intro h
    have h2 := ((m.mem_ascQ_iff_tb hyp).1 h).2
    rcases hu'cases with e | e
    · rw [e, m.tb_ψ_mU] at h2
      exact uTab_not_q h2
    · rw [e, map_mul, m.ψ_hz, m.tb_mul (m.ψ_mem mU) (z_mem_ascH z), m.tb_ψ_mU, m.tb_z] at h2
      exact uzTab_not_q h2
  obtain ⟨c, hc⟩ := isConj_iff.1 (m.outInv_isConj hyp hu'H hu'Q d1)
  have hyp_u : Asc03Hyp G u' := hc ▸ asc03Hyp_conj hyp c
  obtain ⟨mu⟩ : Nonempty (AscModel u') := ⟨hc ▸ m.conj c⟩
  have hg'eq : (c * g⁻¹) * (g * z * g⁻¹) * (c * g⁻¹)⁻¹ = u' := by rw [← hc]; group
  have hsne : u' ≠ g * z * g⁻¹ := fun h => hu'Q (h ▸ hsQ)
  have hsQu' : g * z * g⁻¹ ∈ ascQ u' := by
    have hne : (c * g⁻¹) * (g * z * g⁻¹) * (c * g⁻¹)⁻¹ ≠ g * z * g⁻¹ := by rw [hg'eq]; exact hsne
    have hQ' : (c * g⁻¹) * (g * z * g⁻¹) * (c * g⁻¹)⁻¹ ∈ ascQ (g * z * g⁻¹) := by
      rw [hg'eq]; exact hu'Qs
    have h1 := (config_of_conj hhyp_s hne hQ').1
    have h2 := (mem_ascQ_conj (g * z * g⁻¹) (c * g⁻¹) (g * z * g⁻¹)).2 h1
    rwa [hg'eq] at h2
  have hsFu : g * z * g⁻¹ ∈ mu.fSub :=
    mu.zconj_mem_fSub hyp_u hsQu' (isConj_iff.2 ⟨g * c⁻¹, by rw [← hc]; group⟩)
  have hx1H : x1 ∈ ascH u' := Subgroup.mem_centralizer_singleton_iff.2 hx1u
  have claimU : nrmG x1 (g * z * g⁻¹) ≠ 1 := fun hN =>
    mirror_claim hyp_u mu hhyp_s (m.conj g) hsFu hs1 (Ne.symm hsne) hu'Qs hx1H hx1_3' hx1_1 hz2
      hwQs hx1z' hN
  have hsH' : g * z * g⁻¹ ∈ ascH u' := ascQ_le_ascH u' hsQu'
  have hNH' : nrmG x1 (g * z * g⁻¹) ∈ ascH u' := nrmG_mem hx1H hsH'
  have hx1tb3 : tmul (mu.tb x1) (tmul (mu.tb x1) (mu.tb x1)) = tid := by
    have h : x1 * (x1 * x1) = 1 := by rw [← mul_assoc]; exact hx1_3'
    have := congrArg mu.tb h
    rwa [mu.tb_mul hx1H (mul_mem hx1H hx1H), mu.tb_mul hx1H hx1H, mu.tb_one] at this
  have hx1tid : mu.tb x1 ≠ tid := fun h => hx1_1 ((mu.eq_one_iff hx1H).2 h)
  have hsFt' : mu.tb (g * z * g⁻¹) ∈ FTabs := (mu.mem_fSub_iff.1 hsFu).2
  have hnrmtb' := mu.tb_nrmG hx1H hsH'
  have hN'u : nrmG x1 (g * z * g⁻¹) = u' := by
    rcases nrm_mem (mu.tb x1) (mu.tb_mem hx1H) hx1tb3 hx1tid _ hsFt' with h | h
    · exact absurd ((mu.eq_one_iff hNH').2 (by rw [hnrmtb']; exact h)) claimU
    · exact (mu.eq_z_iff hNH').2 (by rw [hnrmtb']; exact h)
  have hxi : x1⁻¹ = x1 * x1 := inv_eq_of_mul_eq_one_right (by rw [← mul_assoc]; exact hx1_3')
  have hf2 : x1 * ((g * z * g⁻¹) * (x1 * x1)) ∈ mu.fSub := by
    have := mu.fSub_normal hx1H hsFu
    rwa [hxi, mul_assoc] at this
  have hx4 : x1 * x1 * (x1 * x1) = x1 := by
    calc x1 * x1 * (x1 * x1) = (x1 * x1 * x1) * x1 := by group
      _ = x1 := by rw [hx1_3', one_mul]
  have hf3 : (x1 * x1) * ((g * z * g⁻¹) * x1) ∈ mu.fSub := by
    have := mu.fSub_normal (mul_mem hx1H hx1H) hsFu
    have hinv2 : (x1 * x1)⁻¹ = x1 := by
      rw [mul_inv_rev, hxi]
      exact hx4
    have e : (x1 * x1) * (g * z * g⁻¹) * (x1 * x1)⁻¹ = (x1 * x1) * ((g * z * g⁻¹) * x1) := by
      rw [hinv2]
      group
    rwa [e] at this
  have hcube : (x1 * (g * z * g⁻¹)) ^ 3 = u' := by
    rw [cube_eq_nrmG hx1_3' (mu.fSub_elab hsFu hf2).2 (mu.fSub_elab hsFu hf3).2, hN'u]
  have hR23 : ((x1 * z) * (m.ψ mA * u')) ^ 3 = 1 := by
    have e : (x1 * z) * (m.ψ mA * u') = (x1 * (g * z * g⁻¹)) * u' := by
      rw [hs_eq]; group
    rw [e]
    have hcomm : Commute (x1 * (g * z * g⁻¹)) u' := by
      show (x1 * (g * z * g⁻¹)) * u' = u' * (x1 * (g * z * g⁻¹))
      calc (x1 * (g * z * g⁻¹)) * u' = x1 * ((g * z * g⁻¹) * u') := by group
        _ = x1 * (u' * (g * z * g⁻¹)) := by rw [hsu']
        _ = (x1 * u') * (g * z * g⁻¹) := by group
        _ = (u' * x1) * (g * z * g⁻¹) := by rw [hx1u]
        _ = u' * (x1 * (g * z * g⁻¹)) := by group
    rw [hcomm.mul_pow, hcube]
    calc u' * u' ^ 3 = (u' * u') * u' * u' := by rw [pow_succ, pow_two]; group
      _ = 1 := by rw [d1, one_mul, d1]
  have hz2c : (x1 * z) * (x1 * z) = 1 := by
    calc (x1 * z) * (x1 * z) = x1 * (z * x1 * z) := by group
      _ = 1 := by rw [hx1z', mul_inv_cancel]
  have R12 : (z * (x1 * z)) ^ 3 = 1 := by
    have : z * (x1 * z) = x1⁻¹ := by rw [← mul_assoc]; exact hx1z'
    rw [this, inv_pow, hx1_3, inv_one]
  have R13 : (z * (m.ψ mA * u')) ^ 2 = 1 := by rw [pow_two]; exact d7
  have R14 : (z * (u' * m.ψ mX)) ^ 2 = 1 := by rw [pow_two]; exact d8
  have R15 : (z * u') ^ 2 = 1 := by rw [pow_two]; exact d9
  have R35 : ((m.ψ mA * u') * u') ^ 2 = 1 := by rw [pow_two]; exact d11
  have R24 : ((x1 * z) * (u' * m.ψ mX)) ^ 2 = 1 := by
    have hwx1 : (u' * m.ψ mX) * x1 = x1 * (u' * m.ψ mX) := by
      calc (u' * m.ψ mX) * x1 = u' * (m.ψ mX * x1) := by group
        _ = u' * (x1 * m.ψ mX) := by rw [hx1x]
        _ = (u' * x1) * m.ψ mX := by group
        _ = (x1 * u') * m.ψ mX := by rw [hx1u]
        _ = x1 * (u' * m.ψ mX) := by group
    have hwz : (u' * m.ψ mX) * z = z * (u' * m.ψ mX) := by
      calc (u' * m.ψ mX) * z = u' * (m.ψ mX * z) := by group
        _ = u' * (z * m.ψ mX) := by rw [hzx]
        _ = (u' * z) * m.ψ mX := by group
        _ = (z * u') * m.ψ mX := by rw [hzu']
        _ = z * (u' * m.ψ mX) := by group
    rw [pow_two]
    calc ((x1 * z) * (u' * m.ψ mX)) * ((x1 * z) * (u' * m.ψ mX))
        = x1 * z * ((u' * m.ψ mX) * x1) * z * (u' * m.ψ mX) := by group
      _ = x1 * z * (x1 * (u' * m.ψ mX)) * z * (u' * m.ψ mX) := by rw [hwx1]
      _ = x1 * z * x1 * ((u' * m.ψ mX) * z) * (u' * m.ψ mX) := by group
      _ = x1 * z * x1 * (z * (u' * m.ψ mX)) * (u' * m.ψ mX) := by rw [hwz]
      _ = x1 * (z * x1 * z) * ((u' * m.ψ mX) * (u' * m.ψ mX)) := by group
      _ = 1 := by rw [hx1z', d3, mul_inv_cancel, mul_one]
  have R25 : ((x1 * z) * u') ^ 2 = 1 := by
    rw [pow_two]
    calc ((x1 * z) * u') * ((x1 * z) * u') = x1 * z * (u' * x1) * z * u' := by group
      _ = x1 * z * (x1 * u') * z * u' := by rw [hx1u]
      _ = x1 * z * x1 * (u' * z) * u' := by group
      _ = x1 * z * x1 * (z * u') * u' := by rw [hzu']
      _ = x1 * (z * x1 * z) * (u' * u') := by group
      _ = 1 := by rw [hx1z', d1, mul_inv_cancel, mul_one]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · exact hz2
    · exact hz2c
    · exact d6
    · exact d3
    · exact d1
  · intro i j hij
    fin_cases i <;> fin_cases j <;> first | (exfalso; revert hij; decide) | skip
    · simpa [coxVec, coxExp] using R12
    · simpa [coxVec, coxExp] using R13
    · simpa [coxVec, coxExp] using R14
    · simpa [coxVec, coxExp] using R15
    · simpa [coxVec, coxExp] using hR23
    · simpa [coxVec, coxExp] using R24
    · simpa [coxVec, coxExp] using R25
    · simpa [coxVec, coxExp] using d10
    · simpa [coxVec, coxExp] using R35
    · simpa [coxVec, coxExp] using d12
  · show z * (m.ψ mA * u') ≠ 1
    intro h
    apply d13
    have := eq_inv_of_mul_eq_one_right h
    rwa [hzi] at this
  · refine ⟨g, hs_eq, ?_⟩
    rw [← hs_eq]
    exact hu'Qs

end AscModel

end CFSG.Quasithin
